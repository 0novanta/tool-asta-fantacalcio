#!/usr/bin/env python3
"""Assistente Asta Fantacalcio 2026-27 - applicazione desktop offline."""

from __future__ import annotations

import argparse
import csv
from html import unescape
from io import BytesIO
from itertools import combinations
import json
from math import ceil, floor, log10
import re
import shutil
import sqlite3
import threading
import time
import unicodedata
import xml.etree.ElementTree as ET
import zipfile
from decimal import Decimal, ROUND_DOWN
from datetime import datetime
from pathlib import Path
from tkinter import END, StringVar, Tk, Toplevel, filedialog, messagebox
from tkinter import ttk
import tkinter as tk
from urllib.error import HTTPError, URLError
from urllib.parse import quote, urlencode
from urllib.request import Request, urlopen
from PIL import Image, ImageDraw, ImageFont, ImageTk


ROOT = Path(__file__).resolve().parent
LEGACY_DATA_DIR = ROOT / "dati_locali"
PUBLIC_DATA_DIR = ROOT / "dati_condivisibili"
PRIVATE_DATA_DIR = ROOT / "dati_riservati"
DB_PATH = PUBLIC_DATA_DIR / "dati_pubblici.sqlite3"
FANTA_DB_PATH = PRIVATE_DATA_DIR / "dati_fantacalcio.sqlite3"
ASTA_DB_PATH = PRIVATE_DATA_DIR / "asta_personale.sqlite3"
LEGACY_DB_PATH = LEGACY_DATA_DIR / "asta_fantacalcio.sqlite3"
FOTO_DIR = PUBLIC_DATA_DIR / "immagini" / "foto"
STEMMI_DIR = PUBLIC_DATA_DIR / "immagini" / "stemmi"
BANDIERE_DIR = PUBLIC_DATA_DIR / "immagini" / "bandiere"
BACKUP_ASTA_DIR = PRIVATE_DATA_DIR / "backup_asta"
API_KEY_PATH = ROOT / "api_football_key.txt"
API_BASE = "https://v3.football.api-sports.io"
WIKIDATA_API = "https://www.wikidata.org/w/api.php"
WIKIMEDIA_FILE_PATH = "https://commons.wikimedia.org/wiki/Special:FilePath/"
COMMONS_API = "https://commons.wikimedia.org/w/api.php"
FLAGS_NET = "http://www.flags.net/"
XLSX_NS = "{http://schemas.openxmlformats.org/spreadsheetml/2006/main}"

# I dati Classic e le decisioni d'asta non vengono mai scritti nel catalogo
# condivisibile. Il catalogo contiene soltanto le fonti FBref/API e le immagini.
TABELLE_FANTACALCIO = {
    "giocatori", "statistiche_fanta", "quotazioni_fanta", "collegamenti_fbref",
    "problemi_importazione", "specialisti_piazzati", "indicazioni_formazione",
}
TABELLE_ASTA = {
    "tag_asta", "giocatori_acquistati", "impostazioni", "giocatori_venduti",
    "preferenze_giocatori", "fantallenatori", "acquisti_lega", "cronologia_asta",
}


def schema_tabella(nome: str) -> str | None:
    if nome in TABELLE_FANTACALCIO:
        return "fantacalcio"
    if nome in TABELLE_ASTA:
        return "asta"
    return None


def assicura_cartelle_dati() -> None:
    for cartella in (PUBLIC_DATA_DIR, PRIVATE_DATA_DIR, FOTO_DIR, STEMMI_DIR, BANDIERE_DIR, BACKUP_ASTA_DIR):
        cartella.mkdir(parents=True, exist_ok=True)




def percorso_fasce_locali() -> Path:
    percorso = PRIVATE_DATA_DIR / "fasce_asta_fantacalcio_2026_2027.docx"
    sorgente_legacy = ROOT / percorso.name
    if not percorso.exists() and sorgente_legacy.exists():
        assicura_cartelle_dati()
        shutil.copy2(sorgente_legacy, percorso)
    return percorso

def copia_tabella(origine: sqlite3.Connection, destinazione: sqlite3.Connection, tabella: str) -> None:
    definizione = origine.execute(
        "SELECT sql FROM sqlite_master WHERE type='table' AND name=?", (tabella,)
    ).fetchone()[0]
    destinazione.execute(definizione)
    colonne = [riga[1] for riga in origine.execute(f'PRAGMA table_info("{tabella}")')]
    if colonne:
        campi = ", ".join(f'"{colonna}"' for colonna in colonne)
        segnaposto = ", ".join("?" for _ in colonne)
        righe = origine.execute(f'SELECT {campi} FROM "{tabella}"')
        destinazione.executemany(f'INSERT INTO "{tabella}" ({campi}) VALUES ({segnaposto})', righe)
    for (definizione_indice,) in origine.execute(
        "SELECT sql FROM sqlite_master WHERE type='index' AND tbl_name=? AND sql IS NOT NULL", (tabella,)
    ):
        destinazione.execute(definizione_indice)


def migra_database_legacy() -> None:
    """Divide una sola volta il precedente database misto, senza cancellarlo."""
    if DB_PATH.exists() or not LEGACY_DB_PATH.exists():
        return
    assicura_cartelle_dati()
    origine = sqlite3.connect(LEGACY_DB_PATH)
    destinazioni = {
        None: sqlite3.connect(DB_PATH),
        "fantacalcio": sqlite3.connect(FANTA_DB_PATH),
        "asta": sqlite3.connect(ASTA_DB_PATH),
    }
    try:
        tabelle = [riga[0] for riga in origine.execute(
            "SELECT name FROM sqlite_master WHERE type='table' AND name NOT LIKE 'sqlite_%' ORDER BY name"
        )]
        for tabella in tabelle:
            copia_tabella(origine, destinazioni[schema_tabella(tabella)], tabella)
        for destinazione in destinazioni.values():
            destinazione.commit()
        for nome, cartella_destinazione in (("foto", FOTO_DIR), ("stemmi", STEMMI_DIR), ("bandiere", BANDIERE_DIR)):
            sorgente = LEGACY_DATA_DIR / nome
            if sorgente.exists():
                shutil.copytree(sorgente, cartella_destinazione, dirs_exist_ok=True)
        fanta = destinazioni["fantacalcio"]
        if fanta.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='giocatori'").fetchone():
            fanta.execute(
                "UPDATE giocatori SET foto_locale=REPLACE(foto_locale, ?, ?) WHERE foto_locale IS NOT NULL",
                (str(LEGACY_DATA_DIR / "foto"), str(FOTO_DIR)),
            )
            fanta.commit()
    finally:
        origine.close()
        for destinazione in destinazioni.values():
            destinazione.close()


class ConnessioneSeparata(sqlite3.Connection):
    """Catalogo pubblico con i due database locali allegati alla stessa sessione."""
    def __init__(self, *argomenti, **parole_chiave):
        super().__init__(*argomenti, **parole_chiave)
        assicura_cartelle_dati()
        super().execute("ATTACH DATABASE ? AS fantacalcio", (str(FANTA_DB_PATH),))
        super().execute("ATTACH DATABASE ? AS asta", (str(ASTA_DB_PATH),))
        super().execute("PRAGMA foreign_keys = OFF")

    @staticmethod
    def riscrivi(sql: str) -> str:
        if sql.lstrip().upper().startswith("PRAGMA"):
            return sql
        risultato = sql
        for tabella in sorted(TABELLE_FANTACALCIO | TABELLE_ASTA, key=len, reverse=True):
            schema = schema_tabella(tabella)
            risultato = re.sub(rf"(?<![.\w]){re.escape(tabella)}(?!\w)", f"{schema}.{tabella}", risultato)
        return re.sub(
            r"(CREATE\s+(?:UNIQUE\s+)?INDEX\s+(?:IF\s+NOT\s+EXISTS\s+)?)([\w]+)(\s+ON\s+)(fantacalcio|asta)\.([\w]+)",
            r"\1\4.\2\3\5",
            risultato,
            flags=re.IGNORECASE,
        )

    def execute(self, sql, parametri=()):
        return super().execute(self.riscrivi(sql), parametri)

    def executemany(self, sql, parametri):
        return super().executemany(self.riscrivi(sql), parametri)


def assicura_tabelle_riservate(connessione: sqlite3.Connection) -> None:
    """Crea gli schemi locali vuoti dalle definizioni contenute nel catalogo."""
    for tabella in sorted(TABELLE_FANTACALCIO | TABELLE_ASTA):
        schema = schema_tabella(tabella)
        esiste = sqlite3.Connection.execute(
            connessione,
            f"SELECT 1 FROM {schema}.sqlite_master WHERE type='table' AND name=?",
            (tabella,),
        ).fetchone()
        if esiste:
            continue
        definizione = sqlite3.Connection.execute(
            connessione,
            "SELECT sql FROM main.sqlite_master WHERE type='table' AND name=?",
            (tabella,),
        ).fetchone()
        if not definizione:
            continue
        sql = re.sub(
            rf"^CREATE TABLE(?: IF NOT EXISTS)? ({re.escape(tabella)})",
            rf"CREATE TABLE {schema}.\1",
            definizione[0],
            flags=re.IGNORECASE,
        )
        sqlite3.Connection.execute(connessione, sql)
        colonne = [riga[1] for riga in sqlite3.Connection.execute(connessione, f"PRAGMA main.table_info({tabella})")]
        if colonne and sqlite3.Connection.execute(connessione, f"SELECT COUNT(*) FROM main.{tabella}").fetchone()[0] and not sqlite3.Connection.execute(connessione, f"SELECT COUNT(*) FROM {schema}.{tabella}").fetchone()[0]:
            campi = ", ".join(f"\"{colonna}\"" for colonna in colonne)
            sqlite3.Connection.execute(connessione, f"INSERT INTO {schema}.{tabella} ({campi}) SELECT {campi} FROM main.{tabella}")


def normalizza_percorsi_foto(connessione: sqlite3.Connection) -> None:
    """Rende portabili le foto dopo uno spostamento della cartella del progetto."""
    esiste = sqlite3.Connection.execute(
        connessione,
        "SELECT 1 FROM fantacalcio.sqlite_master WHERE type='table' AND name='giocatori'",
    ).fetchone()
    if not esiste:
        return
    aggiornamenti = []
    for giocatore_id, percorso in connessione.execute(
        "SELECT id, foto_locale FROM giocatori"
    ):
        destinazione = FOTO_DIR / f"{giocatore_id}.png"
        if destinazione.exists() and str(destinazione) != (percorso or ""):
            aggiornamenti.append((str(destinazione), giocatore_id))
    if aggiornamenti:
        connessione.executemany(
            "UPDATE giocatori SET foto_locale=? WHERE id=?", aggiornamenti
        )
        connessione.commit()


def apri_connessione() -> sqlite3.Connection:
    migra_database_legacy()
    assicura_cartelle_dati()
    connessione = sqlite3.connect(DB_PATH, factory=ConnessioneSeparata)
    normalizza_percorsi_foto(connessione)
    return connessione
WORD_NS = "{http://schemas.openxmlformats.org/wordprocessingml/2006/main}"
ROSA = {"P": 3, "D": 8, "C": 8, "A": 6}
TEAM_CODES = {
    "ATA": "ATALANTA", "BOL": "BOLOGNA", "CAG": "CAGLIARI", "COM": "COMO",
    "FIO": "FIORENTINA", "FRO": "FROSINONE", "GEN": "GENOA", "INT": "INTER",
    "JUV": "JUVENTUS", "LAZ": "LAZIO", "LEC": "LECCE", "MIL": "MILAN",
    "MON": "MONZA", "NAP": "NAPOLI", "PAR": "PARMA", "ROM": "ROMA",
    "SAS": "SASSUOLO", "TOR": "TORINO", "UDI": "UDINESE", "VEN": "VENEZIA",
}
TIRATORI_FCP_2026_27 = {
    "Atalanta": {"rigori": ["Scamacca", "Krstovic", "Samardzic", "Ederson"], "punizioni": ["Samardzic", "Gaetano", "De Ketelaere", "Raspadori"], "angoli": ["Samardzic", "Gaetano", "Bernasconi", "Bellanova"]},
    "Bologna": {"rigori": ["Orsolini", "Dovbyk", "Bernardeschi"], "punizioni": ["Orsolini", "Bernardeschi", "Ferguson"], "angoli": ["Orsolini", "Bernardeschi", "Miranda"]},
    "Cagliari": {"rigori": ["Fazzini", "Mina", "Borrelli"], "punizioni": ["Maldini", "Fazzini", "Winks", "Obert"], "angoli": ["Fazzini", "Obert", "Romano", "Maldini", "Winks"]},
    "Como": {"rigori": ["Da Cunha", "Douvikas", "Nico Paz"], "punizioni": ["Nico Paz", "Baturina", "Da Cunha"], "angoli": ["Baturina", "Nico Paz", "Da Cunha"]},
    "Fiorentina": {"rigori": ["Gudmundsson", "Kean", "Mandragora", "Piccoli"], "punizioni": ["Gudmundsson", "Mastantuono", "Mandragora", "Fagioli"], "angoli": ["Gudmundsson", "Mastantuono", "Mandragora", "Fagioli"]},
    "Frosinone": {"rigori": ["Calò", "Raimondo"], "punizioni": ["Calò", "Ghedjemis", "Kvernadze"], "angoli": ["Calò", "Ghedjemis", "Kvernadze"]},
    "Genoa": {"rigori": ["Colombo", "Messias", "Vitinha"], "punizioni": ["Baldanzi", "Messias", "Aarón Martín", "Frendrup"], "angoli": ["Aarón Martín", "Baldanzi", "Messias", "Frendrup"]},
    "Inter": {"rigori": ["Calhanoglu", "Lautaro Martinez", "Zielinski"], "punizioni": ["Calhanoglu", "Dimarco", "Zielinski"], "angoli": ["Calhanoglu", "Dimarco", "Zielinski", "Barella"]},
    "Juventus": {"rigori": ["Yildiz", "Locatelli", "Kolo Muani", "David"], "punizioni": ["Yildiz", "Locatelli", "Koopmeiners"], "angoli": ["Yildiz", "Cambiaso", "Locatelli", "Koopmeiners"]},
    "Lazio": {"rigori": ["Zaccagni", "Kenneth Taylor", "Cataldi"], "punizioni": ["Zaccagni", "Cataldi", "Taylor", "Rovella"], "angoli": ["Zaccagni", "Taylor", "Rovella"]},
    "Lecce": {"rigori": ["Geubbels", "Stulic", "Pierotti"], "punizioni": ["Gallo", "Pierotti", "Berisha"], "angoli": ["Gallo", "Pierotti", "Berisha"]},
    "Milan": {"rigori": ["Nkunku", "Gonçalo Ramos", "Pulisic"], "punizioni": ["Modric", "Pulisic", "Nkunku", "Ricci"], "angoli": ["Modric", "Pulisic", "Bartesaghi", "Jashari"]},
    "Monza": {"rigori": ["Pessina", "Cutrone", "Petagna"], "punizioni": ["Colpani", "Pessina", "Ciurria"], "angoli": ["Pessina", "Colpani", "Ciurria"]},
    "Napoli": {"rigori": ["De Bruyne", "Højlund"], "punizioni": ["De Bruyne", "Politano", "Neres", "Lobotka"], "angoli": ["De Bruyne", "Politano", "Neres"]},
    "Parma": {"rigori": ["Pellegrino", "El Bilal Touré"], "punizioni": ["Bernabé", "Nicolussi Caviglia", "Valeri"], "angoli": ["Bernabé", "Nicolussi Caviglia", "Valeri"]},
    "Roma": {"rigori": ["Malen", "Dybala", "Pellegrini", "Soulé"], "punizioni": ["Dybala", "Soulé", "Pellegrini"], "angoli": ["Dybala", "Soulé", "Pellegrini", "Wesley"]},
    "Sassuolo": {"rigori": ["Berardi", "Pinamonti", "Laurienté"], "punizioni": ["Berardi", "Laurienté", "Volpato"], "angoli": ["Berardi", "Laurienté", "Volpato"]},
    "Torino": {"rigori": ["Vlasic", "Kulenovic", "Zapata"], "punizioni": ["Vlasic", "Oristanio", "Ilic"], "angoli": ["Vlasic", "Oristanio", "Ilic"]},
    "Udinese": {"rigori": ["Davis", "Zaniolo", "Solet"], "punizioni": ["Zaniolo", "Vojvoda", "Ekkelenkamp", "Miller"], "angoli": ["Vojvoda", "Ekkelenkamp", "Miller", "Zaniolo"]},
    "Venezia": {"rigori": ["Rrahmani", "Akor Adams", "Yeboah", "Adorante"], "punizioni": ["Busio", "Kike Pérez", "Basic", "Helgason"], "angoli": ["Busio", "Kike Pérez", "Basic", "Helgason"]},
}
FONTE_TIRATORI = "FantacalcioPedia, Rigoristi e tiratori 2026-27 (aggiornato 11 agosto 2026)"
ALIASES_TIRATORI = {("Venezia", "Kike Pérez"): "Perez K.", ("Inter", "Lautaro Martinez"): "Martinez L."}
FONTE_INFOGRAFICA = "Infografica 2026-27"
FUORI_RUOLO_INFOGRAFICA = {("Frosinone", "Schmid"): "in attacco"}
NAZIONALITA_FBREF = {
    "al": ("Albanese", "Albania"), "am": ("Armena", "Armenia"), "ar": ("Argentina", "Argentina"),
    "at": ("Austriaca", "Austria"), "au": ("Australiana", "Australia"), "ba": ("Bosniaca", "Bosnia and Herzegovina"),
    "be": ("Belga", "Belgium"), "bg": ("Bulgara", "Bulgaria"), "br": ("Brasiliana", "Brazil"),
    "ca": ("Canadese", "Canada"), "ch": ("Svizzera", "Switzerland"), "ci": ("Ivoriana", "Côte d'Ivoire"),
    "cm": ("Camerunese", "Cameroon"), "co": ("Colombiana", "Colombia"), "cz": ("Ceca", "the Czech Republic"),
    "de": ("Tedesca", "Germany"), "dk": ("Danese", "Denmark"), "dz": ("Algerina", "Algeria"),
    "ec": ("Ecuadoriana", "Ecuador"), "eng": ("Inglese", "England"), "es": ("Spagnola", "Spain"),
    "fr": ("Francese", "France"), "ga": ("Gabonese", "Gabon"), "ge": ("Georgiana", "Georgia"),
    "gh": ("Ghanese", "Ghana"), "gm": ("Gambiana", "the Gambia"), "gn": ("Guineana", "Guinea"),
    "gq": ("Equatoguineana", "Equatorial Guinea"), "gr": ("Greca", "Greece"), "gw": ("Guineense-bissauiana", "Guinea-Bissau"),
    "hr": ("Croata", "Croatia"), "id": ("Indonesiana", "Indonesia"), "ie": ("Irlandese", "Ireland"),
    "il": ("Israeliana", "Israel"), "is": ("Islandese", "Iceland"), "it": ("Italiana", "Italy"),
    "lt": ("Lituana", "Lithuania"), "ma": ("Marocchina", "Morocco"), "me": ("Montenegrina", "Montenegro"),
    "mk": ("Macedone", "North Macedonia"), "ml": ("Maliana", "Mali"), "mr": ("Mauritana", "Mauritania"),
    "mx": ("Messicana", "Mexico"), "ne": ("Nigerina", "Niger"), "ng": ("Nigeriana", "Nigeria"),
    "nl": ("Olandese", "the Netherlands"), "no": ("Norvegese", "Norway"), "pl": ("Polacca", "Poland"),
    "pt": ("Portoghese", "Portugal"), "ro": ("Romena", "Romania"), "rs": ("Serba", "Serbia"),
    "sct": ("Scozzese", "Scotland"), "se": ("Svedese", "Sweden"), "sk": ("Slovacca", "Slovakia"),
    "sn": ("Senegalese", "Senegal"), "sr": ("Surinamese", "Suriname"), "tr": ("Turca", "Turkey"),
    "ua": ("Ucraina", "Ukraine"), "us": ("Statunitense", "the United States"), "uy": ("Uruguaiana", "Uruguay"),
    "xk": ("Kosovara", "Kosovo"), "zm": ("Zambiana", "Zambia"),
}
INFOGRAFICA_2026_27 = {
    "Atalanta": {"titolari": ["Carnesecchi", "Bellanova", "Kristensen T.", "Scalvini", "Bernasconi", "Samardzic", "Gaetano", "Ederson D.S.", "De Ketelaere", "Scamacca", "Raspadori"], "ballottaggi": [("Bellanova", "Zappacosta"), ("Bernasconi", "Ahanor"), ("Samardzic", "Pasalic")], "rigori": ["Scamacca", "Krstovic", "Ederson D.S."], "punizioni": ["Samardzic", "Gaetano", "De Ketelaere"]},
    "Bologna": {"titolari": ["Skorupski", "Zortea", "Vitik", "Heggem", "Miranda J.", "Bernardeschi", "Moro N.", "Ferguson", "Orsolini", "Dovbyk", "Rowe"], "ballottaggi": [("Moro N.", "El Azzouzi O."), ("Bernardeschi", "Amondarain"), ("Bernardeschi", "Odgaard")], "rigori": ["Orsolini", "Dovbyk", "Bernardeschi"], "punizioni": ["Orsolini", "Bernardeschi", "Rowe"]},
    "Cagliari": {"titolari": ["Caprile", "Zè Pedro", "Mina", "Rodriguez Ju.", "Obert", "Adopo", "Winks", "Romano", "Fazzini", "Kevin Carlos", "Maldini"], "ballottaggi": [("Rodriguez Ju.", "Kofler"), ("Zè Pedro", "Zappa"), ("Romano", "Prati")], "rigori": ["Kevin Carlos", "Fazzini", "Mina"], "punizioni": ["Winks", "Romano"]},
    "Como": {"titolari": ["Butez", "Couto", "Chalobah T.", "Ramon", "Kaiki", "Perrone", "Da Cunha", "Diao", "Paz N.", "Baturina", "Douvikas"], "ballottaggi": [("Chalobah T.", "Kempf"), ("Kaiki", "Valle"), ("Diao", "Rodriguez Je.")], "rigori": ["Da Cunha", "Douvikas", "Paz N."], "punizioni": ["Paz N.", "Baturina", "Da Cunha"]},
    "Fiorentina": {"titolari": ["De Gea", "Jimenez A.", "Dragusin", "Viery", "Valdepenas", "Ndour", "Fagioli", "Atta", "Mastantuono", "Kean", "Gudmundsson A."], "ballottaggi": [("Viery", "Ranieri L."), ("Jimenez A.", "Dodò"), ("Fagioli", "Oulai")], "rigori": ["Gudmundsson A.", "Kean", "Mandragora"], "punizioni": ["Gudmundsson A.", "Mastantuono", "Atta"]},
    "Frosinone": {"titolari": ["Palmisani", "Oyono A.", "Calvani", "Monterisi", "Bracaglia", "Koutsoupias", "Calò", "Grillitsch", "Ghedjemis", "Raimondo", "Schmid"], "ballottaggi": [("Palmisani", "Desplanches"), ("Calvani", "Akpoguma"), ("Bracaglia", "Terzic")], "rigori": ["Calò", "Schmid", "Ghedjemis"], "punizioni": ["Calò", "Schmid", "Ghedjemis"]},
    "Genoa": {"titolari": ["Bijlow", "Marcandalli", "Vasquez", "Ostigard", "Norton-Cuffy", "Sow", "Frendrup", "Ellertsson", "Baldanzi", "Vitinha O.", "Colombo"], "ballottaggi": [("Ellertsson", "Martin"), ("Sow", "Amorim"), ("Baldanzi", "Traorè Hj.")], "rigori": ["Colombo", "Vitinha O.", "Ostigard"], "punizioni": ["Baldanzi", "Martin", "Vitinha O."]},
    "Inter": {"titolari": ["Martinez Jo.", "Akanji", "Stones", "Bastoni", "Spence", "Barella", "Calhanoglu", "Zielinski", "Dimarco", "Thuram", "Martinez L."], "ballottaggi": [("Stones", "Bisseck"), ("Spence", "Diouf"), ("Zielinski", "Sucic P.")], "rigori": ["Calhanoglu", "Zielinski", "Martinez L."], "punizioni": ["Calhanoglu", "Dimarco", "Zielinski"]},
    "Juventus": {"titolari": ["Vicario", "Kalulu", "Bremer", "Lucumì", "Cambiaso", "McKennie", "Locatelli", "Conceicao", "Alajbegovic", "Yildiz", "Kolo Muani"], "ballottaggi": [("Locatelli", "Douglas Luiz"), ("McKennie", "Thuram K."), ("Alajbegovic", "Thuram K.")], "rigori": ["Kolo Muani", "Yildiz", "Locatelli"], "punizioni": ["Yildiz", "Locatelli", "Cambiaso"]},
    "Lazio": {"titolari": ["Mandas", "Marusic", "Doekhi", "Romagnoli", "Pedraza", "Frattesi", "Rovella", "Taylor K.", "Isaksen", "Dia", "Zaccagni"], "ballottaggi": [("Marusic", "Floriani Mussolini"), ("Pedraza", "Tavares N."), ("Isaksen", "Cancellieri")], "rigori": ["Zaccagni", "Taylor K.", "Cataldi"], "punizioni": ["Zaccagni", "Taylor K.", "Cataldi"]},
    "Lecce": {"titolari": ["Falcone", "Veiga D.", "Gaspar K.", "Tiago Gabriel", "Gallo", "Coulibaly L.", "Ngom", "Berisha M.", "Pierotti", "Geubbels", "N'Dri"], "ballottaggi": [("Gaspar K.", "Siebert"), ("Ngom", "Gorter"), ("Berisha M.", "Gandelman")], "rigori": ["Geubbels", "Stulic", "Berisha M."], "punizioni": ["Berisha M.", "Gallo", "Pierotti"]},
    "Milan": {"titolari": ["Maignan", "Gila", "Gabbia", "Pavlovic", "Saelemaekers", "Modric", "Rabiot", "Bartesaghi", "Pulisic", "Leao", "Ramos G."], "ballottaggi": [("Saelemaekers", "Chukwueze")], "rigori": ["Ramos G.", "Pulisic", "Leao"], "punizioni": ["Modric", "Pulisic", "Saelemaekers"]},
    "Monza": {"titolari": ["Thiam", "Birindelli", "Delli Carri", "Carboni A.", "Kouadio", "Akinsanmiro", "Colombo L.", "Mangas", "Colpani", "Mota", "Cutrone"], "ballottaggi": [("Carboni A.", "Lucchesi"), ("Mota", "Varela G.")], "rigori": ["Pessina", "Cutrone", "Mota"], "punizioni": ["Colpani", "Pessina", "Akinsanmiro"]},
    "Napoli": {"titolari": ["Meret", "Di Lorenzo", "Rrahmani", "Beukema", "Spinazzola", "De Bruyne", "Lobotka", "McTominay", "Politano", "Hojlund", "Santos A."], "ballottaggi": [("Meret", "Milinkovic-Savic V."), ("Beukema", "Buongiorno"), ("Spinazzola", "Olivera")], "rigori": ["De Bruyne", "Hojlund"], "punizioni": ["De Bruyne", "Politano", "Vergara"]},
    "Parma": {"titolari": ["Suzuki", "Delprato", "Circati", "Troilo", "Valeri", "Britschgi", "Keita M.", "Bernabè", "Almqvist", "Tourè E.", "Romero D."], "ballottaggi": [("Troilo", "Valenti"), ("Keita M.", "Nicolussi Caviglia"), ("Almqvist", "Diallo O.")], "rigori": ["Tourè E.", "Valeri", "Nicolussi Caviglia"], "punizioni": ["Bernabè", "Nicolussi Caviglia", "Valeri"]},
    "Roma": {"titolari": ["Svilar", "Mancini", "N'Dicka", "Hermoso", "Molina N.", "Cristante", "Konè M.", "Wesley", "Dybala", "Soulè", "Malen"], "ballottaggi": [("Hermoso", "Koulierakis"), ("Soulè", "Castro S.")], "rigori": ["Malen", "Dybala", "Castro S."], "punizioni": ["Dybala", "Soulè", "Malen"]},
    "Sassuolo": {"titolari": ["Muric", "Walukiewicz", "Idzes", "Candè", "Obrador", "Matic", "Thorstvedt", "Berardi", "Adzic", "Laurientè", "Pinamonti"], "ballottaggi": [("Obrador", "Doig"), ("Candè", "Missori"), ("Adzic", "Bakola")], "rigori": ["Berardi", "Pinamonti", "Laurientè"], "punizioni": ["Berardi", "Laurientè", "Adzic"]},
    "Torino": {"titolari": ["Mascardi", "Comuzzo", "Coco", "Comert", "Pedersen", "Gineitis", "Casadei", "Fitz-Jim", "Cacciamani", "Vlasic", "Simeone"], "ballottaggi": [("Comuzzo", "Ismajli"), ("Coco", "Ismajli"), ("Fitz-Jim", "Ilkhan")], "rigori": ["Vlasic", "Kulenovic", "Simeone"], "punizioni": ["Vlasic", "Oristanio", "Fitz-Jim"]},
    "Udinese": {"titolari": ["Okoye", "Bertola", "Kabasele", "Solet", "Vojvoda", "Karlstrom", "Piotrowski", "Kamara H.", "Zaniolo", "Ekkelenkamp", "Davis K."], "ballottaggi": [("Bertola", "Palma"), ("Vojvoda", "Zanoli"), ("Piotrowski", "Miller L.")], "rigori": ["Davis K.", "Solet", "Zaniolo"], "punizioni": ["Zaniolo", "Ekkelenkamp", "Unai Gomez"]},
    "Venezia": {"titolari": ["Stankovic F.", "Schingtienne", "Bella-Kotchap", "Halhal", "Hainaut", "Perez K.", "Busio", "Basic", "Haps", "Yeboah J.", "Adams A."], "ballottaggi": [("Halhal", "Moreno M."), ("Haps", "Correia T."), ("Perez K.", "Sohm")], "rigori": ["Adams A.", "Rrahmani Al.", "Busio"], "punizioni": ["Busio", "Perez K.", "Basic"]},
}
MODULI_FORMAZIONI = {
    "Atalanta": "4-3-3", "Bologna": "4-3-3", "Cagliari": "4-4-2", "Como": "4-2-3-1",
    "Fiorentina": "4-3-3", "Frosinone": "4-3-3", "Genoa": "3-4-2-1", "Inter": "3-5-2",
    "Juventus": "4-2-3-1", "Lazio": "4-3-3", "Lecce": "4-3-3", "Milan": "3-4-2-1",
    "Monza": "3-4-2-1", "Napoli": "4-3-3", "Parma": "4-4-2", "Roma": "3-4-2-1",
    "Sassuolo": "4-2-3-1", "Torino": "3-4-2-1", "Udinese": "3-4-2-1", "Venezia": "3-5-2",
}
# I nomi completi evitano ricerche ambigue per le sigle presenti nei file Classic.
NOMI_WIKIMEDIA = {
    "Hojlund": "Rasmus Højlund", "Martinez L.": "Lautaro Martínez", "N'Dri": "Konan N'Dri",
    "Neres": "David Neres", "Osmajic": "Milutin Osmajić", "Raimondo": "Antonio Raimondo",
    "Sulemana K.": "Kamaldeen Sulemana", "Yildiz": "Kenan Yıldız", "Berisha M.": "Medon Berisha",
    "Boloca": "Daniel Boloca", "Dominguez B.": "Benjamín Domínguez", "Elmas": "Elif Elmas",
    "Gelli F.": "Francesco Gelli", "Gudmundsson A.": "Albert Guðmundsson", "Jones C.": "Curtis Jones",
    "Kaba": "Naby Kaba", "Messias": "Junior Messias", "Mora": "Rodrigo Mora", "Moreira": "Diego Moreira",
    "Ordonez C.": "Christian Ordóñez", "Oulai": "Christ Inao Oulaï", "Perez K.": "Kike Pérez",
    "Rodriguez Je.": "Jesús Rodríguez", "Sorensen O.": "Oliver Sørensen", "Sucic P.": "Petar Sučić",
    "Sulemana I.": "Ibrahim Sulemana", "Tourè I.": "El Bilal Touré", "Badiashile": "Benoît Badiashile",
    "Candè": "Fali Candé", "De Silvestri": "Lorenzo De Silvestri", "Diawara S.": "Sankhoun Diawara",
    "Jimenez A.": "Álex Jiménez", "Leysen F.": "Fedde Leysen", "Marin R.": "Rafa Marín",
    "Matturro": "Alan Matturro", "Ndiaye": "Abdoulaye Ndiaye", "Omar Fayed": "Omar Fayed",
    "Ostigard": "Leo Østigård", "Oyono A.": "Anthony Oyono", "Oyono J.": "Jacques Oyono",
    "Pieragnolo": "Edoardo Pieragnolo", "Rodriguez Ju.": "Juan Rodríguez", "Smolcic I.": "Ivan Smolčić",
    "Sutalo J.": "Josip Šutalo", "Terracciano F.": "Filippo Terracciano", "Ziolkowski": "Jan Ziółkowski",
    "Bleve": "Marco Bleve", "Martinez Jo.": "Josep Martínez", "Montipò": "Lorenzo Montipò",
    "Pisseri": "Matteo Pisseri", "Satalino": "Giacomo Satalino", "Sommariva": "Daniele Sommariva",
    "Terracciano": "Pietro Terracciano", "Vicario": "Guglielmo Vicario", "Grabara": "Kamil Grabara", "Vigorito": "Mauro Vigorito",
}
COLLEGAMENTI_MANUALI_FBREF = {
    "9d376bef": "Berisha M.",
    "47f2af81": "Bleve",
    "85f7ed25": "Boloca",
    "3cc4bb19": "Candè",
    "e74f0e59": "De Silvestri",
    "776c5e04": "Diawara S.",
    "a83b47fa": "Dominguez B.",
    "cf007308": "Elmas",
    "986693ed": "Gelli F.",
    "b79858d5": "Gudmundsson A.",
    "491a433d": "Hojlund",
    "faa13947": "Jimenez A.",
    "19b3caf7": "Leysen F.",
    "3239a8ed": "Marin R.",
    "11d8aff0": "Martinez Jo.",  # Josep Martínez, Inter
    "f7036e1c": "Martinez L.",
    "547c0119": "Matturro",
    "f49c4ae9": "Messias",
    "c1d95617": "Montipò",
    "fc94b80c": "Mora",
    "12de1b0d": "Moreira",
    "17329380": "N'Dri",
    "b8cd2ae4": "Ndiaye",
    "4f1e6a0b": "Neres",
    "0d94b6d9": "Ordonez C.",
    "b35a7399": "Ostigard",
    "62709ee4": "Oulai",
    "68b7e72e": "Oyono A.",
    "237a3851": "Perez K.",
    "ae67e0c4": "Pieragnolo",
    "1671435c": "Pisseri",
    "ce1a6c7e": "Raimondo",
    "f9f74e43": "Rodriguez Je.",
    "8f72c9d2": "Rodriguez Ju.",
    "b1f0b916": "Satalino",
    "08e57960": "Smolcic I.",
    "a8e7f7e9": "Sommariva",
    "23fb46ea": "Sucic P.",
    "230c3f3a": "Sulemana I.",
    "a62f8bf1": "Sulemana K.",
    "e1b0a70d": "Terracciano",
    "5cbb5ad6": "Terracciano F.",
    "47c609d5": "Tourè I.",
    "77d6fd4d": "Vicario",
    "582a251c": "Vigorito",
    "d8cda243": "Yildiz",
    "986dc2e3": "Ziolkowski",
}
GRIGLIA_PORTIERI_PATH = ROOT / "griglia_portieri" / "Griglia_Portieri_Fantacalcio_Stagione_2026-27.xlsx"
CALENDARIO_PORTIERI_PATH = ROOT / "griglia_portieri" / "calendario_serie_a_2026_2027.txt"
TOP_SQUADRE = {"Ata", "Com", "Int", "Juv", "Mil", "Nap"}
SEMITOP_SQUADRE = {"Fio", "Laz", "Rom"}
SQUADRE_FORTI = TOP_SQUADRE | SEMITOP_SQUADRE
NOMI_GRIGLIA = {"Ata": "Atalanta", "Bol": "Bologna", "Cag": "Cagliari", "Com": "Como", "Fio": "Fiorentina", "Fro": "Frosinone", "Gen": "Genoa", "Int": "Inter", "Juv": "Juventus", "Laz": "Lazio", "Lec": "Lecce", "Mil": "Milan", "Mon": "Monza", "Nap": "Napoli", "Par": "Parma", "Rom": "Roma", "Sas": "Sassuolo", "Tor": "Torino", "Udi": "Udinese", "Ven": "Venezia"}
CODICI_CALENDARIO = {
    "atalantabc": "Ata", "bolognafc1909": "Bol", "cagliaricalcio": "Cag", "como1907": "Com",
    "acffiorentina": "Fio", "frosinonecalcio": "Fro", "genoacfc": "Gen", "fcinternazionalemilano": "Int",
    "juventusfc": "Juv", "sslazio": "Laz", "uslecce": "Lec", "acmilan": "Mil", "acmonza": "Mon",
    "sscnapoli": "Nap", "parmacalcio1913": "Par", "asroma": "Rom", "ussassuolocalcio": "Sas",
    "torinofc": "Tor", "udinesecalcio": "Udi", "veneziafc": "Ven",
}
FASCE = ["Prima fascia", "Seconda fascia", "Terza fascia", "Quarta fascia",
          "Scommesse", "Outsider", "Titolari scarsi", "Da assegnare"]
ORDINE_FASCE = {fascia: indice for indice, fascia in enumerate(FASCE)}
COLORI_FASCE = {
    "Prima fascia": "#f6c453", "Seconda fascia": "#9bd4a7",
    "Terza fascia": "#9dc7e8", "Quarta fascia": "#d7dce3", "Scommesse": "#c8b6e8",
    "Outsider": "#f0c590", "Titolari scarsi": "#e5b5b5", "Da assegnare": "#e9edf2",
}
GLOSSARIO = {
    "fvm": "FVM — Fantavalore di Mercato: stima su scala 0-1000.",
    "qta": "Quotazione attuale Classic — valore del calciatore nell'ultima quotazione disponibile.",
    "qti": "Quotazione iniziale Classic — valore del calciatore a inizio stagione.",
    "pv": "Presenze a voto — partite per cui il calciatore ha ricevuto un voto.",
    "mv": "Media voto — media dei voti senza bonus e malus.",
    "fm": "Fantamedia — media dei fantavoti, inclusi bonus e malus.",
    "gf": "Gol fatti.", "gs": "Gol subiti — rilevante per i portieri.", "ass": "Assist.", "g+a": "Gol + assist — somma dei bonus offensivi.",
    "amm": "Ammonizioni.", "esp": "Espulsioni.",
}
STATISTICHE_ELENCO = (
    ("fvm", "FVM ⓘ", "q.fvm"), ("qta", "Qt. attuale ⓘ", "q.quotazione_attuale"),
    ("qti", "Qt. iniziale ⓘ", "q.quotazione_iniziale"), ("pv", "PV ⓘ", "s.presenze"),
    ("mv", "MV ⓘ", "s.mv"), ("fm", "FM ⓘ", "s.fm"), ("gf", "Gol ⓘ", "s.gol_fatti"),
    ("gs", "GS ⓘ", "s.gol_subiti"), ("ass", "Assist ⓘ", "s.assist"),
    ("amm", "Amm. ⓘ", "s.ammonizioni"), ("esp", "Esp. ⓘ", "s.espulsioni"),
)
FONTI_FBREF = ("standard_stats", "shooting_stats", "time", "misc", "goalkeeping")
METRICHE_NEGATIVE = {"Gol subiti", "Gol subiti /90", "Rigori causati", "Autogol", "Ammonizioni", "Espulsioni", "Seconde ammonizioni", "Falli commessi"}
NUMERI_GRASSETTO = str.maketrans("0123456789", "𝟬𝟭𝟮𝟯𝟰𝟱𝟲𝟳𝟴𝟵")
ETICHETTE_FBREF = {
    "# Pl": "Giocatori impiegati", "Age": "Età media", "Poss": "Possesso (%)",
    "MP": "Partite disputate", "Starts": "Presenze da titolare", "Min": "Minuti giocati", "90s": "Partite equivalenti (90')",
    "Gls": "Gol", "Ast": "Assist", "G+A": "Gol + assist", "G-PK": "Gol senza rigori", "G+A-PK": "Gol + assist senza rigori", "PK": "Rigori segnati", "PKatt": "Rigori tirati",
    "CrdY": "Ammonizioni", "CrdR": "Espulsioni", "Sh": "Tiri", "SoT": "Tiri in porta", "SoT%": "Precisione tiri in porta (%)",
    "Sh/90": "Tiri /90", "SoT/90": "Tiri in porta /90", "G/Sh": "Gol per tiro", "G/SoT": "Gol per tiro in porta",
    "Mn/MP": "Minuti per partita", "Min%": "Minuti giocati (%)", "Mn/Start": "Minuti per titolarità", "Compl": "Partite complete",
    "Subs": "Subentri", "Mn/Sub": "Minuti per subentro", "unSub": "Panchine senza ingresso", "PPM": "Punti per partita",
    "onG": "Gol squadra in campo", "onGA": "Gol subiti squadra in campo", "+/-": "Differenza reti in campo", "+/-90": "Differenza reti /90", "On-Off": "Impatto On-Off",
    "2CrdY": "Seconde ammonizioni", "Fls": "Falli commessi", "Fld": "Falli subiti", "Off": "Fuorigioco", "Crs": "Cross",
    "Int": "Intercetti", "TklW": "Contrasti vinti", "PKwon": "Rigori procurati", "PKcon": "Rigori causati", "OG": "Autogol",
    "GA": "Gol subiti", "GA90": "Gol subiti /90", "SoTA": "Tiri in porta subiti", "Saves": "Parate", "Save%": "Parate (%)",
    "W": "Vittorie", "D": "Pareggi", "L": "Sconfitte", "CS": "Clean sheet", "CS%": "Clean sheet (%)", "PKA": "Rigori subiti",
    "PKsv": "Rigori parati", "PKm": "Rigori falliti avversari",
}


def normalizza(testo: str) -> str:
    testo = (testo or "").translate(str.maketrans({"ø": "o", "Ø": "O", "ł": "l", "Ł": "L", "ß": "ss"}))
    testo = unicodedata.normalize("NFKD", testo)
    testo = "".join(c for c in testo if not unicodedata.combining(c))
    return re.sub(r"[^a-z0-9]", "", testo.lower())


def numero(valore: str | None) -> float | None:
    if valore in (None, "", "-"):
        return None
    try:
        return float(str(valore).replace(",", "."))
    except ValueError:
        return None


def righe_xlsx(percorso: Path) -> list[list[str]]:
    with zipfile.ZipFile(percorso) as archivio:
        condivise: list[str] = []
        if "xl/sharedStrings.xml" in archivio.namelist():
            radice = ET.fromstring(archivio.read("xl/sharedStrings.xml"))
            condivise = ["".join(n.itertext()) for n in radice.iter(XLSX_NS + "si")]
        foglio = ET.fromstring(archivio.read("xl/worksheets/sheet1.xml"))
        risultato = []
        for riga in foglio.iter(XLSX_NS + "row"):
            celle: dict[int, str] = {}
            massimo = -1
            for cella in riga.findall(XLSX_NS + "c"):
                riferimento = cella.get("r", "A1")
                colonna = 0
                for lettera in re.match(r"[A-Z]+", riferimento).group(0):
                    colonna = colonna * 26 + ord(lettera) - 64
                colonna -= 1
                valore = cella.find(XLSX_NS + "v")
                testo = "" if valore is None else valore.text or ""
                if cella.get("t") == "s" and testo:
                    testo = condivise[int(testo)]
                celle[colonna] = testo
                massimo = max(massimo, colonna)
            risultato.append([celle.get(indice, "") for indice in range(massimo + 1)])
        return risultato


def leggi_griglia_portieri() -> tuple[list[str], dict[str, dict[str, int]]]:
    """Legge la matrice degli incroci dalla griglia locale dei portieri."""
    righe = righe_xlsx(GRIGLIA_PORTIERI_PATH)
    squadre = [codice for codice in righe[1][1:] if codice]
    matrice: dict[str, dict[str, int]] = {}
    for riga in righe[2:]:
        if not riga or not riga[0] or riga[0] not in squadre:
            continue
        codice = riga[0]
        matrice[codice] = {}
        for indice, avversaria in enumerate(squadre, start=1):
            if indice >= len(riga) or not riga[indice]:
                continue
            try:
                matrice[codice][avversaria] = int(float(riga[indice]))
            except ValueError:
                continue
    return squadre, matrice


def leggi_calendario_portieri() -> dict[int, dict[str, str]]:
    """Restituisce, per ogni giornata, l'avversaria di ciascuna squadra."""
    if not CALENDARIO_PORTIERI_PATH.exists():
        raise FileNotFoundError("Calendario portieri non trovato.")
    calendario: dict[int, dict[str, str]] = {}
    giornata: int | None = None
    espressione = re.compile(r"^\s*(?:\d{1,2}:\d{2}\s+)?(.+?)\s+v\s+(.+?)(?:\s+\d+-\d+.*)?\s*$")
    for riga in CALENDARIO_PORTIERI_PATH.read_text(encoding="utf-8").splitlines():
        trovata = re.match(r"\s*▪\s*Matchday\s+(\d+)", riga)
        if trovata:
            giornata = int(trovata.group(1))
            calendario[giornata] = {}
            continue
        incontro = espressione.match(riga)
        if giornata is None or not incontro:
            continue
        casa = CODICI_CALENDARIO.get(normalizza(incontro.group(1)))
        trasferta = CODICI_CALENDARIO.get(normalizza(incontro.group(2)))
        if casa and trasferta:
            calendario[giornata][casa] = trasferta
            calendario[giornata][trasferta] = casa
    if len(calendario) != 38 or any(len(avversarie) != 20 for avversarie in calendario.values()):
        raise ValueError("Calendario portieri incompleto o non riconosciuto.")
    return calendario


def valuta_trio_portieri(combinazione: tuple[str, ...], calendario: dict[int, dict[str, str]]) -> tuple[int, int]:
    """Conta le giornate senza un portiere al riparo da top e semitop."""
    senza_alternativa = 0
    scelte_sicure = 0
    for avversarie in calendario.values():
        sicure = sum(avversarie.get(squadra) not in SQUADRE_FORTI for squadra in combinazione)
        if not sicure:
            senza_alternativa += 1
        scelte_sicure += sicure
    return senza_alternativa, scelte_sicure


def stagione_da_nome(percorso: Path) -> str:
    trovato = re.search(r"(20\d{2})_(\d{2})", percorso.name)
    if not trovato:
        raise ValueError(f"Stagione non riconosciuta: {percorso.name}")
    return f"{trovato.group(1)}-{trovato.group(2)}"


def stagione_da_cartella(cartella: Path) -> str | None:
    trovato = re.fullmatch(r"(20\d{2})_(20\d{2})", cartella.name)
    if not trovato:
        return None
    return f"{trovato.group(1)}-{trovato.group(2)[-2:]}"


def crea_database(connessione: sqlite3.Connection) -> None:
    connessione.executescript("""
        PRAGMA foreign_keys = OFF;
        CREATE TABLE IF NOT EXISTS giocatori (
            id INTEGER PRIMARY KEY,
            nome TEXT NOT NULL,
            nome_normalizzato TEXT NOT NULL,
            ruolo TEXT,
            squadra TEXT,
            in_quotazioni_correnti INTEGER NOT NULL DEFAULT 0,
            foto_locale TEXT
        );
        CREATE TABLE IF NOT EXISTS statistiche_fanta (
            giocatore_id INTEGER NOT NULL REFERENCES giocatori(id),
            stagione TEXT NOT NULL,
            squadra TEXT,
            presenze REAL, mv REAL, fm REAL, gol_fatti REAL, gol_subiti REAL,
            assist REAL, ammonizioni REAL, espulsioni REAL, dati_json TEXT NOT NULL,
            PRIMARY KEY (giocatore_id, stagione)
        );
        CREATE TABLE IF NOT EXISTS quotazioni_fanta (
            giocatore_id INTEGER NOT NULL REFERENCES giocatori(id),
            stagione TEXT NOT NULL,
            squadra TEXT,
            quotazione_attuale REAL, quotazione_iniziale REAL, fvm REAL,
            dati_json TEXT NOT NULL,
            PRIMARY KEY (giocatore_id, stagione)
        );
        CREATE TABLE IF NOT EXISTS tag_asta (
            giocatore_id INTEGER NOT NULL REFERENCES giocatori(id),
            categoria TEXT NOT NULL,
            nota TEXT,
            posizione INTEGER,
            PRIMARY KEY (giocatore_id, categoria, nota)
        );
        CREATE TABLE IF NOT EXISTS giocatori_acquistati (
            giocatore_id INTEGER PRIMARY KEY REFERENCES giocatori(id),
            prezzo INTEGER NOT NULL CHECK(prezzo >= 1),
            acquistato_il TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS impostazioni (
            chiave TEXT PRIMARY KEY,
            valore TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS problemi_importazione (
            tipo TEXT NOT NULL,
            descrizione TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS dati_reali_api (
            giocatore_id INTEGER PRIMARY KEY REFERENCES giocatori(id),
            api_giocatore_id INTEGER NOT NULL,
            aggiornato_il TEXT NOT NULL,
            dati_json TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS sincronizzazioni_api (
            id INTEGER PRIMARY KEY,
            avviata_il TEXT NOT NULL,
            conclusa_il TEXT,
            esito TEXT NOT NULL,
            richieste INTEGER NOT NULL DEFAULT 0,
            messaggio TEXT
        );
        CREATE TABLE IF NOT EXISTS statistiche_fbref (
            fbref_id TEXT NOT NULL,
            stagione TEXT NOT NULL,
            nome_fbref TEXT NOT NULL,
            squadra_fbref TEXT,
            posizione_fbref TEXT,
            dati_json TEXT NOT NULL,
            PRIMARY KEY (fbref_id, stagione)
        );
        CREATE TABLE IF NOT EXISTS statistiche_squadre_fbref (
            stagione TEXT NOT NULL,
            squadra TEXT NOT NULL,
            squadra_normalizzata TEXT NOT NULL,
            dati_json TEXT NOT NULL,
            PRIMARY KEY (stagione, squadra)
        );
        CREATE INDEX IF NOT EXISTS indice_squadre_fbref_nome
            ON statistiche_squadre_fbref(squadra_normalizzata, stagione);
        CREATE TABLE IF NOT EXISTS collegamenti_fbref (
            fbref_id TEXT NOT NULL,
            stagione TEXT NOT NULL,
            giocatore_id INTEGER NOT NULL REFERENCES giocatori(id),
            PRIMARY KEY (fbref_id, stagione)
        );
        CREATE TABLE IF NOT EXISTS specialisti_piazzati (
            giocatore_id INTEGER NOT NULL REFERENCES giocatori(id),
            tipo TEXT NOT NULL CHECK(tipo IN ('rigori', 'punizioni', 'angoli')),
            priorita INTEGER NOT NULL,
            fonte TEXT NOT NULL,
            PRIMARY KEY (giocatore_id, tipo)
        );
        CREATE TABLE IF NOT EXISTS indicazioni_formazione (
            giocatore_id INTEGER PRIMARY KEY REFERENCES giocatori(id),
            titolare INTEGER NOT NULL DEFAULT 0 CHECK(titolare IN (0, 1)),
            ballottaggio TEXT NOT NULL DEFAULT '',
            fuori_ruolo TEXT NOT NULL DEFAULT '',
            ballottaggio_vantaggio TEXT NOT NULL DEFAULT '',
            ballottaggio_svantaggio TEXT NOT NULL DEFAULT ''
        );
        CREATE TABLE IF NOT EXISTS anagrafica_giocatori (
            giocatore_id INTEGER PRIMARY KEY REFERENCES giocatori(id),
            nazionalita TEXT NOT NULL,
            codice_nazione TEXT NOT NULL,
            eta INTEGER
        );
        CREATE TABLE IF NOT EXISTS giocatori_venduti (
            giocatore_id INTEGER PRIMARY KEY REFERENCES giocatori(id),
            acquirente TEXT NOT NULL CHECK(acquirente IN ('io', 'avversario')),
            prezzo INTEGER NOT NULL CHECK(prezzo >= 1),
            registrato_il TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS preferenze_giocatori (
            giocatore_id INTEGER PRIMARY KEY REFERENCES giocatori(id),
            preferito INTEGER NOT NULL DEFAULT 0 CHECK(preferito IN (0, 1)),
            escluso INTEGER NOT NULL DEFAULT 0 CHECK(escluso IN (0, 1)),
            nota TEXT NOT NULL DEFAULT ''
        );
        CREATE TABLE IF NOT EXISTS fantallenatori (
            id INTEGER PRIMARY KEY,
            nome TEXT NOT NULL UNIQUE,
            crediti_iniziali INTEGER NOT NULL DEFAULT 600 CHECK(crediti_iniziali >= 1),
            e_mio INTEGER NOT NULL DEFAULT 0 CHECK(e_mio IN (0, 1))
        );
        CREATE TABLE IF NOT EXISTS acquisti_lega (
            giocatore_id INTEGER PRIMARY KEY REFERENCES giocatori(id),
            fantallenatore_id INTEGER NOT NULL REFERENCES fantallenatori(id),
            prezzo INTEGER NOT NULL CHECK(prezzo >= 1),
            registrato_il TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS cronologia_asta (
            id INTEGER PRIMARY KEY,
            azione TEXT NOT NULL CHECK(azione IN ('acquisto', 'rimozione')),
            giocatore_id INTEGER NOT NULL REFERENCES giocatori(id),
            fantallenatore_id INTEGER NOT NULL,
            prezzo INTEGER NOT NULL CHECK(prezzo >= 1),
            registrato_il TEXT NOT NULL
        );
    """)
    assicura_tabelle_riservate(connessione)
    for tabella in TABELLE_FANTACALCIO | TABELLE_ASTA:
        sqlite3.Connection.execute(connessione, f'DROP TABLE IF EXISTS main."{tabella}"')
    connessione.execute("PRAGMA foreign_keys = OFF")
    colonne_formazione = {riga[1] for riga in connessione.execute("PRAGMA fantacalcio.table_info(indicazioni_formazione)")}
    for colonna in ("fuori_ruolo", "ballottaggio_vantaggio", "ballottaggio_svantaggio"):
        if colonna not in colonne_formazione:
            connessione.execute(f"ALTER TABLE indicazioni_formazione ADD COLUMN {colonna} TEXT NOT NULL DEFAULT ''")
    colonne_anagrafica = {riga[1] for riga in connessione.execute("PRAGMA table_info(anagrafica_giocatori)")}
    if "eta" not in colonne_anagrafica:
        connessione.execute("ALTER TABLE anagrafica_giocatori ADD COLUMN eta INTEGER")
    # Una sola rosa può essere quella dell'utente. Le versioni precedenti
    # ricreavano erroneamente "La mia squadra" dopo una rinomina.
    mie_squadre = connessione.execute(
        "SELECT id, nome FROM fantallenatori WHERE e_mio=1 ORDER BY id"
    ).fetchall()
    if len(mie_squadre) > 1:
        for identita, nome in mie_squadre[1:]:
            ha_acquisti = connessione.execute(
                "SELECT 1 FROM acquisti_lega WHERE fantallenatore_id=? LIMIT 1", (identita,)
            ).fetchone()
            if nome == "La mia squadra" and not ha_acquisti:
                connessione.execute("DELETE FROM fantallenatori WHERE id=?", (identita,))
            else:
                connessione.execute("UPDATE fantallenatori SET e_mio=0 WHERE id=?", (identita,))
    if not connessione.execute("SELECT 1 FROM fantallenatori WHERE e_mio=1 LIMIT 1").fetchone():
        connessione.execute("INSERT INTO fantallenatori(nome, crediti_iniziali, e_mio) VALUES ('La mia squadra', 600, 1)")
    connessione.execute("CREATE UNIQUE INDEX IF NOT EXISTS una_sola_mia_squadra ON fantallenatori(e_mio) WHERE e_mio=1")
    migrazione_completata = connessione.execute(
        "SELECT 1 FROM impostazioni WHERE chiave='migrazione_rose_lega_v1'"
    ).fetchone()
    if not migrazione_completata:
        rose_esistenti = connessione.execute("SELECT 1 FROM acquisti_lega LIMIT 1").fetchone()
        if not rose_esistenti:
            connessione.execute("""
                INSERT OR IGNORE INTO giocatori_venduti(giocatore_id, acquirente, prezzo, registrato_il)
                SELECT giocatore_id, 'io', prezzo, acquistato_il FROM giocatori_acquistati
            """)
            connessione.execute("""
                INSERT OR IGNORE INTO fantallenatori(nome, crediti_iniziali, e_mio)
                SELECT 'Avversario', 600, 0 WHERE EXISTS (SELECT 1 FROM giocatori_venduti WHERE acquirente='avversario')
            """)
            connessione.execute("""
                INSERT OR IGNORE INTO acquisti_lega(giocatore_id, fantallenatore_id, prezzo, registrato_il)
                SELECT v.giocatore_id,
                       (CASE WHEN v.acquirente='io'
                             THEN (SELECT id FROM fantallenatori WHERE e_mio=1 ORDER BY id LIMIT 1)
                             ELSE (SELECT id FROM fantallenatori WHERE nome='Avversario') END),
                       v.prezzo, v.registrato_il
                FROM giocatori_venduti v
            """)
        connessione.execute("INSERT INTO impostazioni(chiave, valore) VALUES ('migrazione_rose_lega_v1', 'completata')")
    for precedente, nuova in (("Prima fascia - top", "Prima fascia"),
                              ("Seconda fascia - semitop", "Seconda fascia"),
                              ("Titolari scarsi - copertura", "Titolari scarsi")):
        connessione.execute("""
            DELETE FROM tag_asta
            WHERE categoria=? AND EXISTS (
                SELECT 1 FROM tag_asta t2
                WHERE t2.giocatore_id=tag_asta.giocatore_id AND t2.categoria=?
            )
        """, (precedente, nuova))
        connessione.execute("UPDATE tag_asta SET categoria=? WHERE categoria=?", (nuova, precedente))
    connessione.commit()


def crea_backup_asta(connessione: sqlite3.Connection) -> Path:
    BACKUP_ASTA_DIR.mkdir(parents=True, exist_ok=True)
    nome = datetime.now().strftime("asta_%Y%m%d_%H%M%S_%f.sqlite3")
    destinazione = BACKUP_ASTA_DIR / nome
    connessione.commit()
    shutil.copy2(ASTA_DB_PATH, destinazione)
    return destinazione


def valore(riga: dict[str, str], *nomi: str) -> str:
    for nome in nomi:
        if nome in riga:
            return riga[nome]
    return ""


def dati_solo_classic(intestazioni: list[str], valori: list[str]) -> dict[str, str]:
    esclusi = {"rm", "qtam", "qtim", "diffm", "fvmm"}
    return {titolo: valore for titolo, valore, nome in zip(intestazioni, valori, map(normalizza, intestazioni))
            if nome not in esclusi}


def etichetta_fbref(colonna: str, occorrenza: int) -> str:
    etichetta = ETICHETTE_FBREF.get(colonna, colonna)
    if colonna in {"Gls", "Ast", "G+A", "G-PK", "G+A-PK"} and occorrenza > 1:
        return f"{etichetta} /90"
    if colonna == "Save%" and occorrenza > 1:
        return "Parate rigori (%)"
    return etichetta


def righe_fbref(percorso: Path) -> list[tuple[dict, list[dict]]]:
    righe = list(csv.reader(percorso.open(encoding="utf-8-sig")))
    indice_intestazione = next((indice for indice, riga in enumerate(righe) if riga and riga[0] == "Rk"), None)
    if indice_intestazione is None:
        return []
    intestazioni = righe[indice_intestazione]
    risultato = []
    for riga in righe[indice_intestazione + 1:]:
        if len(riga) < len(intestazioni) or not riga[0] or riga[0] == "Rk":
            continue
        base = dict(zip(intestazioni[:7], riga[:7]))
        occorrenze: dict[str, int] = {}
        metriche = []
        for indice, colonna in enumerate(intestazioni[7:], start=7):
            if colonna in {"Matches", "-9999"}:
                continue
            occorrenze[colonna] = occorrenze.get(colonna, 0) + 1
            valore_metriche = riga[indice]
            codice = f"{colonna}#{occorrenze[colonna]}"
            nome = etichetta_fbref(colonna, occorrenze[colonna])
            metriche.append({"codice": codice, "nome": nome, "valore": valore_metriche,
                             "positivo": nome not in METRICHE_NEGATIVE})
        risultato.append((base | {"id": riga[-1]}, metriche))
    return risultato


def righe_fbref_squadre(percorso: Path) -> list[tuple[str, list[dict]]]:
    righe = list(csv.reader(percorso.open(encoding="utf-8-sig")))
    indice_intestazione = next((indice for indice, riga in enumerate(righe) if riga and riga[0] == "Squad"), None)
    if indice_intestazione is None:
        return []
    intestazioni = righe[indice_intestazione]
    risultato = []
    for riga in righe[indice_intestazione + 1:]:
        if len(riga) < len(intestazioni) or not riga[0] or riga[0] == "Squad":
            continue
        occorrenze: dict[str, int] = {}
        metriche = []
        for indice, colonna in enumerate(intestazioni[1:], start=1):
            occorrenze[colonna] = occorrenze.get(colonna, 0) + 1
            occorrenza = occorrenze[colonna]
            nome = etichetta_fbref(colonna, occorrenza)
            metriche.append({"codice": f"{colonna}#{occorrenza}", "nome": nome,
                             "valore": riga[indice], "positivo": nome not in METRICHE_NEGATIVE})
        risultato.append((riga[0], metriche))
    return risultato


def importa_statistiche_squadre_fbref(connessione: sqlite3.Connection) -> int:
    cartella_radice = ROOT / "statistiche_squadre"
    if not cartella_radice.exists() or not any(cartella_radice.glob("**/*.csv")):
        return 0
    connessione.execute("DELETE FROM statistiche_squadre_fbref")
    importate = 0
    for cartella in sorted((p for p in cartella_radice.iterdir() if p.is_dir()), reverse=True):
        stagione = stagione_da_cartella(cartella)
        if stagione is None:
            continue
        squadre: dict[str, dict] = {}
        for fonte in FONTI_FBREF:
            percorso = cartella / f"{fonte}.csv"
            if not percorso.exists():
                continue
            for squadra, metriche in righe_fbref_squadre(percorso):
                squadre.setdefault(squadra, {})[fonte] = metriche
        for squadra, fonti in squadre.items():
            connessione.execute("INSERT INTO statistiche_squadre_fbref VALUES (?, ?, ?, ?)",
                                (stagione, squadra, normalizza_squadra(squadra), json.dumps(fonti, ensure_ascii=False)))
            importate += 1
    connessione.commit()
    return importate


def punteggio_abbinamento_fbref(candidato: sqlite3.Row, nome_fbref: str, squadra_fbref: str) -> int:
    nome_fanta = candidato["nome_normalizzato"]
    nome_riferimento = normalizza(nome_fbref)
    parole_fanta = re.findall(r"[a-z0-9]+", unicodedata.normalize("NFKD", candidato["nome"].lower()))
    parole_fbref = re.findall(r"[a-z0-9]+", unicodedata.normalize("NFKD", nome_fbref.lower()))
    punteggio = 100 if nome_fanta == nome_riferimento else 0
    if not punteggio and (nome_fanta in nome_riferimento or nome_riferimento in nome_fanta):
        punteggio = 55
    for parola in parole_fanta:
        if len(parola) == 1 and any(altra.startswith(parola) for altra in parole_fbref):
            punteggio += 8
        elif len(parola) > 1 and parola in parole_fbref:
            punteggio += 20
    if normalizza_squadra(candidato["squadra"]) == normalizza_squadra(squadra_fbref):
        punteggio += 45
    return punteggio


def importa_fbref(connessione: sqlite3.Connection) -> tuple[int, int]:
    cartella_radice = ROOT / "statistiche_avanzate"
    if not cartella_radice.exists() or not any(cartella_radice.glob("**/*.csv")):
        return 0, 0
    connessione.execute("DELETE FROM collegamenti_fbref")
    connessione.execute("DELETE FROM statistiche_fbref")
    connessione.execute("DELETE FROM problemi_importazione WHERE tipo='fbref'")
    schede = abbinati = 0
    non_abbinati: list[str] = []
    fonti_non_valide: list[str] = []
    for cartella in sorted((p for p in cartella_radice.iterdir() if p.is_dir()), reverse=True):
        stagione = stagione_da_cartella(cartella)
        if stagione is None:
            continue
        aggregati: dict[str, dict] = {}
        for fonte in FONTI_FBREF:
            percorso = cartella / f"{fonte}.csv"
            if not percorso.exists():
                continue
            righe = righe_fbref(percorso)
            if not righe and percorso.stat().st_size:
                fonti_non_valide.append(f"Statistiche storiche {stagione}: {fonte}.csv senza intestazione valida")
            for base, metriche in righe:
                elemento = aggregati.setdefault(base["id"], {"nome": base["Player"], "squadra": base["Squad"], "posizione": base["Pos"], "fonti": {}})
                elemento["fonti"][fonte] = metriche
        candidati = connessione.execute("""
            SELECT DISTINCT g.id, g.nome, g.nome_normalizzato, s.squadra
            FROM giocatori g JOIN statistiche_fanta s ON s.giocatore_id=g.id
            WHERE s.stagione=?
        """, (stagione,)).fetchall()
        for identita, elemento in aggregati.items():
            connessione.execute("INSERT INTO statistiche_fbref VALUES (?, ?, ?, ?, ?, ?)",
                               (identita, stagione, elemento["nome"], elemento["squadra"], elemento["posizione"], json.dumps(elemento["fonti"], ensure_ascii=False)))
            classificati = sorted(((punteggio_abbinamento_fbref(candidato, elemento["nome"], elemento["squadra"]), candidato) for candidato in candidati), key=lambda x: x[0], reverse=True)
            migliore, candidato = classificati[0] if classificati else (0, None)
            secondo = classificati[1][0] if len(classificati) > 1 else 0
            if candidato and migliore >= 70 and migliore - secondo >= 12:
                connessione.execute("INSERT INTO collegamenti_fbref VALUES (?, ?, ?)", (identita, stagione, candidato["id"]))
                abbinati += 1
            else:
                non_abbinati.append(f"{stagione} — {elemento['nome']}")
            schede += 1
    avvisi = [f"Statistiche storiche: nessun abbinamento certo per {nome}" for nome in non_abbinati]
    avvisi += fonti_non_valide
    connessione.executemany("INSERT INTO problemi_importazione VALUES ('fbref', ?)", ((avviso,) for avviso in avvisi))
    connessione.commit()
    return schede, abbinati


def chiave_api() -> str:
    if not API_KEY_PATH.exists():
        raise RuntimeError("File api_football_key.txt non trovato.")
    chiave = API_KEY_PATH.read_text(encoding="utf-8").strip()
    if not chiave:
        raise RuntimeError("La chiave di aggiornamento è vuota.")
    return chiave


def richiesta_api(percorso: str, parametri: dict[str, int | str]) -> dict:
    url = f"{API_BASE}{percorso}?{urlencode(parametri)}"
    richiesta = Request(url, headers={"x-apisports-key": chiave_api()})
    try:
        with urlopen(richiesta, timeout=30) as risposta:
            dati = json.loads(risposta.read().decode("utf-8"))
    except HTTPError as errore:
        raise RuntimeError(f"Il servizio di aggiornamento ha risposto {errore.code}.") from errore
    except URLError as errore:
        raise RuntimeError(f"Servizio di aggiornamento non disponibile: {errore.reason}") from errore
    if dati.get("errors"):
        raise RuntimeError(f"Errore del servizio di aggiornamento: {dati['errors']}")
    return dati


def normalizza_squadra(testo: str) -> str:
    nome = normalizza(testo)
    sostituzioni = {"acmilan": "milan", "asroma": "roma", "ssclnapoli": "napoli", "sscnapoli": "napoli",
                    "fcinternazionale": "inter", "intermilan": "inter", "hellasverona": "verona"}
    return sostituzioni.get(nome, nome)


def importa_tiratori(connessione: sqlite3.Connection) -> tuple[int, int]:
    precedente = connessione.row_factory
    connessione.row_factory = sqlite3.Row
    try:
        candidati = connessione.execute("SELECT id, nome, nome_normalizzato, squadra FROM giocatori WHERE in_quotazioni_correnti=1").fetchall()
        connessione.execute("DELETE FROM specialisti_piazzati")
        connessione.execute("DELETE FROM problemi_importazione WHERE tipo='tiratori'")
        abbinati = 0
        problemi = []
        for squadra, tipologie in TIRATORI_FCP_2026_27.items():
            della_squadra = [candidato for candidato in candidati if normalizza_squadra(candidato["squadra"]) == normalizza_squadra(squadra)]
            for tipo, nomi in tipologie.items():
                for priorita, nome in enumerate(nomi, start=1):
                    nome_candidato = ALIASES_TIRATORI.get((squadra, nome), nome)
                    classificati = sorted(((punteggio_abbinamento_fbref(candidato, nome_candidato, squadra), candidato) for candidato in della_squadra), key=lambda x: x[0], reverse=True)
                    migliore, candidato = classificati[0] if classificati else (0, None)
                    secondo = classificati[1][0] if len(classificati) > 1 else 0
                    if candidato and migliore >= 70 and migliore - secondo >= 12:
                        connessione.execute("INSERT INTO specialisti_piazzati VALUES (?, ?, ?, ?)", (candidato["id"], tipo, priorita, FONTE_TIRATORI))
                        abbinati += 1
                    else:
                        problemi.append(f"Tiratori: nessun abbinamento certo per {nome} ({squadra}, {tipo})")
        connessione.executemany("INSERT INTO problemi_importazione VALUES ('tiratori', ?)", ((problema,) for problema in problemi))
        connessione.commit()
        return abbinati, len(problemi)
    finally:
        connessione.row_factory = precedente


def importa_infografica(connessione: sqlite3.Connection) -> tuple[int, int]:
    """Importa formazione tipo, ballottaggi e gerarchie che prevalgono sui piazzati esistenti."""
    precedente = connessione.row_factory
    connessione.row_factory = sqlite3.Row
    try:
        giocatori = connessione.execute("SELECT id, nome, nome_normalizzato, squadra FROM giocatori WHERE in_quotazioni_correnti=1").fetchall()
        per_squadra: dict[str, list[sqlite3.Row]] = {}
        for giocatore in giocatori:
            per_squadra.setdefault(normalizza_squadra(giocatore["squadra"]), []).append(giocatore)

        def trova(squadra: str, nome: str) -> sqlite3.Row | None:
            candidati = per_squadra.get(normalizza_squadra(squadra), [])
            classificati = sorted(((punteggio_abbinamento_fbref(candidato, nome, squadra), candidato) for candidato in candidati), key=lambda voce: voce[0], reverse=True)
            migliore, candidato = classificati[0] if classificati else (0, None)
            secondo = classificati[1][0] if len(classificati) > 1 else 0
            return candidato if candidato and migliore >= 70 and migliore - secondo >= 12 else None

        connessione.execute("DELETE FROM indicazioni_formazione")
        associazioni = 0
        for squadra, dati in INFOGRAFICA_2026_27.items():
            indicazioni: dict[int, dict[str, object]] = {}
            for nome in dati["titolari"]:
                giocatore = trova(squadra, nome)
                if giocatore:
                    indicazioni.setdefault(giocatore["id"], {"titolare": False, "avversari": [], "fuori_ruolo": "", "vantaggio": [], "svantaggio": []})["titolare"] = True
            for primo, secondo in dati["ballottaggi"]:
                giocatore_primo, giocatore_secondo = trova(squadra, primo), trova(squadra, secondo)
                if giocatore_primo and giocatore_secondo:
                    indicazioni.setdefault(giocatore_primo["id"], {"titolare": False, "avversari": [], "fuori_ruolo": "", "vantaggio": [], "svantaggio": []})["avversari"].append(giocatore_secondo["nome"])
                    indicazioni.setdefault(giocatore_primo["id"], {"titolare": False, "avversari": [], "fuori_ruolo": "", "vantaggio": [], "svantaggio": []})["vantaggio"].append(giocatore_secondo["nome"])
                    indicazioni.setdefault(giocatore_secondo["id"], {"titolare": False, "avversari": [], "fuori_ruolo": "", "vantaggio": [], "svantaggio": []})["avversari"].append(giocatore_primo["nome"])
                    indicazioni.setdefault(giocatore_secondo["id"], {"titolare": False, "avversari": [], "fuori_ruolo": "", "vantaggio": [], "svantaggio": []})["svantaggio"].append(giocatore_primo["nome"])
            for (squadra_fuori_ruolo, nome), impiego in FUORI_RUOLO_INFOGRAFICA.items():
                if normalizza_squadra(squadra_fuori_ruolo) != normalizza_squadra(squadra):
                    continue
                giocatore = trova(squadra, nome)
                if giocatore:
                    indicazioni.setdefault(giocatore["id"], {"titolare": False, "avversari": [], "fuori_ruolo": "", "vantaggio": [], "svantaggio": []})["fuori_ruolo"] = impiego
            for giocatore_id, indicazione in indicazioni.items():
                avversari = " · ".join(dict.fromkeys(indicazione["avversari"]))
                vantaggio = " · ".join(dict.fromkeys(indicazione["vantaggio"]))
                svantaggio = " · ".join(dict.fromkeys(indicazione["svantaggio"]))
                connessione.execute("INSERT INTO indicazioni_formazione VALUES (?, ?, ?, ?, ?, ?)", (giocatore_id, int(indicazione["titolare"]), avversari, indicazione["fuori_ruolo"], vantaggio, svantaggio))
                associazioni += 1
            giocatori_squadra = per_squadra.get(normalizza_squadra(squadra), [])
            for tipo in ("rigori", "punizioni"):
                connessione.executemany("DELETE FROM specialisti_piazzati WHERE giocatore_id=? AND tipo=?", ((giocatore["id"], tipo) for giocatore in giocatori_squadra))
                for priorita, nome in enumerate(dati[tipo], start=1):
                    giocatore = trova(squadra, nome)
                    if giocatore:
                        connessione.execute("INSERT INTO specialisti_piazzati VALUES (?, ?, ?, ?)", (giocatore["id"], tipo, priorita, FONTE_INFOGRAFICA))
        connessione.executemany("INSERT OR IGNORE INTO indicazioni_formazione VALUES (?, 0, '', '', '', '')", ((giocatore["id"],) for giocatore in giocatori))
        connessione.commit()
        return len(giocatori), 0
    finally:
        connessione.row_factory = precedente


def importa_nazionalita_fbref(connessione: sqlite3.Connection) -> int:
    cartella_radice = ROOT / "statistiche_avanzate"
    if not cartella_radice.exists() or not any(cartella_radice.glob("*/standard_stats.csv")):
        return 0
    collegamenti = {
        (riga[0], riga[1]): riga[2]
        for riga in connessione.execute("""
            SELECT c.fbref_id, c.stagione, c.giocatore_id
            FROM collegamenti_fbref c JOIN giocatori g ON g.id=c.giocatore_id
            WHERE g.in_quotazioni_correnti=1
        """)
    }
    connessione.execute("DELETE FROM anagrafica_giocatori")
    importati = 0
    for cartella in sorted((percorso for percorso in cartella_radice.iterdir() if percorso.is_dir()), reverse=True):
        stagione = stagione_da_cartella(cartella)
        if not stagione:
            continue
        percorso = cartella / "standard_stats.csv"
        if not percorso.exists():
            continue
        for base, _ in righe_fbref(percorso):
            giocatore_id = collegamenti.get((base["id"], stagione))
            codice = (base.get("Nation") or "").split(" ", 1)[0].lower()
            dati_nazione = NAZIONALITA_FBREF.get(codice)
            if not giocatore_id or not dati_nazione:
                continue
            eta = re.match(r"\d+", base.get("Age") or "")
            cursore = connessione.execute(
                "INSERT OR IGNORE INTO anagrafica_giocatori(giocatore_id, nazionalita, codice_nazione, eta) VALUES (?, ?, ?, ?)",
                (giocatore_id, dati_nazione[0], codice, int(eta.group()) if eta else None),
            )
            importati += cursore.rowcount
    connessione.commit()
    return importati


def applica_collegamenti_manuali_fbref(connessione: sqlite3.Connection) -> int:
    applicati = 0
    for fbref_id, nome_giocatore in COLLEGAMENTI_MANUALI_FBREF.items():
        giocatore = connessione.execute("""
            SELECT id FROM giocatori WHERE nome=?
            ORDER BY in_quotazioni_correnti DESC, id DESC LIMIT 1
        """, (nome_giocatore,)).fetchone()
        if not giocatore:
            continue
        connessione.execute("DELETE FROM collegamenti_fbref WHERE fbref_id=?", (fbref_id,))
        cursore = connessione.execute("""
            INSERT OR REPLACE INTO collegamenti_fbref(fbref_id, stagione, giocatore_id)
            SELECT fbref_id, stagione, ? FROM statistiche_fbref WHERE fbref_id=?
        """, (giocatore[0], fbref_id))
        applicati += cursore.rowcount
    connessione.commit()
    return applicati


def punteggio_abbinamento(giocatore_fanta: sqlite3.Row, giocatore_api: dict) -> int:
    profilo = giocatore_api.get("player", {})
    statistiche = giocatore_api.get("statistics") or []
    squadra_api = statistiche[0].get("team", {}).get("name", "") if statistiche else ""
    nome_completo = NOMI_WIKIMEDIA.get(giocatore_fanta["nome"], giocatore_fanta["nome"])
    nome_fanta = normalizza(nome_completo)
    parole_fanta = re.findall(r"[a-z0-9]+", unicodedata.normalize("NFKD", nome_completo.lower()))
    candidati_nome = [normalizza(profilo.get(campo, "")) for campo in ("name", "firstname", "lastname")]
    nome_api = normalizza(" ".join(str(profilo.get(campo, "")) for campo in ("firstname", "lastname", "name")))
    parole_api = re.findall(r"[a-z0-9]+", unicodedata.normalize("NFKD", " ".join(str(profilo.get(campo, "")) for campo in ("firstname", "lastname", "name")).lower()))
    punteggio = 0
    if nome_fanta in candidati_nome or nome_fanta == nome_api:
        punteggio += 100
    elif nome_fanta in nome_api or nome_api in nome_fanta:
        punteggio += 55
    for parola in parole_fanta:
        if len(parola) == 1 and any(altra.startswith(parola) for altra in parole_api):
            punteggio += 8
        elif len(parola) > 1 and parola in parole_api:
            punteggio += 20
    if normalizza_squadra(giocatore_fanta["squadra"]) == normalizza_squadra(squadra_api):
        punteggio += 45
    return punteggio


def sincronizza_serie_a(notifica=None) -> tuple[int, int, int]:
    """Scarica rose correnti, anagrafica e foto senza endpoint stagionali a pagamento."""
    def avvisa(testo: str) -> None:
        if notifica:
            notifica(testo)

    connessione = apri_connessione()
    connessione.row_factory = sqlite3.Row
    crea_database(connessione)
    avviata = datetime.now().isoformat(timespec="seconds")
    cursore = connessione.execute("INSERT INTO sincronizzazioni_api(avviata_il, esito) VALUES (?, 'in corso')", (avviata,))
    sincronizzazione_id = cursore.lastrowid
    richieste = 0
    try:
        fanta = connessione.execute("SELECT id, nome, nome_normalizzato, squadra FROM giocatori WHERE in_quotazioni_correnti=1").fetchall()
        squadre_fanta = sorted({giocatore["squadra"] for giocatore in fanta})
        rose_api: list[dict] = []
        squadre_non_trovate: list[str] = []
        for indice, squadra_fanta in enumerate(squadre_fanta, start=1):
            avvisa(f"Cerco squadra {indice}/{len(squadre_fanta)}: {squadra_fanta}…")
            risposta = richiesta_api("/teams", {"search": squadra_fanta})
            richieste += 1
            candidati = [squadra for squadra in risposta.get("response", [])
                          if squadra.get("team", {}).get("country") == "Italy"
                          and normalizza_squadra(squadra.get("team", {}).get("name", "")) == normalizza_squadra(squadra_fanta)]
            if len(candidati) != 1:
                squadre_non_trovate.append(squadra_fanta)
                time.sleep(6.1)
                continue
            squadra_api = candidati[0]["team"]
            time.sleep(6.1)
            avvisa(f"Scarico rosa {indice}/{len(squadre_fanta)}: {squadra_api['name']}…")
            rosa = richiesta_api("/players/squads", {"team": squadra_api["id"]})
            richieste += 1
            for blocco in rosa.get("response", []):
                for giocatore_api in blocco.get("players", []):
                    rose_api.append({"player": giocatore_api, "statistics": [{"team": squadra_api}], "team": squadra_api})
            time.sleep(6.1)
        abbinati = 0
        non_abbinati: list[str] = []
        connessione.execute("DELETE FROM problemi_importazione WHERE tipo='api'")
        for giocatore in fanta:
            classificati = sorted(((punteggio_abbinamento(giocatore, candidato), candidato) for candidato in rose_api), key=lambda x: x[0], reverse=True)
            migliore, candidato = classificati[0] if classificati else (0, None)
            secondo = classificati[1][0] if len(classificati) > 1 else 0
            if not candidato or migliore < 65 or migliore - secondo < 12:
                non_abbinati.append(giocatore["nome"])
                continue
            profilo = candidato.get("player", {})
            connessione.execute("""
                INSERT INTO dati_reali_api VALUES (?, ?, ?, ?)
                ON CONFLICT(giocatore_id) DO UPDATE SET
                    api_giocatore_id=excluded.api_giocatore_id, aggiornato_il=excluded.aggiornato_il, dati_json=excluded.dati_json
            """, (giocatore["id"], profilo["id"], datetime.now().isoformat(timespec="seconds"), json.dumps(candidato, ensure_ascii=False)))
            abbinati += 1
        avvisi = [f"Dati squadra: nessun abbinamento certo per {nome}" for nome in non_abbinati]
        avvisi += [f"Dati squadra: squadra non trovata — {nome}" for nome in squadre_non_trovate]
        connessione.executemany("INSERT INTO problemi_importazione VALUES ('api', ?)", ((avviso,) for avviso in avvisi))
        messaggio = f"{abbinati} giocatori collegati; {len(non_abbinati)} da verificare; {len(squadre_non_trovate)} squadre non trovate."
        connessione.execute("UPDATE sincronizzazioni_api SET conclusa_il=?, esito='completata', richieste=?, messaggio=? WHERE id=?",
                           (datetime.now().isoformat(timespec="seconds"), richieste, messaggio, sincronizzazione_id))
        connessione.commit()
        avvisa(messaggio)
        return richieste, abbinati, len(non_abbinati)
    except Exception as errore:
        connessione.execute("UPDATE sincronizzazioni_api SET conclusa_il=?, esito='errore', richieste=?, messaggio=? WHERE id=?",
                           (datetime.now().isoformat(timespec="seconds"), richieste, str(errore), sincronizzazione_id))
        connessione.commit()
        raise
    finally:
        connessione.close()


def scarica_foto_api(notifica=None, forza: bool = False) -> tuple[int, int]:
    def avvisa(testo: str) -> None:
        if notifica:
            notifica(testo)

    FOTO_DIR.mkdir(parents=True, exist_ok=True)
    connessione = apri_connessione()
    righe = connessione.execute("SELECT d.giocatore_id, d.dati_json FROM dati_reali_api d ORDER BY d.giocatore_id").fetchall()
    scaricate = errori = 0
    try:
        for indice, (giocatore_id, dati_json) in enumerate(righe, start=1):
            dati = json.loads(dati_json)
            url = dati.get("player", {}).get("photo")
            if not url:
                continue
            destinazione = FOTO_DIR / f"{giocatore_id}.png"
            if destinazione.exists() and destinazione.stat().st_size > 0 and not forza:
                connessione.execute("UPDATE giocatori SET foto_locale=? WHERE id=?", (str(destinazione), giocatore_id))
                continue
            if indice == 1 or indice == len(righe) or indice % 20 == 0:
                avvisa(f"Scarico foto {indice}/{len(righe)}…")
            try:
                richiesta = Request(url, headers={"User-Agent": "AssistenteAstaFantacalcio/1.0"})
                with urlopen(richiesta, timeout=20) as risposta:
                    contenuto = risposta.read()
                if not contenuto:
                    raise RuntimeError("immagine vuota")
                destinazione.write_bytes(contenuto)
                connessione.execute("UPDATE giocatori SET foto_locale=? WHERE id=?", (str(destinazione), giocatore_id))
                scaricate += 1
            except (HTTPError, URLError, OSError, RuntimeError):
                errori += 1
        connessione.commit()
        avvisa(f"Foto disponibili: {scaricate}; non scaricate: {errori}.")
        return scaricate, errori
    finally:
        connessione.close()


def richiesta_wikimedia(parametri: dict[str, str]) -> dict:
    url = f"{WIKIDATA_API}?{urlencode(parametri)}"
    richiesta = Request(url, headers={"User-Agent": "AssistenteAstaFantacalcio/1.0 (uso personale offline)"})
    for tentativo in range(3):
        try:
            with urlopen(richiesta, timeout=20) as risposta:
                return json.loads(risposta.read().decode("utf-8"))
        except HTTPError as errore:
            if errore.code == 429 and tentativo < 2:
                attesa = errore.headers.get("Retry-After", "6")
                time.sleep(float(attesa) if attesa.replace(".", "", 1).isdigit() else 6)
                continue
            raise RuntimeError(f"Wikimedia ha risposto {errore.code}.") from errore
        except URLError as errore:
            raise RuntimeError(f"Wikimedia non è disponibile: {errore.reason}") from errore
    raise RuntimeError("Wikimedia non ha risposto.")


def foto_wikipedia(nome: str) -> bytes | None:
    """Usa solo una pagina esatta di un calciatore come fallback ai ritratti P18."""
    for lingua in ("it", "en"):
        richiesta = Request(
            f"https://{lingua}.wikipedia.org/api/rest_v1/page/summary/{quote(nome)}",
            headers={"User-Agent": "AssistenteAstaFantacalcio/1.0 (uso personale offline)"},
        )
        try:
            with urlopen(richiesta, timeout=20) as risposta:
                dati = json.loads(risposta.read().decode("utf-8"))
        except (HTTPError, URLError):
            continue
        descrizione = (dati.get("description") or "").lower()
        miniatura = dati.get("thumbnail", {}).get("source")
        if not miniatura or not any(parola in descrizione for parola in ("calciatore", "footballer", "football player")):
            continue
        try:
            with urlopen(Request(miniatura, headers={"User-Agent": "AssistenteAstaFantacalcio/1.0 (uso personale offline)"}), timeout=25) as risposta:
                return risposta.read() or None
        except (HTTPError, URLError):
            continue
    return None


def foto_wikimedia(nome: str) -> bytes | None:
    """Restituisce un ritratto Wikimedia verificato, con fallback Wikipedia esatto."""
    try:
        ricerca = richiesta_wikimedia({
            "action": "wbsearchentities", "search": nome, "language": "it", "format": "json", "limit": "6",
        })
    except RuntimeError:
        return foto_wikipedia(nome)
    candidati = ricerca.get("search", [])
    esatto = next((candidato for candidato in candidati
                   if normalizza(candidato.get("label", "")) == normalizza(nome)
                   and any(parola in candidato.get("description", "").lower()
                           for parola in ("calciatore", "footballer", "football player"))), None)
    if not esatto:
        return foto_wikipedia(nome)
    time.sleep(0.65)
    try:
        entita = richiesta_wikimedia({
            "action": "wbgetentities", "ids": esatto["id"], "props": "claims", "format": "json",
        })
    except RuntimeError:
        return foto_wikipedia(nome)
    dichiarazioni = entita.get("entities", {}).get(esatto["id"], {}).get("claims", {}).get("P18", [])
    nome_file = dichiarazioni[0].get("mainsnak", {}).get("datavalue", {}).get("value") if dichiarazioni else None
    if nome_file:
        richiesta = Request(f"{WIKIMEDIA_FILE_PATH}{quote(nome_file)}?width=180",
                             headers={"User-Agent": "AssistenteAstaFantacalcio/1.0 (uso personale offline)"})
        try:
            with urlopen(richiesta, timeout=25) as risposta:
                contenuto = risposta.read()
            if contenuto:
                return contenuto
        except (HTTPError, URLError):
            pass
    return foto_wikipedia(nome)


def scarica_foto_wikimedia(notifica=None) -> tuple[int, int]:
    """Completa le foto mancanti con ritratti Wikimedia Commons verificati da Wikidata."""
    def avvisa(testo: str) -> None:
        if notifica:
            notifica(testo)

    FOTO_DIR.mkdir(parents=True, exist_ok=True)
    connessione = apri_connessione()
    righe = connessione.execute("""
        SELECT id, nome FROM giocatori
        WHERE in_quotazioni_correnti=1 AND (foto_locale IS NULL OR foto_locale='')
        ORDER BY ruolo, nome
    """).fetchall()
    scaricate = errori = 0
    try:
        for indice, (giocatore_id, nome) in enumerate(righe, start=1):
            nome_completo = NOMI_WIKIMEDIA.get(nome)
            if not nome_completo:
                continue
            avvisa(f"Cerco foto {indice}/{len(righe)}: {nome}…")
            try:
                contenuto = foto_wikimedia(nome_completo)
                if not contenuto:
                    errori += 1
                    continue
                destinazione = FOTO_DIR / f"{giocatore_id}.png"
                destinazione.write_bytes(contenuto)
                connessione.execute("UPDATE giocatori SET foto_locale=? WHERE id=?", (str(destinazione), giocatore_id))
                connessione.commit()
                scaricate += 1
            except (OSError, RuntimeError):
                errori += 1
            time.sleep(0.65)
        connessione.commit()
        avvisa(f"Foto aggiunte: {scaricate}; senza ritratto verificato: {errori}.")
        return scaricate, errori
    finally:
        connessione.close()


def scarica_bandiere_flagsnet(notifica=None, forza: bool = False) -> tuple[int, int]:
    def avvisa(testo: str) -> None:
        if notifica:
            notifica(testo)

    BANDIERE_DIR.mkdir(parents=True, exist_ok=True)
    connessione = apri_connessione()
    codici = [riga[0] for riga in connessione.execute("SELECT DISTINCT codice_nazione FROM anagrafica_giocatori ORDER BY codice_nazione")]
    scaricate = errori = 0
    try:
        richiesta_indice = Request(f"{FLAGS_NET}fullindex.htm", headers={"User-Agent": "AssistenteAstaFantacalcio/1.0 (uso personale offline)"})
        with urlopen(richiesta_indice, timeout=30) as risposta:
            indice = risposta.read().decode("utf-8", "replace")
        bandiere = {
            normalizza(unescape(nome)): percorso
            for percorso, nome in re.findall(r'<img src="(images/smallflags/[^"]+)"[^>]*\s*/></td><td[^>]*><b>(.*?)</b><br', indice, re.DOTALL)
        }
        alias = {
            "Bosnia and Herzegovina": "Bosnia-Herzegovina",
            "Côte d'Ivoire": "Ivory Coast",
            "the Czech Republic": "The Czech Republic",
            "the Gambia": "The Gambia",
            "North Macedonia": "Macedonia",
            "the Netherlands": "Holland",
            "the United States": "United States",
        }
        percorsi_speciali = {
            "eng": "images/smallflags/UNKG0100.GIF",
            "sct": "images/smallflags/UNKG0101.GIF",
        }
        for indice, codice in enumerate(codici, start=1):
            destinazione = BANDIERE_DIR / f"{codice}.png"
            if not forza and destinazione.exists() and destinazione.stat().st_size > 0:
                continue
            nazione = NAZIONALITA_FBREF.get(codice, ("", ""))[1]
            if not nazione:
                errori += 1
                continue
            avvisa(f"Scarico bandiere {indice}/{len(codici)}…")
            try:
                percorso = percorsi_speciali.get(codice) or bandiere.get(normalizza(alias.get(nazione, nazione)))
                if not percorso:
                    raise RuntimeError("bandiera non trovata")
                richiesta = Request(f"{FLAGS_NET}{quote(percorso)}", headers={"User-Agent": "AssistenteAstaFantacalcio/1.0 (uso personale offline)"})
                with urlopen(richiesta, timeout=20) as risposta:
                    contenuto = risposta.read()
                if not contenuto:
                    raise RuntimeError("immagine vuota")
                with Image.open(BytesIO(contenuto)) as immagine:
                    immagine.verify()
                destinazione.write_bytes(contenuto)
                scaricate += 1
            except (HTTPError, URLError, OSError, RuntimeError, IndexError):
                errori += 1
            time.sleep(.15)
        avvisa(f"Bandiere scaricate: {scaricate}; non disponibili: {errori}.")
        return scaricate, errori
    finally:
        connessione.close()


def scarica_stemmi_api(notifica=None) -> tuple[int, int]:
    def avvisa(testo: str) -> None:
        if notifica:
            notifica(testo)

    STEMMI_DIR.mkdir(parents=True, exist_ok=True)
    connessione = apri_connessione()
    stemmi: dict[int, str] = {}
    try:
        for (dati_json,) in connessione.execute("SELECT dati_json FROM dati_reali_api"):
            squadra = json.loads(dati_json).get("team", {})
            if squadra.get("id") and squadra.get("logo"):
                stemmi[squadra["id"]] = squadra["logo"]
        scaricati = errori = 0
        for indice, (squadra_id, url) in enumerate(stemmi.items(), start=1):
            destinazione = STEMMI_DIR / f"{squadra_id}.png"
            if destinazione.exists() and destinazione.stat().st_size > 0:
                continue
            avvisa(f"Scarico stemmi {indice}/{len(stemmi)}…")
            try:
                richiesta = Request(url, headers={"User-Agent": "AssistenteAstaFantacalcio/1.0"})
                with urlopen(richiesta, timeout=20) as risposta:
                    contenuto = risposta.read()
                if not contenuto:
                    raise RuntimeError("immagine vuota")
                destinazione.write_bytes(contenuto)
                scaricati += 1
            except (HTTPError, URLError, OSError, RuntimeError):
                errori += 1
        avvisa(f"Stemmi disponibili: {scaricati}; non scaricati: {errori}.")
        return scaricati, errori
    finally:
        connessione.close()


def importa_fantacalcio(connessione: sqlite3.Connection) -> tuple[int, int]:
    connessione.execute("DELETE FROM statistiche_fanta")
    connessione.execute("DELETE FROM quotazioni_fanta")
    connessione.execute("UPDATE giocatori SET in_quotazioni_correnti = 0")
    file_statistiche = sorted((ROOT / "statistiche").glob("*.xlsx"))
    file_quotazioni = sorted((ROOT / "quotazioni").glob("*.xlsx"))
    conteggi = [0, 0]

    sorgenti = [("statistiche", p) for p in file_statistiche]
    sorgenti += [("quotazioni", p) for p in file_quotazioni]
    for tipo, file in sorgenti:
        righe = righe_xlsx(file)
        if len(righe) < 3:
            continue
        intestazioni = [normalizza(x) for x in righe[1]]
        stagione = stagione_da_nome(file)
        for valori in righe[2:]:
            riga = dict(zip(intestazioni, valori))
            identita = valore(riga, "id")
            nome = valore(riga, "nome")
            if not identita or not nome:
                continue
            ruolo = valore(riga, "r")
            squadra = valore(riga, "squadra")
            connessione.execute("""
                INSERT INTO giocatori(id, nome, nome_normalizzato, ruolo, squadra)
                VALUES (?, ?, ?, ?, ?)
                ON CONFLICT(id) DO UPDATE SET
                    nome=excluded.nome, nome_normalizzato=excluded.nome_normalizzato,
                    ruolo=excluded.ruolo, squadra=excluded.squadra
            """, (int(identita), nome, normalizza(nome), ruolo, squadra))
            if tipo == "statistiche":
                connessione.execute("""
                    INSERT INTO statistiche_fanta VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """, (int(identita), stagione, squadra, numero(valore(riga, "pv")), numero(valore(riga, "mv")),
                      numero(valore(riga, "fm")), numero(valore(riga, "gf")), numero(valore(riga, "gs")),
                      numero(valore(riga, "ass")), numero(valore(riga, "amm")), numero(valore(riga, "esp")),
                      json.dumps(dati_solo_classic(righe[1], valori), ensure_ascii=False)))
                conteggi[0] += 1
            else:
                corrente = stagione == "2026-27"
                connessione.execute("""
                    INSERT INTO quotazioni_fanta VALUES (?, ?, ?, ?, ?, ?, ?)
                """, (int(identita), stagione, squadra, numero(valore(riga, "qta")), numero(valore(riga, "qti")),
                      numero(valore(riga, "fvm")), json.dumps(dati_solo_classic(righe[1], valori), ensure_ascii=False)))
                if corrente:
                    connessione.execute("UPDATE giocatori SET in_quotazioni_correnti=1 WHERE id=?", (int(identita),))
                conteggi[1] += 1
    normalizza_percorsi_foto(connessione)
    connessione.commit()
    return tuple(conteggi)


def paragrafi_docx(percorso: Path) -> list[str]:
    with zipfile.ZipFile(percorso) as archivio:
        radice = ET.fromstring(archivio.read("word/document.xml"))
    return ["".join(paragrafo.itertext()).replace("\u00a0", " ").strip()
            for paragrafo in radice.iter(WORD_NS + "p")]


def categoria_normalizzata(testo: str) -> str | None:
    basso = testo.lower()
    if "prima" in basso and "fascia" in basso:
        return "Prima fascia"
    if "seconda" in basso and "fascia" in basso:
        return "Seconda fascia"
    if "terza" in basso and "fascia" in basso:
        return "Terza fascia"
    if "quarta" in basso and "fascia" in basso:
        return "Quarta fascia"
    if basso.startswith("scommesse"):
        return "Scommesse"
    if basso.startswith("outsider"):
        return "Outsider"
    if basso.startswith("titolari scarsi"):
        return "Titolari scarsi"
    return None


def importa_fasce(connessione: sqlite3.Connection, percorso: Path) -> tuple[int, list[str]]:
    connessione.execute("DELETE FROM tag_asta")
    connessione.execute("DELETE FROM problemi_importazione WHERE tipo='fasce'")
    ruolo = categoria = None
    posizione = 0
    problemi: list[str] = []
    for testo in paragrafi_docx(percorso):
        if testo in {"Portieri", "Difensori", "Centrocampisti", "Attaccanti"}:
            ruolo = {"Portieri": "P", "Difensori": "D", "Centrocampisti": "C", "Attaccanti": "A"}[testo]
            categoria = "Da assegnare" if ruolo in {"C", "A"} else None
            continue
        nuova_categoria = categoria_normalizzata(testo)
        if nuova_categoria:
            categoria = nuova_categoria
            continue
        if not testo.startswith("□") or not ruolo:
            continue
        abbinato = re.match(r"^□\s*(.*?)\s*\(([A-Z]+)\)\s*(?:-\s*(.*))?$", testo)
        if not abbinato:
            problemi.append(f"Riga non letta: {testo}")
            continue
        nome, codice, nota = abbinato.groups()
        squadra = TEAM_CODES.get(codice, codice)
        nome_normale = normalizza(nome)
        candidati = connessione.execute("""
            SELECT id, nome, ruolo, squadra FROM giocatori
            WHERE in_quotazioni_correnti=1 AND ruolo=? AND lower(squadra)=lower(?) AND nome_normalizzato=?
        """, (ruolo, squadra, nome_normale)).fetchall()
        if len(candidati) != 1:
            candidati = connessione.execute("""
                SELECT id, nome, ruolo, squadra FROM giocatori
                WHERE in_quotazioni_correnti=1 AND nome_normalizzato=?
            """, (nome_normale,)).fetchall()
        if len(candidati) != 1:
            candidati = connessione.execute("""
                SELECT id, nome, ruolo, squadra FROM giocatori
                WHERE in_quotazioni_correnti=1
                  AND (nome_normalizzato LIKE ? OR ? LIKE nome_normalizzato)
            """, (nome_normale + "%", nome_normale)).fetchall()
        if len(candidati) != 1:
            problemi.append(f"{nome} ({codice}): abbinamento non univoco")
            continue
        if candidati[0][1] != nome or candidati[0][2] != ruolo or normalizza(candidati[0][3]) != normalizza(squadra):
            problemi.append(f"{nome} ({codice}): associato a {candidati[0][1]} ({candidati[0][3]}, {candidati[0][2]})")
        posizione += 1
        connessione.execute("INSERT INTO tag_asta VALUES (?, ?, ?, ?)",
                           (candidati[0][0], categoria or "Da assegnare", nota or "", posizione))
    connessione.executemany("INSERT INTO problemi_importazione VALUES ('fasce', ?)", ((x,) for x in problemi))
    connessione.commit()
    return posizione, problemi


class Suggerimento:
    def __init__(self, radice: Tk):
        self.radice = radice
        self.finestra: Toplevel | None = None
        self.testo = ""

    def mostra(self, evento, testo: str) -> None:
        self.mostra_coordinate(testo, evento.x_root + 14, evento.y_root + 14)

    def mostra_sotto(self, widget, testo: str) -> None:
        self.mostra_coordinate(
            testo,
            widget.winfo_rootx() + widget.winfo_width() // 2,
            widget.winfo_rooty() + widget.winfo_height() + 4,
            centrato=True,
        )

    def mostra_sotto_colonna(self, tabella, evento, testo: str) -> None:
        codice = tabella.identify_column(evento.x)
        indice = int(codice[1:]) - 1
        colonne = tabella["columns"]
        if indice < 0 or indice >= len(colonne):
            self.mostra(evento, testo)
            return
        larghezze = [int(tabella.column(colonna, "width")) for colonna in colonne]
        scorrimento = tabella.xview()[0] * sum(larghezze)
        centro = sum(larghezze[:indice]) + larghezze[indice] / 2 - scorrimento
        righe = tabella.get_children()
        riquadro_prima_riga = tabella.bbox(righe[0]) if righe else None
        sotto_intestazione = tabella.winfo_rooty() + (riquadro_prima_riga[1] if riquadro_prima_riga else evento.y + 22)
        self.mostra_coordinate(testo, int(tabella.winfo_rootx() + centro), sotto_intestazione + 3, centrato=True)

    def mostra_coordinate(self, testo: str, x: int, y: int, centrato: bool = False) -> None:
        if self.testo == testo and self.finestra:
            return
        self.nascondi()
        self.testo = testo
        self.finestra = Toplevel(self.radice)
        self.finestra.wm_overrideredirect(True)
        larghezza_schermo = self.radice.winfo_vrootwidth()
        altezza_schermo = self.radice.winfo_vrootheight()
        origine_x = self.radice.winfo_vrootx()
        origine_y = self.radice.winfo_vrooty()
        ttk.Label(
            self.finestra, text=testo, justify="left", padding=7, relief="solid", borderwidth=1,
            wraplength=max(180, min(380, larghezza_schermo - 40)),
        ).pack()
        self.finestra.update_idletasks()
        larghezza = self.finestra.winfo_reqwidth()
        altezza = self.finestra.winfo_reqheight()
        if centrato:
            x -= larghezza // 2
        if x + larghezza > origine_x + larghezza_schermo:
            x = origine_x + larghezza_schermo - larghezza
        x = max(origine_x, x)
        if y + altezza > origine_y + altezza_schermo:
            y = max(origine_y, y - altezza - 8)
        self.finestra.wm_geometry(f"+{x}+{y}")

    def nascondi(self) -> None:
        if self.finestra:
            self.finestra.destroy()
        self.finestra = None
        self.testo = ""


class Applicazione:
    def __init__(self, connessione: sqlite3.Connection):
        self.db = connessione
        self.radice = Tk()
        self.radice.title("Assistente Asta Fantacalcio 2026-27")
        self.radice.geometry("1300x760")
        self.radice.minsize(1050, 620)
        self.ricerca = StringVar()
        self.filtro_ruolo = StringVar(value="Tutti")
        self.filtro_squadra = StringVar(value="Tutte")
        self.filtro_fascia = StringVar(value="Tutte")
        self.filtro_stato = StringVar(value="Disponibili")
        self.filtro_preferenze = StringVar(value="Tutte")
        self.filtro_formazione_tipo = tk.BooleanVar(value=False)
        self.stato = StringVar()
        self.prezzo_live = StringVar()
        self.giocatore_live_id: int | None = None
        self.ordina = "nome"
        self.inverso = False
        self.colonne_statistiche = self.leggi_colonne_statistiche()
        self.confronto: list[int] = []
        self.rose_aperte = []
        self.suggerimento = Suggerimento(self.radice)
        self.crea_interfaccia()
        self.aggiorna_elenco()

    def crea_interfaccia(self) -> None:
        stile = ttk.Style(self.radice)
        stile.theme_use("clam")
        stile.configure("Titolo.TLabel", font=("Sans", 18, "bold"))
        stile.configure("Sottotitolo.TLabel", font=("Sans", 10), foreground="#475467")
        stile.configure("StatoSuccesso.TLabel", font=("Sans", 10, "bold"), foreground="#067647")
        stile.configure("Treeview", background="#ffffff", fieldbackground="#ffffff", foreground="#1d2939", rowheight=26, font=("Sans", 10))
        stile.configure("Treeview.Heading", background="#eaf2ff", foreground="#1d2939", font=("Sans", 10, "bold"), padding=(8, 6))
        stile.map("Treeview", background=[("selected", "#155eef")], foreground=[("selected", "#ffffff")])
        stile.configure("TNotebook.Tab", padding=(10, 6), font=("Sans", 10, "bold"))
        intestazione = ttk.Frame(self.radice, padding=(16, 12))
        intestazione.pack(fill="x")
        ttk.Label(intestazione, text="Assistente Asta Fantacalcio", style="Titolo.TLabel").pack(side="left")
        ttk.Label(intestazione, text="Classic · Serie A 2026-27 · offline").pack(side="left", padx=12)
        ttk.Button(intestazione, text="Colonne statistiche", command=self.apri_colonne_statistiche).pack(side="right", padx=8)
        ttk.Button(intestazione, text="Griglia portieri", command=self.apri_griglia_portieri).pack(side="right", padx=8)
        ttk.Button(intestazione, text="Formazioni tipo", command=self.apri_formazioni_tipo).pack(side="right", padx=8)
        ttk.Button(intestazione, text="Rose lega", command=self.apri_rose_lega).pack(side="right", padx=8)
        annulla = ttk.Button(intestazione, text="↶", width=3, command=self.annulla_ultima_operazione)
        annulla.pack(side="right", padx=4)
        annulla.bind("<Enter>", lambda _: self.suggerimento.mostra_sotto(annulla, "Annulla l'ultima operazione d'asta"))
        annulla.bind("<Leave>", lambda _: self.suggerimento.nascondi())

        filtri = ttk.Frame(self.radice, padding=(16, 0, 16, 8))
        filtri.pack(fill="x")
        ttk.Label(filtri, text="Cerca").pack(side="left")
        ricerca = ttk.Entry(filtri, textvariable=self.ricerca, width=28)
        ricerca.pack(side="left", padx=(6, 16))
        ricerca.bind("<KeyRelease>", lambda _: self.aggiorna_elenco())
        ttk.Label(filtri, text="Ruolo").pack(side="left")
        ruolo = ttk.Combobox(filtri, values=["Tutti", "P", "D", "C", "A"], textvariable=self.filtro_ruolo, width=8, state="readonly")
        ruolo.pack(side="left", padx=(6, 16)); ruolo.bind("<<ComboboxSelected>>", lambda _: self.aggiorna_elenco())
        ttk.Label(filtri, text="Squadra").pack(side="left")
        squadre = [riga[0] for riga in self.db.execute("SELECT DISTINCT squadra FROM giocatori WHERE in_quotazioni_correnti=1 ORDER BY squadra")]
        squadra = ttk.Combobox(filtri, values=["Tutte", *squadre], textvariable=self.filtro_squadra, width=14, state="readonly")
        squadra.pack(side="left", padx=(6, 16)); squadra.bind("<<ComboboxSelected>>", lambda _: self.aggiorna_elenco())
        ttk.Label(filtri, text="Fascia").pack(side="left")
        fascia = ttk.Combobox(filtri, values=["Tutte", *FASCE], textvariable=self.filtro_fascia, width=22, state="readonly")
        fascia.pack(side="left", padx=6); fascia.bind("<<ComboboxSelected>>", lambda _: self.aggiorna_elenco())
        ttk.Label(filtri, text="Stato").pack(side="left", padx=(10, 0))
        stato = ttk.Combobox(filtri, values=["Disponibili", "Tutti", "Miei", "Venduti"], textvariable=self.filtro_stato, width=13, state="readonly")
        stato.pack(side="left", padx=6); stato.bind("<<ComboboxSelected>>", lambda _: self.aggiorna_elenco())
        ttk.Label(filtri, text="Liste").pack(side="left", padx=(10, 0))
        preferenze = ttk.Combobox(filtri, values=["Tutte", "Preferiti", "Esclusi"], textvariable=self.filtro_preferenze, width=12, state="readonly")
        preferenze.pack(side="left", padx=6); preferenze.bind("<<ComboboxSelected>>", lambda _: self.aggiorna_elenco())
        ttk.Checkbutton(filtri, text="Solo formazione tipo", variable=self.filtro_formazione_tipo, command=self.aggiorna_elenco).pack(side="left", padx=(10, 0))

        corpo = ttk.Panedwindow(self.radice, orient="horizontal")
        corpo.pack(fill="both", expand=True, padx=16, pady=(0, 8))
        sinistra = ttk.Frame(corpo)
        contenitore_destra = ttk.Frame(corpo)
        tela_scheda = tk.Canvas(contenitore_destra, highlightthickness=0)
        barra_scheda = ttk.Scrollbar(contenitore_destra, orient="vertical", command=tela_scheda.yview)
        tela_scheda.configure(yscrollcommand=barra_scheda.set)
        tela_scheda.pack(side="left", fill="both", expand=True)
        barra_scheda.pack(side="right", fill="y")
        destra = ttk.Frame(tela_scheda, padding=(14, 0))
        finestra_scheda = tela_scheda.create_window((0, 0), window=destra, anchor="nw")
        destra.bind("<Configure>", lambda _: tela_scheda.configure(scrollregion=tela_scheda.bbox("all")))
        tela_scheda.bind("<Configure>", lambda evento: tela_scheda.itemconfigure(finestra_scheda, width=evento.width))

        def scorri_scheda(evento):
            if getattr(evento, "num", None) == 4:
                tela_scheda.yview_scroll(-1, "units")
            elif getattr(evento, "num", None) == 5:
                tela_scheda.yview_scroll(1, "units")
            else:
                tela_scheda.yview_scroll(int(-evento.delta / 120), "units")

        def attiva_scorrimento(_: object) -> None:
            tela_scheda.bind_all("<MouseWheel>", scorri_scheda)
            tela_scheda.bind_all("<Button-4>", scorri_scheda)
            tela_scheda.bind_all("<Button-5>", scorri_scheda)

        def disattiva_scorrimento(_: object) -> None:
            tela_scheda.unbind_all("<MouseWheel>")
            tela_scheda.unbind_all("<Button-4>")
            tela_scheda.unbind_all("<Button-5>")

        tela_scheda.bind("<Enter>", attiva_scorrimento)
        tela_scheda.bind("<Leave>", disattiva_scorrimento)
        corpo.add(sinistra, weight=3); corpo.add(contenitore_destra, weight=2)
        colonne = ("fascia", "segno", "stato", "nome", "ruolo", "squadra", *(codice for codice, _, _ in STATISTICHE_ELENCO))
        riquadro_tabella = ttk.Frame(sinistra)
        riquadro_tabella.pack(fill="both", expand=True)
        self.tabella = ttk.Treeview(riquadro_tabella, columns=colonne, show="headings", selectmode="browse")
        nomi = {"nome": "Calciatore", "ruolo": "Ruolo", "squadra": "Squadra", "fascia": "Fascia d'asta", "segno": "★", "stato": "Stato"} | {codice: titolo for codice, titolo, _ in STATISTICHE_ELENCO}
        larghezze = {"nome": 170, "ruolo": 58, "squadra": 92, "fascia": 170, "segno": 34, "stato": 105,
                     "fvm": 58, "qta": 68, "qti": 68, "pv": 50, "mv": 56, "fm": 56, "gf": 48,
                     "gs": 48, "ass": 54, "amm": 58, "esp": 54}
        for colonna in colonne:
            self.tabella.heading(colonna, text=nomi[colonna], command=lambda c=colonna: self.ordina_per(c))
            self.tabella.column(colonna, width=larghezze[colonna], anchor="w" if colonna in {"nome", "squadra", "fascia", "stato"} else "center")
        self.aggiorna_colonne_statistiche()
        barra = ttk.Scrollbar(riquadro_tabella, orient="vertical", command=self.tabella.yview)
        barra_orizzontale = ttk.Scrollbar(riquadro_tabella, orient="horizontal", command=self.tabella.xview)
        self.tabella.configure(yscrollcommand=barra.set, xscrollcommand=barra_orizzontale.set)
        self.tabella.grid(row=0, column=0, sticky="nsew"); barra.grid(row=0, column=1, sticky="ns")
        barra_orizzontale.grid(row=1, column=0, sticky="ew")
        riquadro_tabella.rowconfigure(0, weight=1); riquadro_tabella.columnconfigure(0, weight=1)
        self.tabella.bind("<<TreeviewSelect>>", self.mostra_giocatore)
        self.tabella.bind("<Motion>", self.mostra_glossario)
        self.tabella.bind("<Leave>", lambda _: self.suggerimento.nascondi())
        for fascia_nome, colore in COLORI_FASCE.items():
            self.tabella.tag_configure(fascia_nome, background=colore)
        self.tabella.tag_configure("non_disponibile", background="#e5e7eb", foreground="#667085")

        sezione_profilo = ttk.LabelFrame(destra, text="Profilo e lettura rapida", padding=(8, 6))
        sezione_prestazioni = ttk.LabelFrame(destra, text="Prestazioni e storico", padding=(8, 6))
        sezione_asta = ttk.LabelFrame(destra, text="Asta", padding=(8, 6))
        testata_scheda = ttk.Frame(sezione_profilo)
        testata_scheda.pack(fill="x")
        self.foto_scheda = ttk.Label(testata_scheda, anchor="center")
        self.foto_scheda.pack(side="left", padx=(0, 8))
        self.stemma_scheda = ttk.Label(testata_scheda, width=3, anchor="center")
        self.stemma_scheda.pack(side="left", padx=(0, 8))
        titoli_scheda = ttk.Frame(testata_scheda)
        titoli_scheda.pack(side="left", fill="x", expand=True)
        riga_nome = ttk.Frame(titoli_scheda)
        riga_nome.pack(fill="x")
        self.nome_scheda = ttk.Label(riga_nome, text="Seleziona un calciatore", style="Titolo.TLabel", wraplength=275)
        self.nome_scheda.pack(side="left", anchor="w")
        self.badge_fvm = tk.Label(riga_nome, text="FVM —", background="#eaf2ff", foreground="#175cd3", padx=6, pady=3, font=("Sans", 9, "bold"))
        self.badge_fvm.pack(side="right", padx=(4, 0))
        self.badge_qta = tk.Label(riga_nome, text="QtA —", background="#f2f4f7", foreground="#344054", padx=6, pady=3, font=("Sans", 9, "bold"))
        self.badge_qta.pack(side="right")
        self.profilo_scheda = ttk.Label(titoli_scheda, text="", style="Sottotitolo.TLabel")
        self.profilo_scheda.pack(anchor="w", pady=(2, 0))
        riga_anagrafica = ttk.Frame(titoli_scheda)
        riga_anagrafica.pack(anchor="w", pady=(1, 0))
        self.anagrafica_scheda = ttk.Label(riga_anagrafica, text="", style="Sottotitolo.TLabel")
        self.anagrafica_scheda.pack(side="left")
        self.bandiera_scheda = ttk.Label(riga_anagrafica, text="")
        self.bandiera_scheda.pack(side="left", padx=(5, 0))
        self.eta_scheda = ttk.Label(riga_anagrafica, text="", style="Sottotitolo.TLabel")
        self.eta_scheda.pack(side="left")
        riquadro_fascia = ttk.Frame(testata_scheda)
        riquadro_fascia.pack(side="right", anchor="n")
        self.badge_fascia = tk.Label(riquadro_fascia, text="Fascia non assegnata", background=COLORI_FASCE["Da assegnare"], foreground="#1d2939", padx=8, pady=5, font=("Sans", 9, "bold"))
        self.badge_fascia.pack()
        ttk.Button(riquadro_fascia, text="Modifica fascia", command=self.modifica_fascia).pack(fill="x", pady=(4, 0))
        sintesi = ttk.LabelFrame(sezione_profilo, text="Sintesi", padding=(8, 6))
        sintesi.pack(fill="x", pady=(8, 6))
        self.pro_asta = ttk.Label(sintesi, text="✓ Pro: —", style="Sottotitolo.TLabel", wraplength=450)
        self.pro_asta.grid(row=0, column=0, columnspan=5, sticky="w")
        self.contro_asta = ttk.Label(sintesi, text="⚠ Contro: —", style="Sottotitolo.TLabel", wraplength=450)
        self.contro_asta.grid(row=1, column=0, columnspan=5, sticky="w", pady=(2, 5))
        self.indici_asta = ttk.Label(sintesi, text="Profilo: —", style="Sottotitolo.TLabel", wraplength=450)
        self.indici_asta.grid(row=2, column=0, columnspan=5, sticky="w", pady=(0, 5))
        ttk.Separator(sintesi).grid(row=3, column=0, columnspan=5, sticky="ew", pady=(0, 5))
        ttk.Label(sintesi, text="Statistiche chiave 2026-27", font=("Sans", 9, "bold")).grid(row=4, column=0, columnspan=5, sticky="w", pady=(0, 3))
        self.valori_chiave = []
        for indice in range(5):
            riquadro_valore = tk.Frame(sintesi, background="#f8fafc", highlightbackground="#d0d5dd", highlightthickness=1)
            riquadro_valore.grid(row=5, column=indice, sticky="nsew", padx=2)
            etichetta = tk.Label(riquadro_valore, text="—", background="#f8fafc", foreground="#475467", font=("Sans", 8, "bold"), justify="center", wraplength=82)
            etichetta.pack(fill="x", padx=4, pady=(4, 0))
            valore_sintesi = tk.Label(riquadro_valore, text="—", background="#f8fafc", foreground="#101828", font=("Sans", 14, "bold"))
            valore_sintesi.pack(fill="x", padx=4, pady=(0, 4))
            self.valori_chiave.append((etichetta, valore_sintesi))
            sintesi.columnconfigure(indice, weight=1)
        self.titolo_storico = ttk.Label(sintesi, text="Media delle stagioni precedenti", font=("Sans", 9, "bold"))
        self.titolo_storico.grid(row=6, column=0, columnspan=5, sticky="w", pady=(6, 3))
        self.valori_storici = []
        for indice in range(5):
            riquadro_valore = tk.Frame(sintesi, background="#f8fafc", highlightbackground="#d0d5dd", highlightthickness=1)
            riquadro_valore.grid(row=7, column=indice, sticky="nsew", padx=2)
            etichetta = tk.Label(riquadro_valore, text="—", background="#f8fafc", foreground="#475467", font=("Sans", 8, "bold"), justify="center", wraplength=82)
            etichetta.pack(fill="x", padx=4, pady=(4, 0))
            valore_sintesi = tk.Label(riquadro_valore, text="—", background="#f8fafc", foreground="#101828", font=("Sans", 12, "bold"))
            valore_sintesi.pack(fill="x", padx=4, pady=(0, 4))
            self.valori_storici.append((etichetta, valore_sintesi))
        contesto = ttk.LabelFrame(sezione_profilo, text="Contesto squadra", padding=(6, 5))
        contesto.pack(fill="x", pady=(0, 6))
        self.titolo_contesto_squadra = ttk.Label(contesto, text="Squadra: —", font=("Sans", 9, "bold"))
        self.titolo_contesto_squadra.pack(anchor="w")
        self.metriche_contesto_squadra = []
        riga_metriche_squadra = ttk.Frame(contesto)
        riga_metriche_squadra.pack(fill="x", pady=(4, 2))
        for indice in range(4):
            riquadro = tk.Frame(riga_metriche_squadra, background="#f8fafc", highlightbackground="#d0d5dd", highlightthickness=1)
            riquadro.grid(row=0, column=indice, sticky="nsew", padx=2)
            etichetta = tk.Label(riquadro, text="—", background="#f8fafc", foreground="#475467", font=("Sans", 8, "bold"), wraplength=90)
            etichetta.pack(fill="x", padx=3, pady=(3, 0))
            valore_squadra = tk.Label(riquadro, text="—", background="#f8fafc", foreground="#101828", font=("Sans", 11, "bold"))
            valore_squadra.pack(fill="x", padx=3, pady=(0, 3))
            self.metriche_contesto_squadra.append((etichetta, valore_squadra))
            riga_metriche_squadra.columnconfigure(indice, weight=1)
        riga_storico_squadra = ttk.Frame(contesto)
        riga_storico_squadra.pack(fill="x")
        self.storico_contesto_squadra = ttk.Label(riga_storico_squadra, text="Storico Serie A: —", style="Sottotitolo.TLabel", wraplength=350)
        self.storico_contesto_squadra.pack(side="left", fill="x", expand=True)
        ttk.Button(riga_storico_squadra, text="Dettaglio squadra", command=self.apri_dettaglio_squadra).pack(side="right", padx=(6, 0))
        self.commento_contesto_squadra = ttk.Label(contesto, text="", style="Sottotitolo.TLabel", justify="left", wraplength=470)
        self.commento_contesto_squadra.pack(fill="x", pady=(4, 0))

        asta_live = ttk.LabelFrame(sezione_asta, text="Asta live", padding=(8, 6))
        asta_live.pack(fill="x", pady=(0, 6))
        riga_prezzo = ttk.Frame(asta_live)
        riga_prezzo.pack(fill="x")
        ttk.Label(riga_prezzo, text="Prezzo attuale").pack(side="left")
        campo_prezzo = ttk.Entry(riga_prezzo, textvariable=self.prezzo_live, width=8, justify="center")
        campo_prezzo.pack(side="left", padx=(6, 12))
        campo_prezzo.bind("<KeyRelease>", lambda _: self.aggiorna_asta_live())
        self.rilancio_live = ttk.Label(riga_prezzo, text="Prossimo rilancio: —", font=("Sans", 10, "bold"))
        self.rilancio_live.pack(side="left")
        self.tetti_live = ttk.Label(asta_live, text="QtA: — · Massimo sostenibile: —", style="Sottotitolo.TLabel")
        self.tetti_live.pack(anchor="w", pady=(4, 0))

        piano_b = ttk.LabelFrame(sezione_asta, text="Piano B · alternative disponibili", padding=(6, 4))
        piano_b.pack(fill="x", pady=(0, 6))
        self.titolo_piano_b = ttk.Label(piano_b, text="Seleziona un calciatore", style="Sottotitolo.TLabel")
        self.titolo_piano_b.pack(anchor="w", pady=(0, 4))
        colonne_piano_b = ("nome", "fascia", "qta", "fvm", "fm")
        self.piano_b = ttk.Treeview(piano_b, columns=colonne_piano_b, show="headings", height=5, selectmode="browse")
        for codice, titolo, larghezza in (("nome", "Calciatore", 155), ("fascia", "Fascia", 125), ("qta", "QtA", 48), ("fvm", "FVM", 48), ("fm", "FM", 48)):
            self.piano_b.heading(codice, text=titolo)
            self.piano_b.column(codice, width=larghezza, anchor="w" if codice in {"nome", "fascia"} else "center")
        self.piano_b.pack(fill="x")
        self.piano_b.bind("<<TreeviewSelect>>", self.apri_piano_b)

        self.dettaglio = ttk.Label(sezione_prestazioni, text="", justify="left", wraplength=480)
        self.dettaglio.pack(fill="x", pady=(8, 6), anchor="w")
        ttk.Label(sezione_prestazioni, text="Andamento MV e FM per stagione").pack(anchor="w")
        self.grafico = tk.Canvas(sezione_prestazioni, height=180, highlightthickness=0, background="#ffffff")
        self.grafico.pack(fill="both", expand=True, pady=(2, 6))
        self.grafico.bind("<Configure>", self.ridimensiona_grafico)
        self.notebook_statistiche = ttk.Notebook(sezione_prestazioni)
        self.notebook_statistiche.pack(fill="both", expand=True, pady=(0, 8))
        riquadro_timeline = ttk.Frame(self.notebook_statistiche)
        self.notebook_statistiche.add(riquadro_timeline, text="Classic")
        colonne_timeline = ("stagione", "squadra", "pv", "mv", "fm", "gf", "ass", "amm", "esp", "qta", "fvm")
        self.timeline = ttk.Treeview(riquadro_timeline, columns=colonne_timeline, show="headings", height=10)
        titoli_timeline = {"stagione": "Stagione", "squadra": "Squadra", "pv": "PV", "mv": "MV", "fm": "FM", "gf": "Gol", "ass": "Assist", "amm": "Amm.", "esp": "Esp.", "qta": "Qt.A", "fvm": "FVM"}
        for colonna in colonne_timeline:
            if colonna in {"stagione", "squadra"}:
                self.timeline.heading(colonna, text=titoli_timeline[colonna])
            else:
                self.timeline.heading(colonna, text=titoli_timeline[colonna], command=lambda c=colonna: self.apri_plot_fanta(c))
            self.timeline.column(colonna, width=62 if colonna not in {"stagione", "squadra"} else 80, anchor="center")
        barra_timeline = ttk.Scrollbar(riquadro_timeline, orient="vertical", command=self.timeline.yview)
        barra_timeline_orizzontale = ttk.Scrollbar(riquadro_timeline, orient="horizontal", command=self.timeline.xview)
        self.timeline.configure(yscrollcommand=barra_timeline.set, xscrollcommand=barra_timeline_orizzontale.set)
        self.timeline.pack(side="left", fill="both", expand=True); barra_timeline.pack(side="right", fill="y")
        barra_timeline_orizzontale.pack(side="bottom", fill="x")
        self.timeline.bind("<Motion>", self.mostra_glossario_timeline)
        self.timeline.bind("<Leave>", lambda _: self.suggerimento.nascondi())
        self.timeline.tag_configure("riga_pari", background="#f7f9fc")
        self.tabelle_fbref = {}
        etichette = {"standard_stats": "Prestazioni", "shooting_stats": "Tiro", "time": "Impiego", "misc": "Disciplina e difesa", "goalkeeping": "Portieri"}
        for fonte in FONTI_FBREF:
            scheda = ttk.Frame(self.notebook_statistiche)
            self.notebook_statistiche.add(scheda, text=etichette[fonte])
            tabella = ttk.Treeview(scheda, show="headings", height=10)
            barra_verticale = ttk.Scrollbar(scheda, orient="vertical", command=tabella.yview)
            barra_orizzontale = ttk.Scrollbar(scheda, orient="horizontal", command=tabella.xview)
            tabella.configure(yscrollcommand=barra_verticale.set, xscrollcommand=barra_orizzontale.set)
            tabella.grid(row=0, column=0, sticky="nsew")
            barra_verticale.grid(row=0, column=1, sticky="ns"); barra_orizzontale.grid(row=1, column=0, sticky="ew")
            scheda.rowconfigure(0, weight=1); scheda.columnconfigure(0, weight=1)
            tabella.bind("<Motion>", lambda evento, tabella=tabella: self.mostra_glossario_fbref(evento, tabella))
            tabella.bind("<Leave>", lambda _: self.suggerimento.nascondi())
            self.tabelle_fbref[fonte] = tabella
        azioni = ttk.Frame(sezione_asta)
        azioni.pack(fill="x")
        ttk.Button(azioni, text="Registra acquisto", command=self.registra_acquisto).pack(side="left")
        ttk.Button(azioni, text="Rimuovi esito", command=self.rimuovi_acquisto).pack(side="left", padx=6)
        azioni_preferenze = ttk.Frame(sezione_asta)
        azioni_preferenze.pack(fill="x", pady=(6, 0))
        self.pulsante_preferito = ttk.Button(azioni_preferenze, text="★ Preferito", command=self.alterna_preferito)
        self.pulsante_preferito.pack(side="left")
        self.pulsante_escluso = ttk.Button(azioni_preferenze, text="Escludi", command=self.alterna_escluso)
        self.pulsante_escluso.pack(side="left", padx=6)
        ttk.Button(azioni_preferenze, text="Nota personale", command=self.modifica_nota).pack(side="left")
        self.nota_asta = ttk.Label(sezione_asta, text="Nessuna nota personale.", style="Sottotitolo.TLabel", wraplength=450)
        self.nota_asta.pack(fill="x", pady=(5, 0))
        azioni_confronto = ttk.Frame(sezione_prestazioni)
        azioni_confronto.pack(fill="x", pady=(6, 0))
        ttk.Button(azioni_confronto, text="Aggiungi al confronto", command=self.aggiungi_confronto).pack(side="left")
        self.pulsante_confronto = ttk.Button(azioni_confronto, text="Confronto (0/3)", command=self.apri_confronto)
        self.pulsante_confronto.pack(side="left", padx=6)
        ttk.Button(azioni_confronto, text="Svuota", command=self.svuota_confronto).pack(side="left")
        azioni.pack_configure(before=piano_b)
        azioni_preferenze.pack_configure(before=piano_b)
        self.nota_asta.pack_configure(before=piano_b)
        azioni_confronto.pack_configure(before=self.notebook_statistiche)
        self.aggiornamento_scheda = ttk.Label(sezione_profilo, text="", style="Sottotitolo.TLabel")
        self.aggiornamento_scheda.pack(anchor="e", pady=(8, 0))
        sezione_profilo.pack(fill="x", pady=(0, 8))
        sezione_prestazioni.pack(fill="both", expand=True, pady=(0, 8))
        sezione_asta.pack(fill="x", pady=(0, 8))
        self.rendi_richiudibile(sezione_prestazioni, "Prestazioni")
        self.rendi_richiudibile(sezione_asta, "Asta")

        basso = ttk.Frame(self.radice, padding=(16, 4, 16, 12)); basso.pack(fill="x")
        self.riepilogo_budget = ttk.Label(basso, text="")
        self.riepilogo_budget.pack(side="left")
        self.riepilogo_ruoli = {}
        for ruolo in ROSA:
            etichetta = ttk.Label(basso, text="", style="Sottotitolo.TLabel")
            etichetta.pack(side="left", padx=(10, 0))
            self.riepilogo_ruoli[ruolo] = etichetta
        ttk.Label(basso, text="Dati presi da Fantacalcio, FBRef e API-Football", style="Sottotitolo.TLabel").pack(side="right")
        self.etichetta_stato = ttk.Label(basso, textvariable=self.stato)
        self.etichetta_stato.pack(side="right", padx=(0, 16))
        self.aggiorna_budget()

    def rendi_richiudibile(self, sezione, titolo: str) -> None:
        stato = {"layout": None}
        pulsante = ttk.Button(sezione, text=f"Comprimi {titolo} ▴", width=19)

        def alterna() -> None:
            if stato["layout"] is None:
                stato["layout"] = []
                for elemento in sezione.pack_slaves():
                    if elemento is pulsante:
                        continue
                    opzioni = elemento.pack_info()
                    opzioni.pop("in", None)
                    stato["layout"].append((elemento, opzioni))
                for elemento, _ in stato["layout"]:
                    elemento.pack_forget()
                pulsante.configure(text=f"Mostra {titolo} ▾")
            else:
                pulsante.pack_forget()
                layout = stato["layout"]
                for elemento, opzioni in layout:
                    elemento.pack(**opzioni)
                stato["layout"] = None
                pulsante.configure(text=f"Comprimi {titolo} ▴")
                pulsante.pack(anchor="e", before=layout[0][0], pady=(0, 4))

        pulsante.configure(command=alterna)
        primi = sezione.pack_slaves()
        pulsante.pack(anchor="e", before=primi[0] if primi else None, pady=(0, 4))

    def mostra_feedback(self, testo: str) -> None:
        if getattr(self, "feedback_timer", None):
            self.radice.after_cancel(self.feedback_timer)
        self.stato.set(f"✓ {testo}")
        self.etichetta_stato.configure(style="StatoSuccesso.TLabel")

        def ripristina() -> None:
            self.etichetta_stato.configure(style="TLabel")
            self.stato.set(f"{len(self.tabella.get_children())} giocatori visualizzati")
            self.feedback_timer = None

        self.feedback_timer = self.radice.after(3500, ripristina)

    def abilita_rotellina(self, tela, consenti_orizzontale: bool = False, contenuto=None) -> None:
        """Collega la rotellina al canvas attivo, anche su Linux con Button-4 e Button-5."""
        def scorri(evento) -> None:
            if getattr(evento, "num", None) == 4:
                direzione = -1
            elif getattr(evento, "num", None) == 5:
                direzione = 1
            else:
                direzione = int(-evento.delta / 120) or (-1 if evento.delta > 0 else 1)
            if consenti_orizzontale and (getattr(evento, "state", 0) & 1):
                tela.xview_scroll(direzione, "units")
            else:
                tela.yview_scroll(direzione, "units")

        def attiva(_evento=None) -> None:
            tela.bind_all("<MouseWheel>", scorri)
            tela.bind_all("<Button-4>", scorri)
            tela.bind_all("<Button-5>", scorri)

        def disattiva(_evento=None) -> None:
            tela.unbind_all("<MouseWheel>")
            tela.unbind_all("<Button-4>")
            tela.unbind_all("<Button-5>")

        for widget in (tela, contenuto):
            if widget is not None:
                widget.bind("<Enter>", attiva, add="+")
                widget.bind("<Leave>", disattiva, add="+")

    def query_giocatori(self):
        clausole = ["g.in_quotazioni_correnti=1"]
        parametri: list[str] = []
        if self.ricerca.get().strip():
            clausole.append("g.nome_normalizzato LIKE ?")
            parametri.append("%" + normalizza(self.ricerca.get()) + "%")
        if self.filtro_ruolo.get() != "Tutti":
            clausole.append("g.ruolo=?"); parametri.append(self.filtro_ruolo.get())
        if self.filtro_squadra.get() != "Tutte":
            clausole.append("g.squadra=?"); parametri.append(self.filtro_squadra.get())
        if self.filtro_fascia.get() != "Tutte":
            clausole.append("EXISTS (SELECT 1 FROM tag_asta t WHERE t.giocatore_id=g.id AND t.categoria=?)")
            parametri.append(self.filtro_fascia.get())
        if self.filtro_stato.get() == "Disponibili":
            clausole.append("a.giocatore_id IS NULL")
        elif self.filtro_stato.get() == "Miei":
            clausole.append("m.e_mio=1")
        elif self.filtro_stato.get() == "Venduti":
            clausole.append("m.e_mio=0")
        if self.filtro_preferenze.get() == "Preferiti":
            clausole.append("coalesce(p.preferito, 0)=1")
        elif self.filtro_preferenze.get() == "Esclusi":
            clausole.append("coalesce(p.escluso, 0)=1")
        if self.filtro_formazione_tipo.get():
            clausole.append("EXISTS (SELECT 1 FROM indicazioni_formazione i WHERE i.giocatore_id=g.id AND (i.titolare=1 OR i.ballottaggio<>''))")
        ordine_fasce_sql = "CASE coalesce(t.fascia_principale, 'Da assegnare') " + " ".join(
            f"WHEN '{fascia}' THEN {indice}" for fascia, indice in ORDINE_FASCE.items()) + " ELSE 99 END"
        ordine_statistiche = {codice: campo for codice, _, campo in STATISTICHE_ELENCO}
        ordinamenti = {"nome": "g.nome", "ruolo": "g.ruolo, g.nome", "squadra": "g.squadra, g.nome", "fascia": ordine_fasce_sql, "segno": "p.preferito DESC, p.escluso", "stato": "m.nome, a.prezzo"} | ordine_statistiche
        ordine = ordinamenti[self.ordina]
        verso = "DESC" if self.inverso else "ASC"
        return self.db.execute(f"""
            SELECT g.id, g.nome, g.ruolo, g.squadra, coalesce(t.categorie, ''), coalesce(p.preferito, 0), coalesce(p.escluso, 0),
                   m.nome, m.e_mio, a.prezzo, q.fvm, q.quotazione_attuale, q.quotazione_iniziale,
                   s.presenze, s.mv, s.fm, s.gol_fatti, s.gol_subiti, s.assist, s.ammonizioni, s.espulsioni
            FROM giocatori g
            LEFT JOIN quotazioni_fanta q ON q.giocatore_id=g.id AND q.stagione='2026-27'
            LEFT JOIN statistiche_fanta s ON s.giocatore_id=g.id AND s.stagione='2026-27'
            LEFT JOIN acquisti_lega a ON a.giocatore_id=g.id
            LEFT JOIN fantallenatori m ON m.id=a.fantallenatore_id
            LEFT JOIN preferenze_giocatori p ON p.giocatore_id=g.id
            LEFT JOIN (
                SELECT t1.giocatore_id,
                       GROUP_CONCAT(t1.categoria, ' · ') AS categorie,
                       (SELECT t2.categoria FROM tag_asta t2 WHERE t2.giocatore_id=t1.giocatore_id ORDER BY t2.posizione LIMIT 1) AS fascia_principale
                FROM (SELECT giocatore_id, categoria, posizione FROM tag_asta ORDER BY posizione) t1
                GROUP BY t1.giocatore_id
            ) t ON t.giocatore_id=g.id
            WHERE {' AND '.join(clausole)}
            ORDER BY {ordine} {verso}, g.nome
        """, parametri).fetchall()

    def leggi_colonne_statistiche(self) -> list[str]:
        disponibili = [codice for codice, _, _ in STATISTICHE_ELENCO]
        riga = self.db.execute("SELECT valore FROM impostazioni WHERE chiave='colonne_statistiche_elenco'").fetchone()
        try:
            scelte = json.loads(riga[0]) if riga else ["fvm", "qta"]
        except (TypeError, json.JSONDecodeError):
            scelte = ["fvm", "qta"]
        return [codice for codice in disponibili if codice in scelte]

    def aggiorna_colonne_statistiche(self) -> None:
        fisse = ("fascia", "segno", "stato", "nome", "ruolo", "squadra")
        self.tabella.configure(displaycolumns=(*fisse, *self.colonne_statistiche))

    def apri_colonne_statistiche(self) -> None:
        finestra = Toplevel(self.radice)
        finestra.title("Colonne statistiche")
        finestra.transient(self.radice)
        ttk.Label(finestra, text="Statistiche da mostrare nell'elenco", style="Titolo.TLabel", padding=(16, 16, 16, 4)).pack(anchor="w")
        ttk.Label(finestra, text="Le colonne fisse restano sempre visibili.", style="Sottotitolo.TLabel", padding=(16, 0, 16, 10)).pack(anchor="w")
        opzioni = ttk.Frame(finestra, padding=(16, 0, 16, 8))
        opzioni.pack(fill="both", expand=True)
        variabili = {codice: tk.BooleanVar(value=codice in self.colonne_statistiche) for codice, _, _ in STATISTICHE_ELENCO}
        for indice, (codice, titolo, _) in enumerate(STATISTICHE_ELENCO):
            ttk.Checkbutton(opzioni, text=titolo.replace(" ⓘ", ""), variable=variabili[codice]).grid(row=indice // 2, column=indice % 2, sticky="w", padx=(0, 30), pady=3)

        def applica() -> None:
            self.colonne_statistiche = [codice for codice, _, _ in STATISTICHE_ELENCO if variabili[codice].get()]
            self.db.execute("""
                INSERT INTO impostazioni(chiave, valore) VALUES ('colonne_statistiche_elenco', ?)
                ON CONFLICT(chiave) DO UPDATE SET valore=excluded.valore
            """, (json.dumps(self.colonne_statistiche),))
            self.db.commit()
            self.aggiorna_colonne_statistiche()
            self.aggiorna_elenco()
            finestra.destroy()

        def ripristina() -> None:
            for codice, variabile in variabili.items():
                variabile.set(codice in {"fvm", "qta"})

        azioni = ttk.Frame(finestra, padding=(16, 4, 16, 16))
        azioni.pack(fill="x")
        ttk.Button(azioni, text="Ripristina predefinite", command=ripristina).pack(side="left")
        ttk.Button(azioni, text="Applica", command=applica).pack(side="right")

    @staticmethod
    def formato(n: float | None) -> str:
        if n is None:
            return "—"
        valore = Decimal(str(n)).quantize(Decimal("0.01"), rounding=ROUND_DOWN)
        testo = format(valore, "f").rstrip("0").rstrip(".")
        return ("0" if testo in {"", "-0"} else testo).replace(".", ",")

    @staticmethod
    def formato_data(valore: str | None) -> str:
        if not valore:
            return "—"
        try:
            return datetime.fromisoformat(valore).strftime("%d/%m/%Y alle %H:%M")
        except ValueError:
            return valore

    @staticmethod
    def asse_intero(nome: str, valori: list[float]) -> bool:
        descrizione = nome.lower()
        decimali = ("media", "fantamedia", "%", "/90", "per ", "precisione", "gol per ",
                    "punti per ", "impatto", "equivalenti (90')")
        return not any(indizio in descrizione for indizio in decimali) and all(float(valore).is_integer() for valore in valori)

    @staticmethod
    def passo_gradevole(obiettivo: float, intero: bool) -> float:
        if obiettivo <= 0:
            return 1.0
        potenza = 10 ** floor(log10(obiettivo))
        candidati = (1, 2, 5, 10)
        passo = next(fattore * potenza for fattore in candidati if fattore * potenza >= obiettivo)
        if intero:
            return float(max(1, ceil(passo)))
        return max(.01, passo)

    def tacche_asse(self, nome: str, valori: list[float]) -> tuple[float, float, list[float], bool]:
        intero = self.asse_intero(nome, valori)
        minimo, massimo = min(valori), max(valori)
        if intero:
            basso = max(0, floor(minimo) - 1)
            alto = ceil(massimo) + 1
        elif minimo == massimo:
            margine = max(abs(minimo) * .08, .05)
            basso, alto = minimo - margine, massimo + margine
        else:
            basso, alto = minimo, massimo
        passo = self.passo_gradevole((alto - basso) / 4, intero)
        basso = floor(basso / passo) * passo
        alto = ceil(alto / passo) * passo
        descrizione = nome.lower()
        puo_essere_negativa = any(indizio in descrizione for indizio in ("differenza", "impatto", "on-off"))
        if minimo >= 0 and not puo_essere_negativa:
            basso = max(0, basso)
        if basso == minimo and (not intero or basso > 0):
            basso -= passo
            if minimo >= 0 and not puo_essere_negativa:
                basso = max(0, basso)
        if alto == massimo:
            alto += passo
        if alto <= basso:
            alto = basso + passo
        tacche = []
        valore = basso
        while valore <= alto + passo / 1000:
            tacche.append(float(round(valore)) if intero else valore)
            valore += passo
        return basso, alto, tacche, intero

    def formato_massimo(self, valore: float | None, massimo: float | None) -> str:
        testo = self.formato(valore)
        return testo.translate(NUMERI_GRASSETTO) if valore is not None and valore == massimo else testo

    def aggiorna_sintesi_asta(self, giocatore_id: int, ruolo: str, squadra: str, tag, corrente, gol_subiti: float | None, medie: dict[str, float | None], storico) -> None:
        fascia = tag[0][0] if tag else "Da assegnare"
        colore = COLORI_FASCE.get(fascia, COLORI_FASCE["Da assegnare"])
        self.badge_fascia.configure(text=fascia, background=colore)
        if corrente is None:
            valori = {"PV": None, "MV": None, "FM": None, "Gol": None, "Assist": None, "FVM": None, "G+A": None}
        else:
            bonus = None if corrente[5] is None and corrente[6] is None else (corrente[5] or 0) + (corrente[6] or 0)
            valori = {"PV": corrente[2], "MV": corrente[3], "FM": corrente[4], "Gol": corrente[5],
                      "Assist": corrente[6], "FVM": corrente[10], "G+A": bonus}
        metriche_per_ruolo = {
            "P": [("PV", "Presenze a voto"), ("MV", "Media voto"), ("FM", "Fantamedia"), ("GS", "Gol subiti"), ("FVM", "FVM")],
            "D": [("PV", "Presenze a voto"), ("MV", "Media voto"), ("FM", "Fantamedia"), ("G+A", "Gol + assist"), ("FVM", "FVM")],
            "C": [("PV", "Presenze a voto"), ("MV", "Media voto"), ("FM", "Fantamedia"), ("G+A", "Gol + assist"), ("FVM", "FVM")],
            "A": [("PV", "Presenze a voto"), ("FM", "Fantamedia"), ("Gol", "Gol"), ("Assist", "Assist"), ("FVM", "FVM")],
        }
        metriche = metriche_per_ruolo.get(ruolo, [])
        for carte, fonte in ((self.valori_chiave, valori), (self.valori_storici, medie)):
            for (etichetta, valore_sintesi), (codice, nome) in zip(carte, metriche):
                valore = gol_subiti if codice == "GS" and fonte is valori else fonte[codice]
                spiegazione = GLOSSARIO.get(codice.lower(), f"{nome} — valore riferito alla stagione indicata.")
                etichetta.configure(text=nome)
                etichetta.bind("<Enter>", lambda evento, testo=spiegazione, widget=etichetta: self.suggerimento.mostra_sotto(widget, testo))
                etichetta.bind("<Leave>", lambda _: self.suggerimento.nascondi())
                valore_sintesi.configure(text=self.formato(valore))
        stagioni_storiche = len(storico)
        self.titolo_storico.configure(text=f"Media delle {stagioni_storiche} stagioni precedenti" if stagioni_storiche else "Nessuna stagione precedente")
        def media_ponderata(valori: list[float | None]) -> float | None:
            valori = [valore for valore in valori[:3] if valore is not None]
            if not valori:
                return None
            pesi = (.5, .3, .2)[:len(valori)]
            return sum(valore * peso for valore, peso in zip(valori, pesi)) / sum(pesi)

        def scala(valore: float | None, minimo: float, massimo: float) -> float:
            if valore is None:
                return 50.0
            return max(0.0, min(100.0, (valore - minimo) * 100 / (massimo - minimo)))

        righe = [riga for riga in list(reversed(storico))[:5] if riga[0] is not None and riga[0] >= 10]
        pv, mv, fm = (media_ponderata([riga[indice] for riga in righe]) for indice in (0, 1, 2))
        gol = media_ponderata([riga[3] for riga in righe])
        assist = media_ponderata([riga[5] for riga in righe])
        bonus = None if gol is None and assist is None else (gol or 0) + (assist or 0)
        soglia_bonus = {"P": 0, "D": 4, "C": 7, "A": 11}.get(ruolo, 6)
        affidabilita_storica = scala(pv, 10, 30) * .55 + scala(mv, 5.55, 6.35) * .45
        bonus_storico = scala(fm, 5.5, 6.4) if ruolo == "P" else scala(bonus, max(0, soglia_bonus - 6), soglia_bonus + 5) * .7 + scala(fm, 5.7, 7.1) * .3
        corrente_valida = corrente is not None and (corrente[2] or 0) >= 10
        affidabilita_corrente = (scala(corrente[2], 10, 30) * .55 + scala(corrente[3], 5.55, 6.35) * .45) if corrente_valida else None
        bonus_corrente = (scala(corrente[4], 5.5, 6.4) if ruolo == "P" else scala((corrente[5] or 0) + (corrente[6] or 0), max(0, soglia_bonus - 6), soglia_bonus + 5) * .7 + scala(corrente[4], 5.7, 7.1) * .3) if corrente_valida else None

        indicazione = self.db.execute("SELECT titolare, ballottaggio, fuori_ruolo, ballottaggio_vantaggio, ballottaggio_svantaggio FROM indicazioni_formazione WHERE giocatore_id=?", (giocatore_id,)).fetchone()
        titolare = bool(indicazione and indicazione[0])
        ballottaggio = bool(indicazione and indicazione[1])
        fuori_ruolo = indicazione[2] if indicazione else None
        gerarchia = 85.0 if titolare and not ballottaggio else (55.0 if titolare else (38.0 if ballottaggio else 50.0))
        piazzati = self.db.execute("SELECT tipo, priorita FROM specialisti_piazzati WHERE giocatore_id=? ORDER BY priorita, tipo", (giocatore_id,)).fetchall()
        primo_piazzato = next((tipo for tipo, priorita in piazzati if priorita == 1), None)
        if primo_piazzato:
            gerarchia = min(100.0, gerarchia + 10)

        stagioni_squadra = [(stagione, fonti) for stagione, fonti in self.righe_squadra_fbref(squadra) if stagione < "2026-27"][:5]
        def media_squadra(fonte: str, codice: str) -> float | None:
            dati = [self.valore_metrica_squadra(fonti, fonte, codice) for _, fonti in stagioni_squadra]
            dati = [dato for dato in dati if dato is not None]
            return sum(dati) / len(dati) if dati else None
        ga90, clean_sheet = media_squadra("goalkeeping", "GA90#1"), media_squadra("goalkeeping", "CS%#1")
        gol90, tiri90 = media_squadra("standard_stats", "Gls#2"), media_squadra("shooting_stats", "Sh/90#1")
        contesto = (scala(clean_sheet, 20, 38) * .55 + (100 - scala(ga90, .85, 1.65)) * .45) if ruolo in {"P", "D"} else (scala(gol90, 1.05, 1.7) * .6 + scala(tiri90, 8, 14) * .4)
        if not stagioni_squadra:
            contesto = 50.0
        def combina(storico_indice: float, corrente_indice: float | None) -> int:
            peso_storico = .7 if corrente_indice is None else .55
            return round(peso_storico * storico_indice + (.15 * corrente_indice if corrente_indice is not None else 0) + .2 * contesto + .1 * gerarchia)
        affidabilita = combina(affidabilita_storica, affidabilita_corrente)
        indice_bonus = combina(bonus_storico, bonus_corrente)
        rischio = round(max(0, min(100, 100 - (.55 * affidabilita_storica + .2 * contesto + .1 * gerarchia + (.15 * affidabilita_corrente if affidabilita_corrente is not None else .15 * affidabilita_storica)))))
        if ballottaggio:
            rischio = min(100, rischio + 15)
        if len(righe) < 2:
            rischio = min(100, rischio + 12)
        self.indici_asta.configure(text=f"Profilo · Affidabilità {affidabilita}/100 · Bonus {indice_bonus}/100 · Contesto {round(contesto)}/100 · Rischio {rischio}/100")

        pro: list[tuple[int, str]] = []
        contro: list[tuple[int, str]] = []
        if pv is not None and pv >= 25:
            pro.append((affidabilita, f"Sempre a voto: {self.formato(pv)} PV medie nelle ultime stagioni."))
        if mv is not None and len(righe) >= 2:
            sufficienti = sum(riga[1] is not None and riga[1] >= 6 for riga in righe)
            if mv >= 6 and sufficienti >= 2:
                pro.append((affidabilita + 3, f"Costante: MV {self.formato(mv)}; sufficienza in {sufficienti}/{len(righe)} stagioni utili."))
        if ruolo != "P" and bonus is not None and bonus >= soglia_bonus:
            pro.append((indice_bonus + 5, f"Da bonus: {self.formato(bonus)} gol + assist medi a stagione."))
        if ruolo == "P" and fm is not None and fm >= 6.1:
            pro.append((indice_bonus + 5, f"Portiere da rendimento: FM storica {self.formato(fm)}."))
        if titolare and not ballottaggio:
            pro.append((72, "Titolare nella formazione tipo."))
        if primo_piazzato:
            nomi = {"rigori": "Rigorista", "punizioni": "Tiratore di punizioni", "angoli": "Tiratore di angoli"}
            pro.append((78, f"{nomi.get(primo_piazzato, primo_piazzato.title())} indicato come prima scelta."))
        if fuori_ruolo and ruolo in {"D", "C"} and any(parola in normalizza(fuori_ruolo) for parola in ("attacc", "punta", "trequart", "ala")):
            pro.append((75, f"Fuori ruolo offensivo: Classic {ruolo}, impiegato {fuori_ruolo}."))
        if contesto >= 68:
            testo_contesto = f"Squadra protettiva: {self.formato(ga90)} gol subiti/90 e {self.formato(clean_sheet)}% clean sheet nello storico." if ruolo in {"P", "D"} else f"Squadra propositiva: {self.formato(gol90)} gol/90 e {self.formato(tiri90)} tiri/90 nello storico."
            pro.append((round(contesto), testo_contesto))
        if ballottaggio:
            avversario = (indicazione[3] or indicazione[4]) if indicazione else None
            dettaglio = " con " + avversario if avversario else ""
            contro.append((95, "Ballottaggio" + dettaglio + ": minutaggio da monitorare."))
        elif indicazione and not titolare:
            contro.append((80, "Non inserito nella formazione tipo: gerarchia da verificare."))
        if pv is not None and pv < 15:
            contro.append((76, f"Campione ridotto: {self.formato(pv)} PV medie nello storico recente."))
        if mv is not None and mv < 6:
            contro.append((72, f"Voto da alzare: MV storica {self.formato(mv)} sotto la sufficienza."))
        if ruolo in {"C", "A"} and bonus is not None and bonus < soglia_bonus:
            contro.append((68, f"Bonus da consolidare: {self.formato(bonus)} gol + assist medi a stagione."))
        if contesto <= 38:
            testo_contesto = f"Contesto difensivo esigente: {self.formato(ga90)} gol subiti/90 e {self.formato(clean_sheet)}% clean sheet." if ruolo in {"P", "D"} else f"Volume offensivo contenuto: {self.formato(gol90)} gol/90 e {self.formato(tiri90)} tiri/90 della squadra."
            contro.append((70, testo_contesto))
        if len(righe) < 2:
            contro.append((64, "Storico limitato: valutazione più incerta del solito."))
        def seleziona(voci: list[tuple[int, str]]) -> list[str]:
            risultato = []
            for _, testo in sorted(voci, key=lambda voce: voce[0], reverse=True):
                if testo not in risultato:
                    risultato.append(testo)
                if len(risultato) == 3:
                    break
            return risultato
        pro_testo, contro_testo = seleziona(pro), seleziona(contro)
        self.pro_asta.configure(text="✓ Pro: " + (" • ".join(pro_testo) if pro_testo else "Profilo ancora da definire: dati storici insufficienti."))
        self.contro_asta.configure(text="⚠ Contro: " + (" • ".join(contro_testo) if contro_testo else "Nessuna criticità forte nei dati disponibili."))

    def aggiorna_elenco(self) -> None:
        selezionato = self.tabella.selection()
        identita = selezionato[0] if selezionato else None
        self.tabella.delete(*self.tabella.get_children())
        righe = self.query_giocatori()
        for riga in righe:
            fascia = riga[4].split(" · ")[0] if riga[4] else "Da assegnare"
            segno = "★" if riga[5] else ("⊘" if riga[6] else "")
            stato = "Disponibile" if riga[7] is None else (f"Mio · {riga[9]}" if riga[8] else f"{riga[7]} · {riga[9]}")
            tag = (fascia,) if riga[7] is None else (fascia, "non_disponibile")
            self.tabella.insert("", END, iid=str(riga[0]), tags=tag, values=(fascia, segno, stato, riga[1], riga[2], riga[3], *[self.formato(x) for x in riga[10:]]))
        if identita and self.tabella.exists(identita):
            self.tabella.selection_set(identita)
        self.stato.set(f"{len(righe)} giocatori visualizzati")

    def ordina_per(self, colonna: str) -> None:
        if self.ordina == colonna:
            self.inverso = not self.inverso
        else:
            self.ordina, self.inverso = colonna, False
        self.aggiorna_elenco()

    def giocatore_selezionato(self) -> int | None:
        selezione = self.tabella.selection()
        return int(selezione[0]) if selezione else None

    def mostra_glossario(self, evento) -> None:
        if self.tabella.identify_region(evento.x, evento.y) != "heading":
            self.suggerimento.nascondi()
            return
        indice = int(self.tabella.identify_column(evento.x)[1:]) - 1
        colonne = self.tabella["displaycolumns"]
        chiave = colonne[indice] if 0 <= indice < len(colonne) else None
        if chiave in GLOSSARIO:
            self.suggerimento.mostra(evento, GLOSSARIO[chiave])
        else:
            self.suggerimento.nascondi()

    def mostra_glossario_timeline(self, evento) -> None:
        if self.timeline.identify_region(evento.x, evento.y) != "heading":
            self.suggerimento.nascondi()
            return
        colonna = self.timeline.identify_column(evento.x)
        chiavi = {"#3": "pv", "#4": "mv", "#5": "fm", "#6": "gf", "#7": "ass", "#8": "amm", "#9": "esp", "#10": "qta", "#11": "fvm"}
        chiave = chiavi.get(colonna)
        if chiave:
            self.suggerimento.mostra_sotto_colonna(self.timeline, evento, GLOSSARIO[chiave])
        else:
            self.suggerimento.nascondi()

    def mostra_glossario_fbref(self, evento, tabella) -> None:
        if tabella.identify_region(evento.x, evento.y) != "heading":
            self.suggerimento.nascondi()
            return
        indice = int(tabella.identify_column(evento.x)[1:]) - 1
        colonne = tabella["columns"]
        if indice < 0 or indice >= len(colonne):
            self.suggerimento.nascondi()
            return
        codice = colonne[indice]
        if codice == "stagione":
            testo = "Stagione a cui si riferiscono i dati."
        elif codice == "squadra":
            testo = "Squadra del giocatore nella stagione mostrata."
        else:
            nome = tabella.heading(codice, "text")
            if "/90" in nome:
                testo = f"{nome} — valore rapportato a 90 minuti giocati."
            elif "(%)" in nome:
                testo = f"{nome} — percentuale calcolata per la stagione indicata."
            else:
                testo = f"{nome} — statistica riferita alla stagione e alla squadra mostrate."
        self.suggerimento.mostra_sotto_colonna(tabella, evento, testo)

    def ridimensiona_grafico(self, _evento=None) -> None:
        if hasattr(self, "timeline_grafico"):
            self.disegna_grafico(self.timeline_grafico)

    def disegna_grafico(self, timeline) -> None:
        self.grafico.delete("all")
        larghezza = max(self.grafico.winfo_width(), 360)
        altezza = max(self.grafico.winfo_height(), 160)
        margine_sinistro, margine_destro, margine_alto, margine_basso = 34, 14, 18, 28
        valori = [v for riga in timeline for v in (riga[3], riga[4]) if v is not None]
        if not valori:
            self.grafico.create_text(larghezza / 2, altezza / 2, text="Nessun voto disponibile per il grafico", fill="#667085")
            return
        minimo, massimo = 5.5, 7.0
        if min(valori) < minimo:
            minimo = min(valori) - .15
        if max(valori) > massimo:
            massimo = max(valori) + .15
        def punto(indice, voto):
            x = margine_sinistro + indice * (larghezza - margine_sinistro - margine_destro) / max(len(timeline) - 1, 1)
            y = margine_alto + (massimo - voto) * (altezza - margine_alto - margine_basso) / (massimo - minimo)
            return x, y
        for passo in range(4):
            voto = minimo + passo * (massimo - minimo) / 3
            y = punto(0, voto)[1]
            self.grafico.create_line(margine_sinistro, y, larghezza - margine_destro, y, fill="#e8edf3")
            self.grafico.create_text(margine_sinistro - 5, y, text=self.formato(voto), anchor="e", fill="#667085", font=("Sans", 8))
        if minimo <= 6.0 <= massimo:
            y_sufficienza = punto(0, 6.0)[1]
            self.grafico.create_line(margine_sinistro, y_sufficienza, larghezza - margine_destro, y_sufficienza,
                                     fill="#111111", dash=(5, 4), width=1)
            self.grafico.create_text(larghezza - margine_destro, y_sufficienza - 5, text="Sufficienza 6,0",
                                     anchor="se", fill="#111111", font=("Sans", 8, "bold"))
        for indice, riga in enumerate(timeline):
            x = punto(indice, minimo)[0]
            self.grafico.create_text(x, altezza - 12, text=riga[0][-5:], fill="#667085", font=("Sans", 8))
        for indice_colore, (indice_valore, colore) in enumerate(((3, "#1570ef"), (4, "#d92d20"))):
            punti = [punto(indice, riga[indice_valore]) for indice, riga in enumerate(timeline) if riga[indice_valore] is not None]
            if len(punti) > 1:
                self.grafico.create_line(*[coordinata for punto_grafico in punti for coordinata in punto_grafico], fill=colore, width=2)
            for x, y in punti:
                self.grafico.create_oval(x - 3, y - 3, x + 3, y + 3, fill=colore, outline="")
            self.grafico.create_text(42 + indice_colore * 68, 8, text=("MV" if indice_valore == 3 else "FM"), fill=colore, anchor="w", font=("Sans", 9, "bold"))

    def aggiorna_asta_live(self) -> None:
        if self.giocatore_live_id is None:
            self.rilancio_live.configure(text="Prossimo rilancio: —")
            self.tetti_live.configure(text="QtA: — · Massimo sostenibile: —")
            return
        giocatore = self.db.execute("""
            SELECT g.ruolo, q.quotazione_attuale
            FROM giocatori g LEFT JOIN quotazioni_fanta q ON q.giocatore_id=g.id AND q.stagione='2026-27'
            WHERE g.id=?
        """, (self.giocatore_live_id,)).fetchone()
        mio = self.db.execute("SELECT id FROM fantallenatori WHERE e_mio=1 ORDER BY id LIMIT 1").fetchone()
        massimo = self.massimo_offerta(mio[0], giocatore[0]) if giocatore and mio else 0
        try:
            prezzo = int(self.prezzo_live.get())
        except ValueError:
            prezzo = None
        rilancio = "—" if prezzo is None or prezzo < 0 else str(prezzo + 1)
        self.rilancio_live.configure(text=f"Prossimo rilancio: {rilancio}")
        qta = self.formato(giocatore[1]) if giocatore and giocatore[1] is not None else "—"
        self.tetti_live.configure(text=f"QtA: {qta} · Massimo sostenibile: {massimo}")

    def aggiorna_piano_b(self, giocatore_id: int, ruolo: str, fascia: str) -> None:
        self.piano_b.delete(*self.piano_b.get_children())
        self.titolo_piano_b.configure(text=f"Ruolo {ruolo} · priorità: {fascia}")
        righe = self.db.execute("""
            SELECT g.id, g.nome,
                   COALESCE((SELECT categoria FROM tag_asta t WHERE t.giocatore_id=g.id ORDER BY posizione LIMIT 1), 'Da assegnare'),
                   q.quotazione_attuale, q.fvm, s.fm
            FROM giocatori g
            LEFT JOIN quotazioni_fanta q ON q.giocatore_id=g.id AND q.stagione='2026-27'
            LEFT JOIN statistiche_fanta s ON s.giocatore_id=g.id AND s.stagione='2026-27'
            LEFT JOIN acquisti_lega a ON a.giocatore_id=g.id
            LEFT JOIN preferenze_giocatori p ON p.giocatore_id=g.id
            WHERE g.in_quotazioni_correnti=1 AND g.id<>? AND g.ruolo=? AND a.giocatore_id IS NULL
              AND COALESCE(p.escluso, 0)=0
            ORDER BY CASE WHEN COALESCE((SELECT categoria FROM tag_asta t WHERE t.giocatore_id=g.id ORDER BY posizione LIMIT 1), 'Da assegnare')=? THEN 0 ELSE 1 END,
                     COALESCE(q.fvm, 0) DESC, COALESCE(q.quotazione_attuale, 0) DESC, g.nome
            LIMIT 5
        """, (giocatore_id, ruolo, fascia)).fetchall()
        for identita, nome, alternativa_fascia, qta, fvm, fm in righe:
            self.piano_b.insert("", END, iid=str(identita), values=(nome, alternativa_fascia, self.formato(qta), self.formato(fvm), self.formato(fm)))

    def apri_piano_b(self, _evento=None) -> None:
        selezione = self.piano_b.selection()
        if not selezione:
            return
        identita = int(selezione[0])
        if self.tabella.exists(str(identita)):
            self.tabella.selection_set(str(identita))
            self.tabella.focus(str(identita))
        self.mostra_giocatore(identita=identita)

    def mostra_giocatore(self, _evento=None, identita: int | None = None) -> None:
        identita = self.giocatore_selezionato() if identita is None else identita
        if identita is None:
            return
        if self.giocatore_live_id != identita:
            self.giocatore_live_id = identita
            self.prezzo_live.set("")
        giocatore = self.db.execute("SELECT nome, ruolo, squadra, foto_locale FROM giocatori WHERE id=?", (identita,)).fetchone()
        tag = self.db.execute("SELECT categoria, nota FROM tag_asta WHERE giocatore_id=? ORDER BY posizione", (identita,)).fetchall()
        preferenze = self.db.execute("SELECT preferito, escluso, nota FROM preferenze_giocatori WHERE giocatore_id=?", (identita,)).fetchone() or (0, 0, "")
        self.pulsante_preferito.configure(text="★ Rimuovi preferito" if preferenze[0] else "★ Preferito")
        self.pulsante_escluso.configure(text="Rimuovi esclusione" if preferenze[1] else "Escludi")
        timeline = self.db.execute("""
            SELECT s.stagione, s.squadra, s.presenze, s.mv, s.fm, s.gol_fatti, s.assist, s.ammonizioni, s.espulsioni,
                   q.quotazione_attuale, q.fvm
            FROM statistiche_fanta s LEFT JOIN quotazioni_fanta q ON q.giocatore_id=s.giocatore_id AND q.stagione=s.stagione
            WHERE s.giocatore_id=? ORDER BY s.stagione DESC
        """, (identita,)).fetchall()
        corrente = timeline[0] if timeline else None
        riga_gol_subiti = self.db.execute("SELECT gol_subiti FROM statistiche_fanta WHERE giocatore_id=? AND stagione='2026-27'", (identita,)).fetchone()
        gol_subiti = riga_gol_subiti[0] if riga_gol_subiti else None
        storico = self.db.execute("""
            SELECT s.presenze, s.mv, s.fm, s.gol_fatti, s.gol_subiti, s.assist, q.fvm
            FROM statistiche_fanta s LEFT JOIN quotazioni_fanta q ON q.giocatore_id=s.giocatore_id AND q.stagione=s.stagione
            WHERE s.giocatore_id=? AND s.stagione<'2026-27' ORDER BY s.stagione
        """, (identita,)).fetchall()
        def media(indice: int) -> float | None:
            valori = [riga[indice] for riga in storico if riga[indice] is not None]
            return sum(valori) / len(valori) if valori else None
        gol_media, assist_media = media(3), media(5)
        medie = {"PV": media(0), "MV": media(1), "FM": media(2), "Gol": gol_media, "GS": media(4),
                 "Assist": assist_media, "FVM": media(6), "G+A": None if gol_media is None and assist_media is None else (gol_media or 0) + (assist_media or 0)}
        testo = []
        piazzati = self.db.execute("SELECT tipo, priorita, fonte FROM specialisti_piazzati WHERE giocatore_id=? ORDER BY tipo, priorita", (identita,)).fetchall()
        if piazzati:
            etichette_piazzati = {"rigori": "Rigorista", "punizioni": "Punizioni", "angoli": "Angoli"}
            testo += ["Piazzati 2026-27: " + " · ".join(f"{etichette_piazzati[tipo]} #{priorita}" for tipo, priorita, _ in piazzati)]
        indicazione = self.db.execute("SELECT titolare, ballottaggio, fuori_ruolo, ballottaggio_vantaggio, ballottaggio_svantaggio FROM indicazioni_formazione WHERE giocatore_id=?", (identita,)).fetchone()
        if indicazione:
            testo += ([""] if testo else []) + ["Inserito nella formazione tipo." if indicazione[0] else "Non inserito nella formazione tipo."]
            if indicazione[3]:
                testo += [f"Ballottaggio: in vantaggio su {indicazione[3]}."]
            if indicazione[4]:
                testo += [f"Ballottaggio: dietro a {indicazione[4]}."]
            if indicazione[2]:
                testo += [f"Fuori ruolo: Classic {giocatore[1]}, schierato {indicazione[2]}."]
        squadra_api = None
        anagrafica = self.db.execute("SELECT nazionalita, codice_nazione, eta FROM anagrafica_giocatori WHERE giocatore_id=?", (identita,)).fetchone()
        nazionalita = anagrafica[0] if anagrafica else "—"
        codice_nazione = anagrafica[1] if anagrafica else None
        eta = anagrafica[2] if anagrafica and anagrafica[2] is not None else "—"
        squadra_anagrafica = giocatore[2] or "—"
        aggiornato_il = None
        reale = self.db.execute("SELECT dati_json, aggiornato_il FROM dati_reali_api WHERE giocatore_id=?", (identita,)).fetchone()
        if reale:
            dati = json.loads(reale[0])
            profilo = dati.get("player", {})
            statistiche_api = (dati.get("statistics") or [{}])[0]
            partite = statistiche_api.get("games", {})
            gol = statistiche_api.get("goals", {})
            squadra_api = dati.get("team", statistiche_api.get("team", {}))
            if nazionalita == "—":
                nazionalita = profilo.get("nationality") or "—"
            eta = profilo.get("age") or "—"
            aggiornato_il = reale[1]
            if partite:
                testo += ([""] if testo else []) + [f"Minuti: {partite.get('minutes') or '—'} · Voto: {partite.get('rating') or '—'} · Presenze: {partite.get('appearences') or 0} · Titolare: {partite.get('lineups') or 0}",
                                                       f"Gol: {gol.get('total') or 0} · Assist: {gol.get('assists') or 0}"]
        self.nome_scheda.configure(text=giocatore[0])
        self.badge_qta.configure(text=f"QtA {self.formato(corrente[9]) if corrente else '—'}")
        self.badge_fvm.configure(text=f"FVM {self.formato(corrente[10]) if corrente else '—'}")
        self.profilo_scheda.configure(text=f"Ruolo Classic {giocatore[1]} · Squadra: {squadra_anagrafica}")
        self.anagrafica_scheda.configure(text=f"Nazionalità: {nazionalita}")
        self.eta_scheda.configure(text=f" - Età: {eta} anni" if eta != "—" else " - Età: —")
        self.aggiorna_bandiera(codice_nazione)
        self.aggiornamento_scheda.configure(text=f"Dati aggiornati il {self.formato_data(aggiornato_il)}" if aggiornato_il else "")
        self.aggiorna_foto(giocatore[3])
        self.aggiorna_stemma(None, squadra_anagrafica)
        self.aggiorna_contesto_squadra(giocatore[2] or squadra_anagrafica, giocatore[1], identita)
        self.aggiorna_asta_live()
        self.aggiorna_piano_b(identita, giocatore[1], tag[0][0] if tag else "Da assegnare")
        self.aggiorna_sintesi_asta(identita, giocatore[1], giocatore[2] or squadra_anagrafica, tag, corrente, gol_subiti, medie, storico)
        note_asta = []
        if preferenze[2]:
            note_asta.append(f"Nota personale: {preferenze[2]}")
        note_asta += [f"Nota fascia: {nota}" for _, nota in tag if nota]
        self.nota_asta.configure(text=" · ".join(note_asta) if note_asta else "Nessuna nota personale.")
        self.dettaglio.configure(text="\n".join(testo))
        self.timeline.delete(*self.timeline.get_children())
        indici_positivi = (2, 3, 4, 5, 6, 9, 10)
        massimi = {indice: max((riga[indice] for riga in timeline if riga[indice] is not None), default=None) for indice in indici_positivi}
        for indice_riga, riga in enumerate(timeline):
            valori = [self.formato_massimo(valore, massimi.get(indice)) if indice in indici_positivi else self.formato(valore)
                      for indice, valore in enumerate(riga[2:], start=2)]
            self.timeline.insert("", END, values=(riga[0], riga[1], *valori),
                                 tags=("riga_pari",) if indice_riga % 2 else ())
        self.timeline_grafico = list(reversed(timeline))
        self.disegna_grafico(self.timeline_grafico)
        self.mostra_statistiche_fbref(identita)

    def mostra_statistiche_fbref(self, giocatore_id: int) -> None:
        righe = self.db.execute("""
            SELECT s.stagione, s.squadra_fbref, s.dati_json
            FROM statistiche_fbref s JOIN collegamenti_fbref c ON c.fbref_id=s.fbref_id AND c.stagione=s.stagione
            WHERE c.giocatore_id=? ORDER BY s.stagione DESC
        """, (giocatore_id,)).fetchall()
        per_fonte = {fonte: [] for fonte in FONTI_FBREF}
        for stagione, squadra, dati_json in righe:
            for fonte, metriche in json.loads(dati_json).items():
                per_fonte[fonte].append((stagione, squadra, metriche))
        for fonte, tabella in self.tabelle_fbref.items():
            tabella.delete(*tabella.get_children())
            righe_fonte = per_fonte[fonte]
            metriche = righe_fonte[0][2] if righe_fonte else []
            colonne = ("stagione", "squadra", *[metrica["codice"] for metrica in metriche])
            tabella.configure(columns=colonne)
            tabella.tag_configure("riga_pari", background="#f7f9fc")
            tabella.heading("stagione", text="Stagione"); tabella.column("stagione", width=80, anchor="center")
            tabella.heading("squadra", text="Squadra"); tabella.column("squadra", width=105)
            for metrica in metriche:
                codice, nome = metrica["codice"], metrica["nome"]
                valori_plot = sorted(
                    [(stagione, numero(next((m["valore"] for m in valori if m["codice"] == codice), "")))
                     for stagione, _, valori in righe_fonte],
                    key=lambda valore: valore[0],
                )
                squadre_plot = [(stagione, squadra) for stagione, squadra, _ in righe_fonte]
                tabella.heading(codice, text=nome, command=lambda n=nome, v=valori_plot, s=squadre_plot: self.apri_plot_statistica(n, v, s))
                tabella.column(codice, width=max(92, len(nome) * 7), anchor="center")
            massimi = {}
            if len(righe_fonte) > 1:
                for metrica in metriche:
                    if metrica["positivo"]:
                        valori_numerici = [numero(next((m["valore"] for m in valori if m["codice"] == metrica["codice"]), "")) for _, _, valori in righe_fonte]
                        massimi[metrica["codice"]] = max((valore for valore in valori_numerici if valore is not None), default=None)
            for indice_riga, (stagione, squadra, valori) in enumerate(righe_fonte):
                tabella.insert("", END, values=(stagione, squadra, *[self.formato_massimo(numero(metrica["valore"]), massimi.get(metrica["codice"])) if metrica["positivo"] else self.formato(numero(metrica["valore"])) for metrica in valori]),
                              tags=("riga_pari",) if indice_riga % 2 else ())

    @staticmethod
    def valore_metrica_squadra(fonti: dict, fonte: str, codice: str) -> float | None:
        metrica = next((metrica for metrica in fonti.get(fonte, []) if metrica["codice"] == codice), None)
        return numero(metrica["valore"]) if metrica else None

    def righe_squadra_fbref(self, squadra: str) -> list[tuple[str, dict]]:
        righe = self.db.execute("""
            SELECT stagione, dati_json FROM statistiche_squadre_fbref
            WHERE squadra_normalizzata=? ORDER BY stagione DESC
        """, (normalizza_squadra(squadra),)).fetchall()
        return [(stagione, json.loads(dati_json)) for stagione, dati_json in righe]

    def aggiorna_contesto_squadra(self, squadra: str, ruolo: str, giocatore_id: int) -> None:
        righe = self.righe_squadra_fbref(squadra)
        self.squadra_contesto = squadra
        if not righe:
            self.titolo_contesto_squadra.configure(text=f"{squadra} · dati squadra non disponibili")
            self.storico_contesto_squadra.configure(text="Storico Serie A: —")
            self.commento_contesto_squadra.configure(text="Non ci sono ancora dati storici sufficienti per valutare il contesto della squadra.")
            for etichetta, valore_squadra in self.metriche_contesto_squadra:
                etichetta.configure(text="—"); valore_squadra.configure(text="—")
            return
        stagione, fonti = righe[0]
        complete = [(stagione_storica, fonti_storiche) for stagione_storica, fonti_storiche in righe if stagione_storica < "2026-27"][:5]
        if ruolo == "P":
            metriche = (("Gol subiti /90", "goalkeeping", "GA90#1", ""), ("Parate (%)", "goalkeeping", "Save%#1", "%"),
                        ("Clean sheet (%)", "goalkeeping", "CS%#1", "%"), ("Tiri in porta subiti", "goalkeeping", "SoTA#1", ""))
            storico_metriche = (("goalkeeping", "GA90#1", "GS/90", ""), ("goalkeeping", "CS%#1", "CS", "%"))
        elif ruolo == "D":
            metriche = (("Gol subiti /90", "goalkeeping", "GA90#1", ""), ("Clean sheet (%)", "goalkeeping", "CS%#1", "%"),
                        ("Possesso (%)", "standard_stats", "Poss#1", "%"), ("Ammonizioni", "standard_stats", "CrdY#1", ""))
            storico_metriche = (("goalkeeping", "GA90#1", "GS/90", ""), ("goalkeeping", "CS%#1", "CS", "%"))
        else:
            metriche = (("Gol squadra /90", "standard_stats", "Gls#2", ""), ("Tiri /90", "shooting_stats", "Sh/90#1", ""),
                        ("Tiri in porta /90", "shooting_stats", "SoT/90#1", ""), ("Possesso (%)", "standard_stats", "Poss#1", "%"))
            storico_metriche = (("standard_stats", "Gls#2", "Gol/90", ""), ("shooting_stats", "Sh/90#1", "Tiri/90", ""))
        if complete:
            self.titolo_contesto_squadra.configure(text=f"{squadra} · medie {complete[-1][0]}–{complete[0][0]}")
        else:
            self.titolo_contesto_squadra.configure(text=f"{squadra} · {stagione}")
        for (etichetta, valore_squadra), (nome, fonte, codice, suffisso) in zip(self.metriche_contesto_squadra, metriche):
            valori = [self.valore_metrica_squadra(fonti_storiche, fonte, codice) for _, fonti_storiche in complete]
            valori = [valore_storico for valore_storico in valori if valore_storico is not None]
            valore = sum(valori) / len(valori) if valori else self.valore_metrica_squadra(fonti, fonte, codice)
            etichetta.configure(text=nome)
            valore_squadra.configure(text=(self.formato(valore) + suffisso) if valore is not None else "—")
            descrizione = f"{nome} — media delle stagioni Serie A disponibili della squadra."
            for widget in (etichetta, valore_squadra):
                widget.bind("<Enter>", lambda evento, testo=descrizione, widget=widget: self.suggerimento.mostra_sotto(widget, testo))
                widget.bind("<Leave>", lambda _: self.suggerimento.nascondi())
        parti = []
        for fonte, codice, etichetta, suffisso in storico_metriche:
            valori = [self.valore_metrica_squadra(fonti_storiche, fonte, codice) for _, fonti_storiche in complete]
            valori = [valore for valore in valori if valore is not None]
            if valori:
                parti.append(f"{etichetta} {self.formato(sum(valori) / len(valori))}{suffisso}")
        self.storico_contesto_squadra.configure(text=(f"Storico ultime {len(complete)} stagioni complete: " + " · ".join(parti)) if parti else "Storico Serie A: —")
        self.commento_contesto_squadra.configure(text=self.commento_contesto_squadra_testuale(squadra, giocatore_id, ruolo, complete))

    def commento_contesto_squadra_testuale(self, squadra: str, giocatore_id: int, ruolo: str, stagioni_squadra: list[tuple[str, dict]]) -> str:
        """Incrocia le medie storiche della squadra con le statistiche Classic del calciatore."""
        if not stagioni_squadra:
            return "Non ci sono ancora stagioni complete sufficienti per valutare il contesto della squadra."

        def media_squadra(fonte: str, codice: str) -> float | None:
            valori = [self.valore_metrica_squadra(fonti, fonte, codice) for _, fonti in stagioni_squadra]
            valori = [valore for valore in valori if valore is not None]
            return sum(valori) / len(valori) if valori else None

        righe_giocatore = self.db.execute("""
            SELECT stagione, mv, fm, gol_fatti, assist
            FROM statistiche_fanta
            WHERE giocatore_id=? AND stagione<'2026-27'
            ORDER BY stagione DESC LIMIT 5
        """, (giocatore_id,)).fetchall()

        def media_giocatore(indice: int) -> float | None:
            valori = [riga[indice] for riga in righe_giocatore if riga[indice] is not None]
            return sum(valori) / len(valori) if valori else None

        mv, fm = media_giocatore(1), media_giocatore(2)
        bonus = [riga[3] + riga[4] for riga in righe_giocatore if riga[3] is not None and riga[4] is not None]
        bonus_medi = sum(bonus) / len(bonus) if bonus else None
        periodo = f"nelle ultime {len(stagioni_squadra)} stagioni complete"

        if ruolo == "P":
            gol_subiti_90 = media_squadra("goalkeeping", "GA90#1")
            clean_sheet = media_squadra("goalkeeping", "CS%#1")
            resa = f"FM storica {self.formato(fm)}" if fm is not None else "dati Classic storici parziali"
            squadra_testo = []
            if gol_subiti_90 is not None:
                squadra_testo.append(f"{self.formato(gol_subiti_90)} gol subiti/90")
            if clean_sheet is not None:
                squadra_testo.append(f"{self.formato(clean_sheet)}% di clean sheet")
            if gol_subiti_90 is not None and clean_sheet is not None and gol_subiti_90 <= 1.15 and clean_sheet >= 30:
                giudizio = "contesto favorevole a imbattibilità e rendimento."
            elif gol_subiti_90 is not None and (gol_subiti_90 >= 1.4 or (clean_sheet is not None and clean_sheet < 25)):
                giudizio = "contesto meno favorevole ai clean sheet: diventano importanti parate e voto."
            else:
                giudizio = "contesto difensivo intermedio, da leggere insieme al minutaggio."
            return f"Con {resa}, {squadra} ha registrato {', '.join(squadra_testo) or 'dati difensivi parziali'} {periodo}: {giudizio}"

        if ruolo == "D":
            gol_subiti_90 = media_squadra("goalkeeping", "GA90#1")
            clean_sheet = media_squadra("goalkeeping", "CS%#1")
            profilo = []
            if mv is not None:
                profilo.append(f"MV storica {self.formato(mv)}")
            if bonus_medi is not None:
                profilo.append(f"{self.formato(bonus_medi)} gol+assist medi a stagione")
            difesa = []
            if gol_subiti_90 is not None:
                difesa.append(f"{self.formato(gol_subiti_90)} gol subiti/90")
            if clean_sheet is not None:
                difesa.append(f"{self.formato(clean_sheet)}% clean sheet")
            if gol_subiti_90 is not None and clean_sheet is not None and gol_subiti_90 <= 1.15 and clean_sheet >= 30:
                giudizio = "una base difensiva che può sostenere modificatore, imbattibilità e voti."
            elif gol_subiti_90 is not None and (gol_subiti_90 >= 1.4 or (clean_sheet is not None and clean_sheet < 25)):
                giudizio = "un quadro che limita il potenziale da clean sheet e richiede bonus o voti alti."
            else:
                giudizio = "un quadro difensivo equilibrato: pesano soprattutto titolarità e propensione al bonus."
            return f"Il giocatore porta {' e '.join(profilo) if profilo else 'dati storici Classic parziali'}; {squadra} ha avuto {', '.join(difesa) or 'dati difensivi parziali'} {periodo}: {giudizio}"

        gol_90 = media_squadra("standard_stats", "Gls#2")
        tiri_90 = media_squadra("shooting_stats", "Sh/90#1")
        profilo = []
        if bonus_medi is not None:
            profilo.append(f"{self.formato(bonus_medi)} gol+assist medi a stagione")
        if fm is not None:
            profilo.append(f"FM storica {self.formato(fm)}")
        attacco = []
        if gol_90 is not None:
            attacco.append(f"{self.formato(gol_90)} gol/90")
        if tiri_90 is not None:
            attacco.append(f"{self.formato(tiri_90)} tiri/90")
        if gol_90 is not None and tiri_90 is not None and gol_90 >= 1.5 and tiri_90 >= 12:
            giudizio = "un volume offensivo che può valorizzare un profilo da bonus."
        elif gol_90 is not None and (gol_90 <= 1.1 or (tiri_90 is not None and tiri_90 < 9)):
            giudizio = "un contesto con volume ridotto, quindi i bonus potrebbero essere più difficili da sostenere."
        else:
            giudizio = "un contesto offensivo intermedio: la differenza la fanno ruolo reale e piazzati."
        return f"Il giocatore ha {', '.join(profilo) if profilo else 'dati storici Classic parziali'}; {squadra} ha prodotto {', '.join(attacco) or 'dati offensivi parziali'} {periodo}: {giudizio}"

    def apri_dettaglio_squadra(self) -> None:
        squadra = getattr(self, "squadra_contesto", None)
        righe = self.righe_squadra_fbref(squadra) if squadra else []
        if not righe:
            messagebox.showinfo("Dettaglio squadra", "Nessuna statistica squadra disponibile.", parent=self.radice)
            return
        finestra = Toplevel(self.radice)
        finestra.title(f"Dettaglio squadra · {squadra}")
        finestra.geometry("920x560"); finestra.minsize(620, 380); finestra.resizable(True, True)
        notebook = ttk.Notebook(finestra)
        notebook.pack(fill="both", expand=True, padx=12, pady=12)
        etichette = {"standard_stats": "Prestazioni", "shooting_stats": "Tiro", "goalkeeping": "Portieri", "time": "Impiego", "misc": "Disciplina"}
        for fonte in FONTI_FBREF:
            righe_fonte = [(stagione, fonti[fonte]) for stagione, fonti in righe if fonte in fonti]
            if not righe_fonte:
                continue
            scheda = ttk.Frame(notebook, padding=8)
            notebook.add(scheda, text=etichette[fonte])
            metriche = righe_fonte[0][1]
            colonne = ("stagione", *[metrica["codice"] for metrica in metriche])
            tabella = ttk.Treeview(scheda, columns=colonne, show="headings")
            tabella.heading("stagione", text="Stagione"); tabella.column("stagione", width=90, anchor="center")
            for metrica in metriche:
                codice, nome = metrica["codice"], metrica["nome"]
                valori_plot = sorted([(stagione, self.valore_metrica_squadra({fonte: valori}, fonte, codice)) for stagione, valori in righe_fonte], key=lambda valore: valore[0])
                tabella.heading(codice, text=nome, command=lambda n=nome, v=valori_plot: self.apri_plot_statistica(n, v))
                tabella.column(codice, width=max(96, len(nome) * 7), anchor="center")
            for stagione, valori in righe_fonte:
                tabella.insert("", END, values=(stagione, *[self.formato(numero(metrica["valore"])) for metrica in valori]))
            barra_v = ttk.Scrollbar(scheda, orient="vertical", command=tabella.yview)
            barra_h = ttk.Scrollbar(scheda, orient="horizontal", command=tabella.xview)
            tabella.configure(yscrollcommand=barra_v.set, xscrollcommand=barra_h.set)
            tabella.bind("<Motion>", lambda evento, tabella=tabella: self.mostra_glossario_fbref(evento, tabella))
            tabella.bind("<Leave>", lambda _: self.suggerimento.nascondi())
            tabella.grid(row=0, column=0, sticky="nsew"); barra_v.grid(row=0, column=1, sticky="ns"); barra_h.grid(row=1, column=0, sticky="ew")
            scheda.rowconfigure(0, weight=1); scheda.columnconfigure(0, weight=1)

    def apri_plot_fanta(self, metrica: str) -> None:
        giocatore_id = self.giocatore_selezionato()
        if giocatore_id is None:
            return
        campi = {"pv": ("s.presenze", "Presenze a voto"), "mv": ("s.mv", "Media voto"), "fm": ("s.fm", "Fantamedia"),
                  "gf": ("s.gol_fatti", "Gol fatti"), "ass": ("s.assist", "Assist"), "amm": ("s.ammonizioni", "Ammonizioni"),
                  "esp": ("s.espulsioni", "Espulsioni"), "qta": ("q.quotazione_attuale", "Quotazione attuale Classic"), "fvm": ("q.fvm", "FVM")}
        campo, nome = campi[metrica]
        valori = self.db.execute(f"""
            SELECT s.stagione, {campo}, s.squadra FROM statistiche_fanta s
            LEFT JOIN quotazioni_fanta q ON q.giocatore_id=s.giocatore_id AND q.stagione=s.stagione
            WHERE s.giocatore_id=? ORDER BY s.stagione
        """, (giocatore_id,)).fetchall()
        squadre = [(stagione, squadra) for stagione, _, squadra in valori]
        self.apri_plot_statistica(nome, [(stagione, valore) for stagione, valore, _ in valori], squadre)

    def apri_plot_statistica(self, nome: str, valori: list[tuple[str, float | None]], squadre: list[tuple[str, str]] | None = None) -> None:
        dati = [(stagione, valore) for stagione, valore in valori if valore is not None]
        finestra = Toplevel(self.radice); finestra.title(nome); finestra.transient(self.radice)
        finestra.geometry("720x430"); finestra.minsize(560, 330); finestra.resizable(True, True)
        ttk.Button(finestra, text="✕ Chiudi", command=finestra.destroy).pack(anchor="ne", padx=8, pady=6)
        grafico = tk.Canvas(finestra, background="#ffffff", highlightthickness=0)
        grafico.pack(fill="both", expand=True, padx=12, pady=(0, 12))
        squadre_per_stagione = dict(squadre or [])
        finestra.immagini_stemmi = []

        def ridisegna(_: tk.Event | None = None) -> None:
            larghezza, altezza = grafico.winfo_width(), grafico.winfo_height()
            if larghezza < 100 or altezza < 100:
                return
            grafico.delete("all")
            if not dati:
                grafico.create_text(larghezza / 2, altezza / 2, text="Nessun dato numerico disponibile", fill="#667085")
                return
            valori_numerici = [valore for _, valore in dati]
            minimo, massimo, tacche_y, intero = self.tacche_asse(nome, valori_numerici)
            etichette_y = [str(int(valore)) if intero else self.formato(valore) for valore in tacche_y]
            sinistra = max(58, 18 + max(len(etichetta) for etichetta in etichette_y) * 8)
            destra, alto, basso = 28, 38, 84
            x0, x1, y0, y1 = sinistra, larghezza - destra, alto, altezza - basso
            grafico.create_text(x0, 18, text=nome, anchor="w", font=("Sans", 12, "bold"))

            def punto(indice: int, valore: float) -> tuple[float, float]:
                x = x0 + indice * (x1 - x0) / max(len(dati) - 1, 1)
                y = y0 + (massimo - valore) * (y1 - y0) / (massimo - minimo)
                return x, y

            if squadre_per_stagione:
                periodi = []
                for indice, (stagione, _) in enumerate(dati):
                    squadra = squadre_per_stagione.get(stagione)
                    if not squadra:
                        continue
                    if periodi and periodi[-1][0] == squadra and periodi[-1][2] == indice - 1:
                        periodi[-1][2] = indice
                    else:
                        periodi.append([squadra, indice, indice])
                colori_bande = ("#edf4ff", "#effaf3", "#fff4ed", "#f5f3ff", "#fff1f3")
                finestra.immagini_stemmi = []
                for indice_periodo, (squadra, inizio, fine) in enumerate(periodi):
                    x_inizio = x0 if inizio == 0 else (punto(inizio - 1, minimo)[0] + punto(inizio, minimo)[0]) / 2
                    x_fine = x1 if fine == len(dati) - 1 else (punto(fine, minimo)[0] + punto(fine + 1, minimo)[0]) / 2
                    grafico.create_rectangle(x_inizio, y0, x_fine, y1, fill=colori_bande[indice_periodo % len(colori_bande)], outline="")
                    centro = (x_inizio + x_fine) / 2
                    percorso_stemma = self.percorso_stemma_squadra(squadra)
                    if percorso_stemma:
                        try:
                            with Image.open(percorso_stemma) as sorgente:
                                immagine = sorgente.convert("RGBA")
                                filtro = Image.Resampling.LANCZOS if hasattr(Image, "Resampling") else Image.LANCZOS
                                immagine.thumbnail((22, 22), filtro)
                                stemma = ImageTk.PhotoImage(immagine)
                            finestra.immagini_stemmi.append(stemma)
                            grafico.create_image(centro, y0 + 13, image=stemma)
                        except (OSError, tk.TclError):
                            pass
                    grafico.create_text(centro, y0 + 28, text=squadra, width=max(48, x_fine - x_inizio - 6), fill="#475467", font=("Sans", 8, "bold"))

            for valore, etichetta in zip(tacche_y, etichette_y):
                y = punto(0, valore)[1]
                grafico.create_line(x0, y, x1, y, fill="#e8edf3")
                grafico.create_text(x0 - 8, y, text=etichetta, anchor="e", fill="#667085")
            grafico.create_line(x0, y1, x1, y1, fill="#98a2b3")
            punti = [punto(indice, valore) for indice, (_, valore) in enumerate(dati)]
            if len(punti) > 1:
                grafico.create_line(*[coordinata for punto_grafico in punti for coordinata in punto_grafico], fill="#1570ef", width=2)
            for (stagione, _), (x, y) in zip(dati, punti):
                grafico.create_oval(x - 4, y - 4, x + 4, y + 4, fill="#1570ef", outline="")
                grafico.create_text(x, y1 + 12, text=stagione, anchor="n", angle=45, fill="#667085", font=("Sans", 9))

        grafico.bind("<Configure>", ridisegna)
        finestra.after_idle(ridisegna)

    @staticmethod
    def sagoma_anonima(lato: int) -> Image.Image:
        immagine = Image.new("RGBA", (lato, lato), (0, 0, 0, 0))
        disegno = ImageDraw.Draw(immagine)
        colore = "#98a2b3"
        disegno.ellipse((lato * .32, lato * .10, lato * .68, lato * .46), fill=colore)
        disegno.ellipse((lato * .16, lato * .48, lato * .84, lato * 1.18), fill=colore)
        return immagine

    def aggiorna_foto(self, percorso: str | None) -> None:
        if percorso and Path(percorso).exists():
            try:
                with Image.open(percorso) as sorgente:
                    immagine = sorgente.convert("RGBA")
                    filtro = Image.Resampling.LANCZOS if hasattr(Image, "Resampling") else Image.LANCZOS
                    immagine.thumbnail((76, 76), filtro)
                    immagine = ImageTk.PhotoImage(immagine)
                self.immagine_scheda = immagine
                self.foto_scheda.configure(image=immagine, text="")
                return
            except (OSError, tk.TclError):
                pass
        self.immagine_scheda = ImageTk.PhotoImage(self.sagoma_anonima(76))
        self.foto_scheda.configure(image=self.immagine_scheda, text="")

    def aggiorna_bandiera(self, codice: str | None) -> None:
        percorso = BANDIERE_DIR / f"{codice}.png" if codice else None
        if percorso and percorso.exists():
            try:
                with Image.open(percorso) as sorgente:
                    immagine = sorgente.convert("RGBA")
                    filtro = Image.Resampling.LANCZOS if hasattr(Image, "Resampling") else Image.LANCZOS
                    immagine.thumbnail((28, 18), filtro)
                    self.immagine_bandiera = ImageTk.PhotoImage(immagine)
                self.bandiera_scheda.configure(image=self.immagine_bandiera, text="")
                return
            except (OSError, tk.TclError):
                pass
        self.bandiera_scheda.configure(image="", text="")

    def percorso_stemma_squadra(self, nome_squadra: str | None) -> Path | None:
        if not nome_squadra:
            return None
        if not hasattr(self, "stemmi_per_squadra"):
            self.stemmi_per_squadra = {}
            for (dati_json,) in self.db.execute("SELECT dati_json FROM dati_reali_api"):
                try:
                    dati = json.loads(dati_json)
                    squadra = dati.get("team") or ((dati.get("statistics") or [{}])[0].get("team") or {})
                    identita, nome = squadra.get("id"), squadra.get("name")
                    percorso = STEMMI_DIR / f"{identita}.png" if identita else None
                    if nome and percorso and percorso.exists():
                        self.stemmi_per_squadra.setdefault(normalizza(nome), percorso)
                except (json.JSONDecodeError, AttributeError, IndexError):
                    continue
        nome_normalizzato = normalizza(nome_squadra)
        alias = {"milan": "acmilan", "roma": "asroma", "verona": "hellasverona"}
        percorso = self.stemmi_per_squadra.get(alias.get(nome_normalizzato, nome_normalizzato))
        if percorso:
            return percorso
        storico = STEMMI_DIR / f"storico_{nome_normalizzato}.png"
        return storico if storico.exists() else None

    def aggiorna_stemma(self, squadra: dict | None, nome_squadra: str | None = None) -> None:
        percorso = self.percorso_stemma_squadra(nome_squadra)
        squadra_id = squadra.get("id") if squadra else None
        if not squadra_id and nome_squadra and not percorso:
            riga = self.db.execute("""
                SELECT d.dati_json FROM dati_reali_api d JOIN giocatori g ON g.id=d.giocatore_id
                WHERE g.squadra=? LIMIT 1
            """, (nome_squadra,)).fetchone()
            if riga:
                try:
                    squadra_id = json.loads(riga[0]).get("team", {}).get("id")
                except (json.JSONDecodeError, AttributeError):
                    pass
        if not percorso:
            percorso = STEMMI_DIR / f"{squadra_id}.png" if squadra_id else None
        if percorso and percorso.exists():
            try:
                immagine = tk.PhotoImage(file=percorso)
                fattore = max(immagine.width() // 52, immagine.height() // 52, 1)
                if fattore > 1:
                    immagine = immagine.subsample(fattore, fattore)
                self.immagine_stemma = immagine
                self.stemma_scheda.configure(image=immagine, text="")
                return
            except tk.TclError:
                pass
        self.stemma_scheda.configure(image="", text="")

    def icona_rosa(self, foto_locale: str | None, dati_squadra: str | None, nome_squadra: str | None = None) -> ImageTk.PhotoImage | None:
        percorsi = []
        if foto_locale and Path(foto_locale).exists():
            percorsi.append(Path(foto_locale))
        stemma = self.percorso_stemma_squadra(nome_squadra)
        if not stemma:
            try:
                squadra_id = json.loads(dati_squadra or "{}").get("team", {}).get("id")
            except (json.JSONDecodeError, AttributeError):
                squadra_id = None
            stemma = STEMMI_DIR / f"{squadra_id}.png" if squadra_id else None
        if stemma and stemma.exists():
            percorsi.append(stemma)
        immagini = []
        foto_caricata = False
        for percorso in percorsi:
            try:
                with Image.open(percorso) as immagine:
                    filtro = Image.Resampling.LANCZOS if hasattr(Image, "Resampling") else Image.LANCZOS
                    miniatura = immagine.convert("RGBA")
                    miniatura.thumbnail((16, 16), filtro)
                    immagini.append(miniatura.copy())
                    if foto_locale and percorso == Path(foto_locale):
                        foto_caricata = True
            except OSError:
                continue
        if not foto_caricata:
            immagini.insert(0, self.sagoma_anonima(16))
        larghezza_totale = sum(immagine.width for immagine in immagini) + 3 * (len(immagini) - 1)
        composita = Image.new("RGBA", (larghezza_totale, 16), (255, 255, 255, 0))
        posizione = 0
        for immagine in immagini:
            composita.alpha_composite(immagine, (posizione, 0))
            posizione += immagine.width + 3
        return ImageTk.PhotoImage(composita)

    def budget(self) -> tuple[int, int, dict[str, int]]:
        mio = self.db.execute("SELECT id, crediti_iniziali FROM fantallenatori WHERE e_mio=1 ORDER BY id LIMIT 1").fetchone()
        if mio is None:
            return 600, sum(ROSA.values()), {ruolo: 0 for ruolo in ROSA}
        righe = self.db.execute("SELECT g.ruolo, COUNT(*), COALESCE(SUM(a.prezzo), 0) FROM acquisti_lega a JOIN giocatori g ON g.id=a.giocatore_id WHERE a.fantallenatore_id=? GROUP BY g.ruolo", (mio[0],)).fetchall()
        per_ruolo = {ruolo: 0 for ruolo in ROSA}; speso = 0
        for ruolo, conteggio, totale in righe:
            per_ruolo[ruolo] = conteggio; speso += totale
        return mio[1] - speso, sum(ROSA.values()) - sum(per_ruolo.values()), per_ruolo

    def aggiorna_budget(self) -> None:
        residuo, slot, per_ruolo = self.budget()
        massimo = residuo - max(slot - 1, 0)
        self.riepilogo_budget.configure(text=f"Crediti: {residuo}/600 · Rilancio massimo: {massimo}")
        for ruolo in ROSA:
            self.riepilogo_ruoli[ruolo].configure(text=f"{ruolo} {per_ruolo[ruolo]}/{ROSA[ruolo]}")
        if hasattr(self, "prezzo_live"):
            self.aggiorna_asta_live()

    def riepilogo_fantallenatore(self, fantallenatore_id: int) -> tuple[int, int, dict[str, int], dict[str, int], list[tuple]]:
        crediti = self.db.execute("SELECT crediti_iniziali FROM fantallenatori WHERE id=?", (fantallenatore_id,)).fetchone()[0]
        righe = self.db.execute("""
            SELECT g.ruolo, COUNT(*), COALESCE(SUM(a.prezzo), 0)
            FROM acquisti_lega a JOIN giocatori g ON g.id=a.giocatore_id
            WHERE a.fantallenatore_id=? GROUP BY g.ruolo
        """, (fantallenatore_id,)).fetchall()
        quantita = {ruolo: 0 for ruolo in ROSA}
        speso_ruolo = {ruolo: 0 for ruolo in ROSA}
        for ruolo, conteggio, spesa in righe:
            if ruolo in ROSA:
                quantita[ruolo] = conteggio
                speso_ruolo[ruolo] = spesa
        acquisti = self.db.execute("""
            SELECT g.id, g.ruolo, g.nome, g.squadra,
                   COALESCE((SELECT categoria FROM tag_asta t WHERE t.giocatore_id=g.id ORDER BY posizione LIMIT 1), 'Da assegnare'),
                   a.prezzo, g.foto_locale,
                   COALESCE(d.dati_json, (
                       SELECT d2.dati_json FROM dati_reali_api d2
                       JOIN giocatori g2 ON g2.id=d2.giocatore_id
                       WHERE g2.squadra=g.squadra LIMIT 1
                   ))
            FROM acquisti_lega a JOIN giocatori g ON g.id=a.giocatore_id
            LEFT JOIN dati_reali_api d ON d.giocatore_id=g.id
            WHERE a.fantallenatore_id=?
            ORDER BY CASE g.ruolo WHEN 'P' THEN 1 WHEN 'D' THEN 2 WHEN 'C' THEN 3 WHEN 'A' THEN 4 ELSE 5 END, g.nome
        """, (fantallenatore_id,)).fetchall()
        speso = sum(speso_ruolo.values())
        return crediti - speso, speso, quantita, speso_ruolo, acquisti

    def massimo_offerta(self, fantallenatore_id: int, ruolo: str) -> int:
        residuo, _, quantita, _, _ = self.riepilogo_fantallenatore(fantallenatore_id)
        if ruolo not in ROSA or quantita[ruolo] >= ROSA[ruolo]:
            return 0
        slot_mancanti = sum(ROSA[codice] - quantita[codice] for codice in ROSA)
        return max(0, residuo - max(slot_mancanti - 1, 0))

    @staticmethod
    def testo_fabbisogni(quantita: dict[str, int]) -> str:
        mancanti = [f"{ruolo} {ROSA[ruolo] - quantita[ruolo]}" for ruolo in ROSA if ROSA[ruolo] > quantita[ruolo]]
        return "Rosa completa" if not mancanti else "Fabbisogni: " + " · ".join(mancanti)

    def salva_modifica_asta(self) -> None:
        self.db.commit()
        try:
            crea_backup_asta(self.db)
            messaggio = "Asta salvata con backup locale."
        except sqlite3.Error:
            messaggio = "Asta salvata, ma backup non riuscito."
        self.aggiorna_budget()
        self.aggiorna_elenco()
        self.aggiorna_rose_aperte()
        self.mostra_feedback(messaggio)

    def rimuovi_acquisto_id(self, giocatore_id: int) -> bool:
        acquisto = self.db.execute("SELECT fantallenatore_id, prezzo FROM acquisti_lega WHERE giocatore_id=?", (giocatore_id,)).fetchone()
        if not acquisto:
            return False
        self.db.execute("DELETE FROM acquisti_lega WHERE giocatore_id=?", (giocatore_id,))
        self.db.execute("INSERT INTO cronologia_asta(azione, giocatore_id, fantallenatore_id, prezzo, registrato_il) VALUES ('rimozione', ?, ?, ?, ?)",
                        (giocatore_id, acquisto[0], acquisto[1], datetime.now().isoformat(timespec="seconds")))
        self.salva_modifica_asta()
        return True

    def annulla_ultima_operazione(self) -> None:
        movimento = self.db.execute("SELECT id, azione, giocatore_id, fantallenatore_id, prezzo FROM cronologia_asta ORDER BY id DESC LIMIT 1").fetchone()
        if not movimento:
            messagebox.showinfo("Asta", "Non ci sono operazioni da annullare.")
            return
        if movimento[1] == "acquisto":
            self.db.execute("DELETE FROM acquisti_lega WHERE giocatore_id=?", (movimento[2],))
        else:
            self.db.execute("INSERT OR IGNORE INTO acquisti_lega VALUES (?, ?, ?, ?)",
                            (movimento[2], movimento[3], movimento[4], datetime.now().isoformat(timespec="seconds")))
        self.db.execute("DELETE FROM cronologia_asta WHERE id=?", (movimento[0],))
        self.salva_modifica_asta()
        self.mostra_giocatore()

    def aggiorna_rose_aperte(self) -> None:
        finestre_attive = []
        for finestra, aggiorna in self.rose_aperte:
            try:
                if finestra.winfo_exists():
                    aggiorna()
                    finestre_attive.append((finestra, aggiorna))
            except tk.TclError:
                continue
        self.rose_aperte = finestre_attive

    def apri_rose_lega(self) -> None:
        finestra = Toplevel(self.radice)
        finestra.title("Rose della lega")
        finestra.geometry("1200x650")
        finestra.minsize(700, 440)
        testata = ttk.Frame(finestra, padding=(16, 12, 16, 4))
        testata.pack(fill="x")
        ttk.Label(testata, text="Rose della lega", style="Titolo.TLabel").pack(side="left")
        gestione = ttk.Frame(finestra, padding=(16, 4))
        gestione.pack(fill="x")
        ttk.Label(gestione, text="Nome fantallenatore").pack(side="left")
        nome = StringVar()
        campo = ttk.Entry(gestione, textvariable=nome, width=28)
        campo.pack(side="left", padx=8)
        squadra_da_rimuovere = StringVar()
        notebook = ttk.Notebook(finestra)
        notebook.pack(fill="both", expand=True, padx=16, pady=(4, 16))
        vista_rose = ttk.Frame(notebook, padding=10)
        registro = ttk.Frame(notebook, padding=10)
        notebook.add(vista_rose, text="Rose affiancate")
        notebook.add(registro, text="Registro asta")
        immagini_rose = []

        def righe_registro() -> list[tuple]:
            return self.db.execute("""
                SELECT a.registrato_il, f.nome, g.ruolo, g.nome, g.squadra,
                       COALESCE((SELECT categoria FROM tag_asta t
                                 WHERE t.giocatore_id=g.id ORDER BY posizione LIMIT 1), 'Da assegnare'),
                       a.prezzo
                FROM acquisti_lega a
                JOIN fantallenatori f ON f.id=a.fantallenatore_id
                JOIN giocatori g ON g.id=a.giocatore_id
                ORDER BY a.registrato_il, a.rowid
            """).fetchall()

        def esporta_registro() -> None:
            percorso = filedialog.asksaveasfilename(
                parent=finestra, title="Esporta registro asta", defaultextension=".csv",
                initialfile="registro_asta.csv", filetypes=[("File CSV", "*.csv"), ("Tutti i file", "*.*")],
            )
            if not percorso:
                return
            try:
                with open(percorso, "w", encoding="utf-8-sig", newline="") as file_csv:
                    scrittore = csv.writer(file_csv, delimiter=";")
                    scrittore.writerow(("Data", "Fantallenatore", "Ruolo", "Calciatore", "Squadra Serie A", "Fascia", "Prezzo"))
                    for data, fantallenatore, ruolo, giocatore, squadra, fascia, prezzo in righe_registro():
                        scrittore.writerow((self.formato_data(data), fantallenatore, ruolo, giocatore, squadra or "", fascia, prezzo))
                self.stato.set("Registro asta esportato.")
            except OSError as errore:
                messagebox.showerror("Esporta registro", f"Impossibile salvare il file.\n{errore}", parent=finestra)

        def esporta_rose() -> None:
            percorso = filedialog.asksaveasfilename(
                parent=finestra, title="Esporta rose della lega", defaultextension=".csv",
                initialfile="rose_lega.csv", filetypes=[("File CSV", "*.csv"), ("Tutti i file", "*.*")],
            )
            if not percorso:
                return
            try:
                with open(percorso, "w", encoding="utf-8-sig", newline="") as file_csv:
                    scrittore = csv.writer(file_csv, delimiter=";")
                    scrittore.writerow(("Fantallenatore", "Ruolo", "Calciatore", "Squadra Serie A", "Fascia", "Prezzo"))
                    for _, fantallenatore, ruolo, giocatore, squadra, fascia, prezzo in righe_registro():
                        scrittore.writerow((fantallenatore, ruolo, giocatore, squadra or "", fascia, prezzo))
                self.stato.set("Rose della lega esportate.")
            except OSError as errore:
                messagebox.showerror("Esporta rose", f"Impossibile salvare il file.\n{errore}", parent=finestra)

        ttk.Button(testata, text="Esporta rose CSV", command=esporta_rose).pack(side="right")

        def aggiorna_schede() -> None:
            for contenitore in (vista_rose, registro):
                for figlio in contenitore.winfo_children():
                    figlio.destroy()
            immagini_rose.clear()
            fantallenatori = self.db.execute("SELECT id, nome, e_mio FROM fantallenatori ORDER BY e_mio DESC, nome").fetchall()
            avversari = [(identita, nome_fantallenatore) for identita, nome_fantallenatore, e_mio in fantallenatori if not e_mio]
            selettore_rimozione.configure(values=[nome_fantallenatore for _, nome_fantallenatore in avversari])
            if squadra_da_rimuovere.get() not in {nome_fantallenatore for _, nome_fantallenatore in avversari}:
                squadra_da_rimuovere.set(avversari[0][1] if avversari else "")

            area_rose = ttk.Frame(vista_rose)
            area_rose.pack(fill="both", expand=True)
            tela_rose = tk.Canvas(area_rose, highlightthickness=0)
            barra_orizzontale = ttk.Scrollbar(area_rose, orient="horizontal", command=tela_rose.xview)
            barra_verticale = ttk.Scrollbar(area_rose, orient="vertical", command=tela_rose.yview)
            colonne_rose = ttk.Frame(tela_rose)
            tela_rose.create_window((0, 0), window=colonne_rose, anchor="nw")
            colonne_rose.bind("<Configure>", lambda _: tela_rose.configure(scrollregion=tela_rose.bbox("all")))
            tela_rose.configure(xscrollcommand=barra_orizzontale.set, yscrollcommand=barra_verticale.set)
            self.abilita_rotellina(tela_rose, consenti_orizzontale=True, contenuto=colonne_rose)
            tela_rose.grid(row=0, column=0, sticky="nsew")
            barra_verticale.grid(row=0, column=1, sticky="ns")
            barra_orizzontale.grid(row=1, column=0, sticky="ew")
            area_rose.rowconfigure(0, weight=1)
            area_rose.columnconfigure(0, weight=1)

            def apri_scheda_giocatore(_evento=None, tabella=None) -> None:
                selezione = tabella.selection()
                if not selezione or not selezione[0].startswith("giocatore-"):
                    return
                giocatore_id = int(selezione[0].removeprefix("giocatore-"))
                if self.tabella.exists(str(giocatore_id)):
                    self.tabella.selection_set(str(giocatore_id))
                    self.tabella.focus(str(giocatore_id))
                self.mostra_giocatore(identita=giocatore_id)

            nomi_ruolo = {"P": "Portieri", "D": "Difensori", "C": "Centrocampisti", "A": "Attaccanti"}
            for indice, (identita, nome_fantallenatore, e_mio) in enumerate(fantallenatori):
                scheda = ttk.LabelFrame(colonne_rose, text=nome_fantallenatore + (" · mia" if e_mio else ""), padding=8)
                scheda.grid(row=indice // 4, column=indice % 4, sticky="ns", padx=4, pady=4)
                residuo, speso, quantita, speso_ruolo, acquisti = self.riepilogo_fantallenatore(identita)
                ttk.Label(scheda, text=f"Crediti: {residuo}/600 · Spesi: {speso}", font=("Sans", 10, "bold")).pack(anchor="w")
                ttk.Label(scheda, text=" · ".join(f"{ruolo} {quantita[ruolo]}/{ROSA[ruolo]}" for ruolo in ROSA), style="Sottotitolo.TLabel").pack(anchor="w", pady=(3, 0))
                massimo = max((self.massimo_offerta(identita, ruolo) for ruolo in ROSA if quantita[ruolo] < ROSA[ruolo]), default=0)
                ttk.Label(scheda, text=f"{self.testo_fabbisogni(quantita)} · Max: {massimo} cr", style="Sottotitolo.TLabel", wraplength=440).pack(anchor="w", pady=(2, 6))
                contenitore = ttk.Frame(scheda)
                contenitore.pack(fill="both", expand=True)
                tabella = ttk.Treeview(contenitore, columns=("ruolo", "nome", "squadra", "fascia", "prezzo"), show=("tree", "headings"), height=12)
                tabella.heading("#0", text="")
                tabella.column("#0", width=42, minwidth=42, stretch=False, anchor="center")
                for codice, titolo, larghezza in (("ruolo", "R", 34), ("nome", "Calciatore", 135), ("squadra", "Squadra", 82), ("fascia", "Fascia", 110), ("prezzo", "Cr", 48)):
                    tabella.heading(codice, text=titolo)
                    tabella.column(codice, width=larghezza, anchor="w" if codice in {"nome", "squadra", "fascia"} else "center")
                tabella.tag_configure("intestazione_ruolo", background="#eaf2ff", font=("Sans", 10, "bold"))
                for fascia, colore in COLORI_FASCE.items():
                    tabella.tag_configure(fascia, background=colore)
                tabella.bind("<<TreeviewSelect>>", lambda evento, tabella=tabella: apri_scheda_giocatore(evento, tabella))
                def aggiorna_cursore_rosa(evento, tabella=tabella) -> None:
                    elemento = tabella.identify_row(evento.y)
                    tabella.configure(cursor="hand2" if elemento.startswith("giocatore-") else "")
                tabella.bind("<Motion>", aggiorna_cursore_rosa)
                tabella.bind("<Leave>", lambda _, tabella=tabella: tabella.configure(cursor=""))
                for ruolo in ROSA:
                    tabella.insert("", END, values=(ruolo, f"{nomi_ruolo[ruolo]} · {quantita[ruolo]}/{ROSA[ruolo]}", "", "", f"{speso_ruolo[ruolo]} cr"), tags=("intestazione_ruolo",))
                    for giocatore_id, ruolo_acquisto, giocatore, squadra, fascia, prezzo, foto_locale, dati_squadra in acquisti:
                        if ruolo_acquisto == ruolo:
                            icona = self.icona_rosa(foto_locale, dati_squadra, squadra)
                            if icona:
                                immagini_rose.append(icona)
                            tabella.insert("", END, iid=f"giocatore-{giocatore_id}", image=icona, values=(ruolo, giocatore, squadra or "—", fascia, prezzo), tags=(fascia,))
                barra = ttk.Scrollbar(contenitore, orient="vertical", command=tabella.yview)
                tabella.configure(yscrollcommand=barra.set)
                tabella.pack(side="left", fill="both", expand=True)
                barra.pack(side="right", fill="y")

                def rimuovi_giocatore_selezionato(tabella=tabella) -> None:
                    selezione = tabella.selection()
                    if not selezione or not selezione[0].startswith("giocatore-"):
                        messagebox.showinfo("Rose della lega", "Seleziona un giocatore, non l'intestazione del ruolo.", parent=finestra)
                        return
                    giocatore_id = int(selezione[0].removeprefix("giocatore-"))
                    nome_giocatore = tabella.item(selezione[0], "values")[1]
                    if messagebox.askyesno("Rimuovi giocatore", f"Rimuovere {nome_giocatore} dalla rosa?", parent=finestra):
                        self.rimuovi_acquisto_id(giocatore_id)

                ttk.Button(scheda, text="Rimuovi giocatore", command=rimuovi_giocatore_selezionato).pack(anchor="e", pady=(6, 0))

            righe = righe_registro()
            totale_speso = sum(riga[6] for riga in righe)
            media = totale_speso / len(righe) if righe else 0
            testata_registro = ttk.Frame(registro)
            testata_registro.pack(fill="x")
            ttk.Label(testata_registro, text=f"Acquisti: {len(righe)} · Spesa totale: {totale_speso} cr · Prezzo medio: {self.formato(media)} cr", font=("Sans", 11, "bold")).pack(side="left")
            ttk.Button(testata_registro, text="Esporta CSV", command=esporta_registro).pack(side="right")
            riepiloghi = ttk.Frame(registro)
            riepiloghi.pack(fill="x", pady=(10, 8))
            per_ruolo = {ruolo: [] for ruolo in ROSA}
            per_fascia = {}
            for _, _, ruolo, _, _, fascia, prezzo in righe:
                per_ruolo.setdefault(ruolo, []).append(prezzo)
                per_fascia.setdefault(fascia, []).append(prezzo)
            for colonna, (titolo, valori) in enumerate((("Per ruolo", per_ruolo), ("Per fascia", per_fascia))):
                riquadro = ttk.LabelFrame(riepiloghi, text=titolo, padding=5)
                riquadro.grid(row=0, column=colonna, sticky="nsew", padx=(0, 5) if colonna == 0 else (5, 0))
                tabella_riepilogo = ttk.Treeview(riquadro, columns=("voce", "acquisti", "spesa", "media"), show="headings", height=5)
                for codice, intestazione, larghezza in (("voce", "Ruolo" if colonna == 0 else "Fascia", 170), ("acquisti", "Acq.", 55), ("spesa", "Spesa", 70), ("media", "Media", 70)):
                    tabella_riepilogo.heading(codice, text=intestazione)
                    tabella_riepilogo.column(codice, width=larghezza, anchor="w" if codice == "voce" else "center")
                ordinamento = (lambda voce: list(ROSA).index(voce) if voce in ROSA else 99) if colonna == 0 else (lambda voce: ORDINE_FASCE.get(voce, 99))
                for voce in sorted(valori, key=ordinamento):
                    prezzi = valori[voce]
                    tabella_riepilogo.insert("", END, values=(voce, len(prezzi), sum(prezzi), self.formato(sum(prezzi) / len(prezzi)) if prezzi else "—"))
                tabella_riepilogo.pack(fill="x")
                riepiloghi.columnconfigure(colonna, weight=1)
            ttk.Label(registro, text="Cronologia degli acquisti", font=("Sans", 10, "bold")).pack(anchor="w", pady=(0, 4))
            contenitore_registro = ttk.Frame(registro)
            contenitore_registro.pack(fill="both", expand=True)
            tabella_registro = ttk.Treeview(contenitore_registro, columns=("data", "fantallenatore", "ruolo", "giocatore", "squadra", "fascia", "prezzo"), show="headings")
            for codice, intestazione, larghezza in (("data", "Data", 125), ("fantallenatore", "Fantallenatore", 110), ("ruolo", "Ruolo", 52), ("giocatore", "Calciatore", 165), ("squadra", "Squadra", 105), ("fascia", "Fascia", 155), ("prezzo", "Prezzo", 65)):
                tabella_registro.heading(codice, text=intestazione)
                tabella_registro.column(codice, width=larghezza, anchor="w" if codice in {"data", "fantallenatore", "giocatore", "squadra", "fascia"} else "center")
            for data, fantallenatore, ruolo, giocatore, squadra, fascia, prezzo in righe:
                tabella_registro.insert("", END, values=(self.formato_data(data), fantallenatore, ruolo, giocatore, squadra or "—", fascia, prezzo), tags=(fascia,))
            for fascia, colore in COLORI_FASCE.items():
                tabella_registro.tag_configure(fascia, background=colore)
            barra_verticale = ttk.Scrollbar(contenitore_registro, orient="vertical", command=tabella_registro.yview)
            barra_orizzontale = ttk.Scrollbar(contenitore_registro, orient="horizontal", command=tabella_registro.xview)
            tabella_registro.configure(yscrollcommand=barra_verticale.set, xscrollcommand=barra_orizzontale.set)
            tabella_registro.grid(row=0, column=0, sticky="nsew")
            barra_verticale.grid(row=0, column=1, sticky="ns")
            barra_orizzontale.grid(row=1, column=0, sticky="ew")
            contenitore_registro.rowconfigure(0, weight=1)
            contenitore_registro.columnconfigure(0, weight=1)

        def aggiungi_fantallenatore() -> None:
            valore = nome.get().strip()
            if not valore:
                messagebox.showerror("Rose della lega", "Inserisci il nome del fantallenatore.", parent=finestra)
                return
            try:
                self.db.execute("INSERT INTO fantallenatori(nome, crediti_iniziali) VALUES (?, 600)", (valore,))
            except sqlite3.IntegrityError:
                messagebox.showerror("Rose della lega", "Questo fantallenatore è già presente.", parent=finestra)
                return
            nome.set("")
            self.salva_modifica_asta()

        def rimuovi_fantallenatore() -> None:
            nome_squadra = squadra_da_rimuovere.get()
            if not nome_squadra:
                messagebox.showinfo("Rose della lega", "Seleziona una squadra da rimuovere.", parent=finestra)
                return
            fantallenatore = self.db.execute("SELECT id, nome, e_mio FROM fantallenatori WHERE nome=?", (nome_squadra,)).fetchone()
            if fantallenatore is None:
                return
            identita, nome_squadra, e_mio = fantallenatore
            if e_mio:
                messagebox.showerror("Rose della lega", "La tua squadra non può essere rimossa.", parent=finestra)
                return
            acquisti = self.db.execute("SELECT COUNT(*) FROM acquisti_lega WHERE fantallenatore_id=?", (identita,)).fetchone()[0]
            if acquisti:
                messagebox.showerror("Rose della lega", "Rimuovi prima gli acquisti di questa squadra oppure assegnali a un altro fantallenatore.", parent=finestra)
                return
            if not messagebox.askyesno("Rimuovi squadra", f"Rimuovere {nome_squadra} dalla lega?", parent=finestra):
                return
            self.db.execute("DELETE FROM fantallenatori WHERE id=?", (identita,))
            self.salva_modifica_asta()

        def rinomina_mia_squadra() -> None:
            valore = nome.get().strip()
            if not valore:
                messagebox.showerror("Rose della lega", "Inserisci il nuovo nome della tua squadra.", parent=finestra)
                return
            try:
                self.db.execute("UPDATE fantallenatori SET nome=? WHERE e_mio=1", (valore,))
            except sqlite3.IntegrityError:
                messagebox.showerror("Rose della lega", "Questo fantallenatore è già presente.", parent=finestra)
                return
            nome.set("")
            self.salva_modifica_asta()

        ttk.Button(gestione, text="Aggiungi", command=aggiungi_fantallenatore).pack(side="left")
        ttk.Button(gestione, text="Rinomina la mia squadra", command=rinomina_mia_squadra).pack(side="left", padx=6)
        ttk.Label(gestione, text="Rimuovi").pack(side="left", padx=(14, 0))
        selettore_rimozione = ttk.Combobox(gestione, textvariable=squadra_da_rimuovere, width=16, state="readonly")
        selettore_rimozione.pack(side="left", padx=6)
        ttk.Button(gestione, text="Rimuovi squadra", command=rimuovi_fantallenatore).pack(side="left")
        campo.bind("<Return>", lambda _: aggiungi_fantallenatore())
        self.rose_aperte.append((finestra, aggiorna_schede))
        aggiorna_schede()

        def chiudi() -> None:
            self.rose_aperte = [(aperta, aggiorna) for aperta, aggiorna in self.rose_aperte if aperta != finestra]
            finestra.destroy()

        finestra.protocol("WM_DELETE_WINDOW", chiudi)

    def squadre_portieri_miei(self, squadre: list[str]) -> list[str]:
        """Restituisce i codici delle squadre dei portieri già nella mia rosa."""
        righe = self.db.execute("""
            SELECT DISTINCT g.squadra
            FROM acquisti_lega a
            JOIN fantallenatori f ON f.id=a.fantallenatore_id
            JOIN giocatori g ON g.id=a.giocatore_id
            WHERE f.e_mio=1 AND g.ruolo=? AND g.squadra IS NOT NULL
        """, ("P",)).fetchall()
        squadre_mie = {normalizza(riga[0]) for riga in righe if riga[0]}
        return [codice for codice in squadre if normalizza(NOMI_GRIGLIA.get(codice, codice)) in squadre_mie]

    def mostra_dettaglio_abbinamento(self, contenitore, combinazione: tuple[str, ...], calendario: dict[int, dict[str, str]]) -> None:
        """Disegna il mini-calendario della combinazione selezionata, senza scrolling."""
        for elemento in contenitore.winfo_children():
            elemento.destroy()
        nomi = " + ".join(NOMI_GRIGLIA.get(codice, codice) for codice in combinazione)
        ttk.Label(contenitore, text=nomi, font=("Sans", 10, "bold")).pack(anchor="w")
        ttk.Label(
            contenitore,
            text="38 giornate · verde: almeno due alternative sicure · giallo: una · rosso: nessuna contro top/semitop.",
            style="Sottotitolo.TLabel",
        ).pack(anchor="w", pady=(0, 4))
        tessere = ttk.Frame(contenitore)
        tessere.pack(anchor="w")
        for indice, giornata in enumerate(sorted(calendario)):
            avversarie = [(codice, calendario[giornata].get(codice, "—")) for codice in combinazione]
            sicure = [(codice, avversaria) for codice, avversaria in avversarie if avversaria not in SQUADRE_FORTI]
            colore = "#d1fadf" if len(sicure) >= 2 else "#fef0c7" if sicure else "#fecdca"
            testo = f"{giornata}ª\n{len(sicure)}/{len(combinazione)}"
            descrizione = " · ".join(
                f"{NOMI_GRIGLIA.get(codice, codice)}–{NOMI_GRIGLIA.get(avversaria, avversaria)}"
                for codice, avversaria in avversarie
            )
            scelta = ", ".join(NOMI_GRIGLIA.get(codice, codice) for codice, _ in sicure) or "nessuna"
            descrizione = f"Giornata {giornata}: {descrizione}. Alternative sicure: {scelta}."
            tessera = tk.Label(tessere, text=testo, width=3, background=colore, foreground="#1d2939", font=("Sans", 8, "bold"), padx=3, pady=2)
            tessera.grid(row=indice // 19, column=indice % 19, padx=1, pady=1)
            tessera.bind("<Enter>", lambda _, testo=descrizione, widget=tessera: self.suggerimento.mostra_sotto(widget, testo))
            tessera.bind("<Leave>", lambda _: self.suggerimento.nascondi())

    def aggiungi_lista_incroci(self, contenitore, combinazioni_punteggi: list[tuple[tuple[str, ...], int]], calendario: dict[int, dict[str, str]]) -> None:
        """Mostra le combinazioni principali e il dettaglio di quella selezionata."""
        ttk.Label(contenitore, text="Punteggio basso = meno sovrapposizioni casalinghe. Seleziona una riga per vedere le 38 giornate.", style="Sottotitolo.TLabel").pack(anchor="w", padx=8, pady=(8, 3))
        pannelli = ttk.Frame(contenitore)
        pannelli.pack(fill="x", padx=8)
        dettaglio = ttk.LabelFrame(contenitore, text="Mini-calendario", padding=(8, 5))
        dettaglio.pack(fill="x", padx=8, pady=(6, 8))
        ttk.Label(dettaglio, text="Seleziona un abbinamento nelle tabelle qui sopra.", style="Sottotitolo.TLabel").pack(anchor="w")
        gruppi = (("Migliori abbinamenti", combinazioni_punteggi[:10]), ("Peggiori abbinamenti", list(reversed(combinazioni_punteggi[-10:]))))
        for indice, (titolo, righe) in enumerate(gruppi):
            riquadro = ttk.LabelFrame(pannelli, text=titolo, padding=5)
            riquadro.grid(row=0, column=indice, sticky="nsew", padx=(0, 4) if indice == 0 else (4, 0))
            tabella = ttk.Treeview(riquadro, columns=("abbinamento", "punteggio"), show="headings", height=10)
            tabella.heading("abbinamento", text="Squadre")
            tabella.heading("punteggio", text="Punti")
            tabella.column("abbinamento", width=155, anchor="w")
            tabella.column("punteggio", width=55, anchor="center", stretch=False)
            selezioni = {}
            for numero, (combinazione, punteggio) in enumerate(righe):
                nomi = " + ".join(NOMI_GRIGLIA.get(codice, codice) for codice in combinazione)
                identita = str(numero)
                selezioni[identita] = combinazione
                tabella.insert("", END, iid=identita, values=(nomi, punteggio))
            def mostra_selezione(_, albero=tabella, mappa=selezioni):
                selezione = albero.selection()
                if selezione:
                    self.mostra_dettaglio_abbinamento(dettaglio, mappa[selezione[0]], calendario)
            tabella.bind("<<TreeviewSelect>>", mostra_selezione)
            tabella.pack(fill="x", expand=True)
            pannelli.columnconfigure(indice, weight=1)

    def aggiungi_lista_trii(self, contenitore, valutazioni: list[tuple[tuple[str, ...], int, int]], calendario: dict[int, dict[str, str]]) -> None:
        ttk.Label(
            contenitore,
            text="Migliore = più giornate con almeno un portiere che non affronta top o semitop. Seleziona una riga per il dettaglio.",
            style="Sottotitolo.TLabel",
        ).pack(anchor="w", padx=8, pady=(8, 3))
        pannelli = ttk.Frame(contenitore)
        pannelli.pack(fill="x", padx=8)
        dettaglio = ttk.LabelFrame(contenitore, text="Mini-calendario", padding=(8, 5))
        dettaglio.pack(fill="x", padx=8, pady=(6, 8))
        ttk.Label(dettaglio, text="Seleziona un abbinamento nelle tabelle qui sopra.", style="Sottotitolo.TLabel").pack(anchor="w")
        migliori = valutazioni[:10]
        peggiori = sorted(valutazioni, key=lambda riga: (riga[1], -riga[2]), reverse=True)[:10]
        for indice, (titolo, righe) in enumerate((("Migliori abbinamenti", migliori), ("Peggiori abbinamenti", peggiori))):
            riquadro = ttk.LabelFrame(pannelli, text=titolo, padding=5)
            riquadro.grid(row=0, column=indice, sticky="nsew", padx=(0, 4) if indice == 0 else (4, 0))
            tabella = ttk.Treeview(riquadro, columns=("abbinamento", "scoperte", "sicure"), show="headings", height=10)
            tabella.heading("abbinamento", text="Squadre")
            tabella.heading("scoperte", text="Senza scelta")
            tabella.heading("sicure", text="Sicure")
            tabella.column("abbinamento", width=135, anchor="w")
            tabella.column("scoperte", width=85, anchor="center", stretch=False)
            tabella.column("sicure", width=55, anchor="center", stretch=False)
            selezioni = {}
            for numero, (combinazione, scoperte, sicure) in enumerate(righe):
                nomi = " + ".join(NOMI_GRIGLIA.get(codice, codice) for codice in combinazione)
                identita = str(numero)
                selezioni[identita] = combinazione
                tabella.insert("", END, iid=identita, values=(nomi, scoperte, sicure))
            def mostra_selezione(_, albero=tabella, mappa=selezioni):
                selezione = albero.selection()
                if selezione:
                    self.mostra_dettaglio_abbinamento(dettaglio, mappa[selezione[0]], calendario)
            tabella.bind("<<TreeviewSelect>>", mostra_selezione)
            tabella.pack(fill="x", expand=True)
            pannelli.columnconfigure(indice, weight=1)

    def apri_griglia_portieri(self) -> None:
        if not GRIGLIA_PORTIERI_PATH.exists():
            messagebox.showerror("Griglia portieri", "Non trovo il file della griglia portieri nella cartella prevista.")
            return
        try:
            squadre, matrice = leggi_griglia_portieri()
            calendario = leggi_calendario_portieri()
        except (OSError, ValueError, KeyError, zipfile.BadZipFile) as errore:
            messagebox.showerror("Griglia portieri", f"Non riesco a leggere la griglia: {errore}")
            return
        finestra = Toplevel(self.radice)
        finestra.title("Griglia portieri")
        finestra.geometry("1000x640")
        finestra.minsize(760, 480)
        notebook = ttk.Notebook(finestra)
        notebook.pack(fill="both", expand=True, padx=12, pady=12)
        completa = ttk.Frame(notebook)
        notebook.add(completa, text="Griglia completa")
        ttk.Label(completa, text="Numero di sovrapposizioni di partite in casa: più basso è meglio.", style="Sottotitolo.TLabel").pack(anchor="w", padx=10, pady=(10, 4))
        contenitore = ttk.Frame(completa)
        contenitore.pack(fill="both", expand=True, padx=10, pady=(0, 10))
        colonne = ("squadra", *squadre)
        tabella = ttk.Treeview(contenitore, columns=colonne, show="headings")
        tabella.heading("squadra", text="Squadra")
        tabella.column("squadra", width=120, anchor="w", stretch=False)
        for squadra in squadre:
            tabella.heading(squadra, text=NOMI_GRIGLIA.get(squadra, squadra))
            tabella.column(squadra, width=70, anchor="center", stretch=False)
        for squadra in squadre:
            tabella.insert("", END, values=(NOMI_GRIGLIA.get(squadra, squadra), *[matrice.get(squadra, {}).get(avversaria, "—") for avversaria in squadre]))
        barra_v = ttk.Scrollbar(contenitore, orient="vertical", command=tabella.yview)
        barra_o = ttk.Scrollbar(contenitore, orient="horizontal", command=tabella.xview)
        tabella.configure(yscrollcommand=barra_v.set, xscrollcommand=barra_o.set)
        tabella.grid(row=0, column=0, sticky="nsew"); barra_v.grid(row=0, column=1, sticky="ns"); barra_o.grid(row=1, column=0, sticky="ew")
        contenitore.rowconfigure(0, weight=1); contenitore.columnconfigure(0, weight=1)
        tabella.grid_remove(); barra_v.grid_remove(); barra_o.grid_remove()

        legenda = ttk.Frame(completa)
        legenda.pack(fill="x", padx=10, pady=(0, 8), before=contenitore)
        ttk.Label(legenda, text="Legenda:", font=("Sans", 9, "bold")).pack(side="left", padx=(0, 6))
        for testo, colore in (("3–6 ottimo", "#d1fadf"), ("7–9 buono", "#fef0c7"), ("10–12 critico", "#fedf89"), ("13+ sfavorevole", "#fecdca")):
            tk.Label(legenda, text=testo, background=colore, foreground="#344054", padx=7, pady=3, font=("Sans", 9)).pack(side="left", padx=(0, 5))
        ttk.Label(legenda, text="Grigio = stessa squadra.", style="Sottotitolo.TLabel").pack(side="left", padx=(5, 0))

        tela_griglia = tk.Canvas(contenitore, highlightthickness=0, background="#ffffff")
        barra_colori_v = ttk.Scrollbar(contenitore, orient="vertical", command=tela_griglia.yview)
        barra_colori_o = ttk.Scrollbar(contenitore, orient="horizontal", command=tela_griglia.xview)
        tela_griglia.configure(yscrollcommand=barra_colori_v.set, xscrollcommand=barra_colori_o.set)
        corpo_griglia = tk.Frame(tela_griglia, background="#ffffff")
        tela_griglia.create_window((0, 0), window=corpo_griglia, anchor="nw")
        corpo_griglia.bind("<Configure>", lambda _: tela_griglia.configure(scrollregion=tela_griglia.bbox("all")))
        self.abilita_rotellina(tela_griglia, consenti_orizzontale=True, contenuto=corpo_griglia)
        tela_griglia.grid(row=0, column=0, sticky="nsew"); barra_colori_v.grid(row=0, column=1, sticky="ns"); barra_colori_o.grid(row=1, column=0, sticky="ew")

        dettaglio_portieri = ttk.LabelFrame(completa, text="Portieri delle squadre selezionate", padding=(8, 6))
        dettaglio_portieri.pack(fill="x", padx=10, pady=(0, 10))
        immagini_portieri: list[ImageTk.PhotoImage] = []
        immagini_stemmi_griglia: list[ImageTk.PhotoImage] = []

        def testo_verticale_griglia(codice: str) -> ImageTk.PhotoImage:
            nome = NOMI_GRIGLIA.get(codice, codice)
            try:
                font = ImageFont.truetype("/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf", 12)
            except OSError:
                font = ImageFont.load_default()
            riquadro = font.getbbox(nome)
            testo = Image.new("RGBA", (riquadro[2] - riquadro[0] + 6, riquadro[3] - riquadro[1] + 6), (0, 0, 0, 0))
            ImageDraw.Draw(testo).text((3 - riquadro[0], 3 - riquadro[1]), nome, font=font, fill="#1d2939")
            ruotato = testo.rotate(90, expand=True)
            risultato = ImageTk.PhotoImage(ruotato)
            immagini_stemmi_griglia.append(risultato)
            return risultato

        def immagine_stemma_griglia(codice: str, lato: int = 22) -> ImageTk.PhotoImage | None:
            percorso = self.percorso_stemma_squadra(NOMI_GRIGLIA.get(codice, codice))
            if not percorso:
                return None
            try:
                with Image.open(percorso) as sorgente:
                    immagine = sorgente.convert("RGBA")
                    filtro = Image.Resampling.LANCZOS if hasattr(Image, "Resampling") else Image.LANCZOS
                    immagine.thumbnail((lato, lato), filtro)
                    risultato = ImageTk.PhotoImage(immagine)
                immagini_stemmi_griglia.append(risultato)
                return risultato
            except (OSError, tk.TclError):
                return None

        celle_griglia: dict[tuple[str, str], tk.Label] = {}
        intestazioni_riga: dict[str, tk.Label] = {}
        intestazioni_colonna: dict[str, tk.Label] = {}
        selezione_righe: set[str] = set()
        selezione_colonne: set[str] = set()

        def colore_sovrapposizioni(valore, stessa_squadra: bool) -> str:
            if stessa_squadra or valore is None:
                return "#eaecf0"
            if valore <= 6:
                return "#d1fadf"
            if valore <= 9:
                return "#fef0c7"
            if valore <= 12:
                return "#fedf89"
            return "#fecdca"

        def immagine_portiere(percorso: str | None) -> ImageTk.PhotoImage:
            try:
                if percorso and Path(percorso).exists():
                    with Image.open(percorso) as sorgente:
                        immagine = sorgente.convert("RGBA")
                else:
                    immagine = self.sagoma_anonima(34)
                filtro = Image.Resampling.LANCZOS if hasattr(Image, "Resampling") else Image.LANCZOS
                immagine.thumbnail((34, 34), filtro)
                risultato = ImageTk.PhotoImage(immagine)
            except (OSError, tk.TclError):
                risultato = ImageTk.PhotoImage(self.sagoma_anonima(34))
            immagini_portieri.append(risultato)
            return risultato

        def aggiorna_portieri(codici: list[str]) -> None:
            for elemento in dettaglio_portieri.winfo_children():
                elemento.destroy()
            immagini_portieri.clear()
            if not codici:
                ttk.Label(dettaglio_portieri, text="Seleziona una squadra nella prima riga o colonna, oppure un incrocio nella matrice.", style="Sottotitolo.TLabel").pack(anchor="w")
                return
            riquadri = ttk.Frame(dettaglio_portieri)
            riquadri.pack(fill="x")
            for indice, codice in enumerate(dict.fromkeys(codici)):
                squadra = NOMI_GRIGLIA.get(codice, codice)
                riquadro = ttk.LabelFrame(riquadri, text=squadra, padding=5)
                riquadro.grid(row=0, column=indice, sticky="nsew", padx=(0, 6) if indice == 0 else 6)
                portieri = self.db.execute("""
                    SELECT g.nome, g.foto_locale, q.quotazione_attuale
                    FROM giocatori g
                    LEFT JOIN quotazioni_fanta q ON q.giocatore_id=g.id AND q.stagione='2026-27'
                    WHERE g.in_quotazioni_correnti=1 AND g.squadra=? AND g.ruolo='P'
                    ORDER BY q.quotazione_attuale DESC, g.nome
                """, (squadra,)).fetchall()
                if not portieri:
                    ttk.Label(riquadro, text="Nessun portiere disponibile.", style="Sottotitolo.TLabel").pack(anchor="w")
                for nome_portiere, foto_locale, quotazione in portieri:
                    scheda = ttk.Frame(riquadro)
                    scheda.pack(fill="x", pady=2)
                    ttk.Label(scheda, image=immagine_portiere(foto_locale)).pack(side="left", padx=(0, 5))
                    ttk.Label(scheda, text=nome_portiere).pack(side="left")
                    ttk.Label(scheda, text=f"QtA {self.formato(quotazione)}", font=("Sans", 9, "bold")).pack(side="left", padx=(8, 0))
                riquadri.columnconfigure(indice, weight=1)

        def aggiorna_evidenza() -> None:
            for (riga, colonna), cella in celle_griglia.items():
                evidenziata = riga in selezione_righe or colonna in selezione_colonne
                cella.configure(relief="solid" if evidenziata else "flat", borderwidth=2 if evidenziata else 0, highlightbackground="#155eef", highlightcolor="#155eef")
            for codice, intestazione in intestazioni_riga.items():
                intestazione.configure(background="#bfd7ff" if codice in selezione_righe else "#eaf2ff")
            for codice, intestazione in intestazioni_colonna.items():
                intestazione.configure(background="#bfd7ff" if codice in selezione_colonne else "#eaf2ff")

        def seleziona_cella(riga: str, colonna: str) -> None:
            selezione_righe.clear(); selezione_colonne.clear()
            selezione_righe.add(riga); selezione_colonne.add(colonna)
            aggiorna_evidenza(); aggiorna_portieri([riga, colonna])

        def seleziona_riga(codice: str) -> None:
            selezione_righe.clear(); selezione_colonne.clear()
            selezione_righe.add(codice)
            aggiorna_evidenza(); aggiorna_portieri([codice])

        def seleziona_colonna(codice: str) -> None:
            selezione_righe.clear(); selezione_colonne.clear()
            selezione_colonne.add(codice)
            aggiorna_evidenza(); aggiorna_portieri([codice])

        tk.Label(corpo_griglia, text="Squadra", width=15, background="#eaf2ff", foreground="#1d2939", font=("Sans", 9, "bold"), padx=4, pady=5).grid(row=0, column=0, sticky="nsew", padx=1, pady=1)
        for indice, squadra in enumerate(squadre, start=1):
            testo_ruotato = testo_verticale_griglia(squadra)
            intestazione = tk.Label(corpo_griglia, image=testo_ruotato, background="#eaf2ff", padx=5, pady=5, cursor="hand2")
            intestazione.image = testo_ruotato
            intestazione.grid(row=0, column=indice, sticky="nsew", padx=1, pady=1)
            intestazione.bind("<Button-1>", lambda _, codice=squadra: seleziona_colonna(codice))
            intestazioni_colonna[squadra] = intestazione
        for riga, squadra in enumerate(squadre, start=1):
            stemma = immagine_stemma_griglia(squadra, 20)
            intestazione = tk.Label(corpo_griglia, text=NOMI_GRIGLIA.get(squadra, squadra), image=stemma if stemma else "", compound="left", width=15, background="#eaf2ff", foreground="#1d2939", font=("Sans", 9, "bold"), padx=4, pady=5, anchor="w", cursor="hand2")
            intestazione.image = stemma
            intestazione.grid(row=riga, column=0, sticky="nsew", padx=1, pady=1)
            intestazione.bind("<Button-1>", lambda _, codice=squadra: seleziona_riga(codice))
            intestazioni_riga[squadra] = intestazione
            for colonna, avversaria in enumerate(squadre, start=1):
                valore = matrice.get(squadra, {}).get(avversaria)
                stessa_squadra = squadra == avversaria
                testo = "—" if stessa_squadra else (str(valore) if valore is not None else "—")
                sfondo = colore_sovrapposizioni(valore, stessa_squadra)
                cella = tk.Label(corpo_griglia, text=testo, width=7, background=sfondo, foreground="#1d2939", font=("Sans", 10, "bold"), padx=1, pady=3, cursor="hand2")
                cella.grid(row=riga, column=colonna, sticky="nsew", padx=1, pady=1)
                celle_griglia[(squadra, avversaria)] = cella
                descrizione = "Stessa squadra: abbinamento non applicabile." if stessa_squadra else f"{NOMI_GRIGLIA.get(squadra, squadra)} + {NOMI_GRIGLIA.get(avversaria, avversaria)}: {testo} sovrapposizioni di partite in casa."
                cella.bind("<Enter>", lambda evento, testo=descrizione, widget=cella: self.suggerimento.mostra_sotto(widget, testo))
                cella.bind("<Leave>", lambda _: self.suggerimento.nascondi())
                if not stessa_squadra:
                    cella.bind("<Button-1>", lambda _, riga=squadra, colonna=avversaria: seleziona_cella(riga, colonna))
        aggiorna_portieri([])

        for dimensione, titolo in ((2, "Abbinamenti a 2"), (3, "Abbinamenti a 3")):
            scheda = ttk.Frame(notebook)
            notebook.add(scheda, text=titolo)
            viste = ttk.Notebook(scheda)
            viste.pack(fill="both", expand=True)
            combinazioni = list(combinations(squadre, dimensione))
            if dimensione == 2:
                combinazioni_punteggi = []
                for combinazione in combinazioni:
                    try:
                        punteggio = matrice[combinazione[0]][combinazione[1]]
                    except KeyError:
                        continue
                    combinazioni_punteggi.append((combinazione, punteggio))
                combinazioni_punteggi.sort(key=lambda riga: (riga[1], riga[0]))
            else:
                combinazioni_punteggi = [
                    (combinazione, *valuta_trio_portieri(combinazione, calendario))
                    for combinazione in combinazioni
                ]
                combinazioni_punteggi.sort(key=lambda riga: (riga[1], -riga[2], riga[0]))
            filtri = [
                ("Tutte", combinazioni_punteggi),
                ("Con top squadre", [riga for riga in combinazioni_punteggi if any(codice in TOP_SQUADRE for codice in riga[0])]),
                ("Senza top squadre", [riga for riga in combinazioni_punteggi if not any(codice in TOP_SQUADRE for codice in riga[0])]),
            ]
            miei_codici = self.squadre_portieri_miei(squadre)
            if 0 < len(miei_codici) <= dimensione:
                richiesti = set(miei_codici)
                dalla_mia_rosa = [riga for riga in combinazioni_punteggi if richiesti.issubset(set(riga[0]))]
                if dalla_mia_rosa:
                    filtri.insert(0, ("Dalla mia rosa", dalla_mia_rosa))
            for etichetta, righe in filtri:
                vista = ttk.Frame(viste)
                viste.add(vista, text=etichetta)
                if dimensione == 2:
                    self.aggiungi_lista_incroci(vista, righe, calendario)
                else:
                    self.aggiungi_lista_trii(vista, righe, calendario)

    def apri_formazioni_tipo(self) -> None:
        finestra = Toplevel(self.radice)
        finestra.title("Formazioni tipo")
        finestra.geometry("940x700")
        finestra.minsize(880, 540)
        testata = ttk.Frame(finestra, padding=(16, 12, 16, 6))
        testata.pack(fill="x")
        ttk.Label(testata, text="Formazioni tipo e ballottaggi", style="Titolo.TLabel").pack(side="left")
        filtro_squadra = StringVar(value="Tutte")
        ttk.Label(testata, text="Squadra").pack(side="right", padx=(12, 4))
        scelta = ttk.Combobox(testata, values=["Tutte", *INFOGRAFICA_2026_27.keys()], textvariable=filtro_squadra, width=16, state="readonly")
        scelta.pack(side="right")

        contenitore = ttk.Frame(finestra)
        contenitore.pack(fill="both", expand=True, padx=16, pady=(0, 16))
        tela = tk.Canvas(contenitore, highlightthickness=0, background="#f8fafc")
        barra = ttk.Scrollbar(contenitore, orient="vertical", command=tela.yview)
        tela.configure(yscrollcommand=barra.set)
        tela.pack(side="left", fill="both", expand=True)
        barra.pack(side="right", fill="y")
        elenco = ttk.Frame(tela, padding=10)
        finestra_elenco = tela.create_window((0, 0), window=elenco, anchor="nw")
        elenco.bind("<Configure>", lambda _: tela.configure(scrollregion=tela.bbox("all")))
        self.abilita_rotellina(tela, contenuto=elenco)
        tela.bind("<Configure>", lambda evento: tela.itemconfigure(finestra_elenco, width=evento.width))

        immagini: list[ImageTk.PhotoImage] = []

        def immagine(percorso: str | None, lato: int) -> ImageTk.PhotoImage:
            try:
                if percorso and Path(percorso).exists():
                    with Image.open(percorso) as sorgente:
                        foto = sorgente.convert("RGBA")
                else:
                    foto = self.sagoma_anonima(lato)
                filtro = Image.Resampling.LANCZOS if hasattr(Image, "Resampling") else Image.LANCZOS
                foto.thumbnail((lato, lato), filtro)
                sfondo = Image.new("RGBA", (lato, lato), (255, 255, 255, 0))
                sfondo.alpha_composite(foto, ((lato - foto.width) // 2, (lato - foto.height) // 2))
                risultato = ImageTk.PhotoImage(sfondo)
                immagini.append(risultato)
                return risultato
            except OSError:
                risultato = ImageTk.PhotoImage(self.sagoma_anonima(lato))
                immagini.append(risultato)
                return risultato

        def stemma(squadra: str) -> ImageTk.PhotoImage | None:
            riga = self.db.execute("""
                SELECT d.dati_json FROM dati_reali_api d JOIN giocatori g ON g.id=d.giocatore_id
                WHERE g.squadra=? LIMIT 1
            """, (squadra,)).fetchone()
            if not riga:
                return None
            try:
                squadra_id = json.loads(riga[0]).get("team", {}).get("id")
            except (json.JSONDecodeError, AttributeError):
                return None
            percorso = STEMMI_DIR / f"{squadra_id}.png" if squadra_id else None
            return immagine(str(percorso) if percorso and percorso.exists() else None, 34) if percorso and percorso.exists() else None

        def coordinate(modulo: str) -> list[tuple[float, float]]:
            linee = [int(valore) for valore in modulo.split("-")]
            risultato = [(0.5, 0.88)]
            livelli = len(linee)
            for indice, quantita in enumerate(linee):
                y = .70 - indice * (.52 / max(livelli - 1, 1))
                risultato.extend(((posizione + 1) / (quantita + 1), y) for posizione in range(quantita))
            return risultato

        def apri_giocatore(identita: int) -> None:
            if self.tabella.exists(str(identita)):
                self.tabella.selection_set(str(identita))
                self.tabella.focus(str(identita))
            self.mostra_giocatore(identita=identita)

        def aggiorna() -> None:
            for elemento in elenco.winfo_children():
                elemento.destroy()
            immagini.clear()
            squadre = INFOGRAFICA_2026_27.items()
            if filtro_squadra.get() != "Tutte":
                squadre = ((filtro_squadra.get(), INFOGRAFICA_2026_27[filtro_squadra.get()]),)
            for squadra, dati in squadre:
                profili = {
                    normalizza(riga[1]): riga
                    for riga in self.db.execute("SELECT id, nome, ruolo, foto_locale FROM giocatori WHERE in_quotazioni_correnti=1 AND squadra=?", (squadra,))
                }
                riquadro = ttk.LabelFrame(elenco, text=squadra, padding=(12, 8))
                riquadro.pack(fill="x", pady=(0, 10))
                intestazione_squadra = ttk.Frame(riquadro)
                intestazione_squadra.pack(fill="x", pady=(0, 4))
                stemma_squadra = stemma(squadra)
                if stemma_squadra:
                    ttk.Label(intestazione_squadra, image=stemma_squadra).pack(side="left", padx=(0, 6))
                modulo = MODULI_FORMAZIONI[squadra]
                ttk.Label(intestazione_squadra, text=f"Formazione tipo · {modulo}", font=("Sans", 10, "bold")).pack(side="left")
                campo = tk.Canvas(riquadro, width=840, height=370, highlightthickness=0, background="#dfeeda")
                campo.pack(fill="x", pady=(0, 8))
                larghezza, altezza = 840, 370
                campo.create_rectangle(18, 12, larghezza - 18, altezza - 12, outline="#ffffff", width=2)
                campo.create_line(larghezza / 2, 12, larghezza / 2, altezza - 12, fill="#ffffff", width=2)
                campo.create_oval(larghezza / 2 - 42, altezza / 2 - 42, larghezza / 2 + 42, altezza / 2 + 42, outline="#ffffff", width=2)
                campo.create_rectangle(larghezza * .31, 12, larghezza * .69, 60, outline="#ffffff", width=2)
                campo.create_rectangle(larghezza * .31, altezza - 60, larghezza * .69, altezza - 12, outline="#ffffff", width=2)
                for (x, y), nome in zip(coordinate(modulo), dati["titolari"]):
                    profilo = profili.get(normalizza(nome))
                    nome_mostrato = profilo[1] if profilo else nome
                    ruolo = profilo[2] if profilo else "—"
                    foto = immagine(profilo[3] if profilo else None, 36)
                    px, py = 20 + x * (larghezza - 40), 10 + y * (altezza - 20)
                    tag = f"giocatore_{profilo[0]}" if profilo else ""
                    campo.create_oval(px - 22, py - 22, px + 22, py + 22, fill="#ffffff", outline="#1570ef", width=2, tags=(tag,))
                    campo.create_image(px, py, image=foto, tags=(tag,))
                    campo.create_text(px, py + 30, text=f"{nome_mostrato} ({ruolo})", font=("Sans", 8, "bold"), fill="#1d2939", width=128, tags=(tag,))
                    if profilo:
                        campo.tag_bind(tag, "<Button-1>", lambda _, identita=profilo[0]: apri_giocatore(identita))
                        campo.tag_bind(tag, "<Enter>", lambda _, canvas=campo: canvas.configure(cursor="hand2"))
                        campo.tag_bind(tag, "<Leave>", lambda _, canvas=campo: canvas.configure(cursor=""))
                ttk.Label(riquadro, text="Ballottaggi", font=("Sans", 10, "bold")).pack(anchor="w")
                if not dati["ballottaggi"]:
                    ttk.Label(riquadro, text="Nessun ballottaggio indicato.", style="Sottotitolo.TLabel").pack(anchor="w", pady=(2, 0))
                for titolare, alternativa in dati["ballottaggi"]:
                    riga = ttk.Frame(riquadro)
                    riga.pack(anchor="w", pady=(2, 0))
                    profilo_titolare = profili.get(normalizza(titolare))
                    profilo_alternativa = profili.get(normalizza(alternativa))
                    nome_titolare = profilo_titolare[1] if profilo_titolare else titolare
                    nome_alternativa = profilo_alternativa[1] if profilo_alternativa else alternativa
                    etichetta_titolare = ttk.Label(riga, text=nome_titolare, font=("Sans", 10, "bold"))
                    etichetta_titolare.pack(side="left")
                    if profilo_titolare:
                        etichetta_titolare.configure(cursor="hand2")
                        etichetta_titolare.bind("<Button-1>", lambda _, identita=profilo_titolare[0]: apri_giocatore(identita))
                    ttk.Label(riga, text=" in vantaggio su ").pack(side="left")
                    etichetta_alternativa = ttk.Label(riga, text=nome_alternativa)
                    etichetta_alternativa.pack(side="left")
                    if profilo_alternativa:
                        etichetta_alternativa.configure(cursor="hand2")
                        etichetta_alternativa.bind("<Button-1>", lambda _, identita=profilo_alternativa[0]: apri_giocatore(identita))

        scelta.bind("<<ComboboxSelected>>", lambda _: aggiorna())
        aggiorna()

    def modifica_fascia(self) -> None:
        identita = self.giocatore_selezionato()
        if identita is None:
            messagebox.showinfo("Fascia d'asta", "Seleziona prima un calciatore.")
            return
        giocatore = self.db.execute("SELECT nome FROM giocatori WHERE id=?", (identita,)).fetchone()
        tag = self.db.execute("SELECT rowid, categoria FROM tag_asta WHERE giocatore_id=? ORDER BY posizione LIMIT 1", (identita,)).fetchone()
        finestra = Toplevel(self.radice); finestra.title("Modifica fascia"); finestra.transient(self.radice); finestra.grab_set()
        ttk.Label(finestra, text=giocatore[0], style="Titolo.TLabel", padding=(16, 16, 16, 4)).pack(anchor="w")
        ttk.Label(finestra, text="Fascia d'asta", padding=(16, 4, 16, 2)).pack(anchor="w")
        fascia = StringVar(value=tag[1] if tag else "Da assegnare")
        scelta = ttk.Combobox(finestra, values=FASCE, textvariable=fascia, state="readonly", width=30)
        scelta.pack(padx=16, fill="x")

        def salva() -> None:
            try:
                if tag:
                    self.db.execute("UPDATE tag_asta SET categoria=? WHERE rowid=?", (fascia.get(), tag[0]))
                else:
                    posizione = self.db.execute("SELECT COALESCE(MAX(posizione), 0) + 1 FROM tag_asta").fetchone()[0]
                    self.db.execute("INSERT INTO tag_asta VALUES (?, ?, '', ?)", (identita, fascia.get(), posizione))
                self.db.commit()
            except sqlite3.IntegrityError:
                messagebox.showerror("Fascia d'asta", "Il giocatore possiede già questa fascia.", parent=finestra)
                return
            finestra.destroy()
            self.aggiorna_elenco()
            if self.tabella.exists(str(identita)):
                self.tabella.selection_set(str(identita))
                self.mostra_giocatore()

        ttk.Button(finestra, text="Salva", command=salva).pack(anchor="e", padx=16, pady=16)

    def registra_acquisto(self) -> None:
        identita = self.giocatore_selezionato()
        if identita is None:
            messagebox.showinfo("Asta", "Seleziona prima un calciatore.")
            return
        esito = self.db.execute("SELECT 1 FROM acquisti_lega WHERE giocatore_id=?", (identita,)).fetchone()
        if esito:
            messagebox.showerror("Asta", "Il calciatore non è più disponibile.")
            return
        giocatore = self.db.execute("SELECT nome, ruolo FROM giocatori WHERE id=?", (identita,)).fetchone()
        fantallenatori = self.db.execute("SELECT id, nome FROM fantallenatori ORDER BY e_mio DESC, nome").fetchall()
        finestra = Toplevel(self.radice); finestra.title("Registra esito asta"); finestra.transient(self.radice); finestra.grab_set()
        ttk.Label(finestra, text=giocatore[0], style="Titolo.TLabel", padding=(16, 16, 16, 4)).pack(anchor="w")
        ttk.Label(finestra, text="Fantallenatore", padding=(16, 4, 16, 2)).pack(anchor="w")
        scelta = StringVar(value=fantallenatori[0][1])
        ttk.Combobox(finestra, values=[riga[1] for riga in fantallenatori], textvariable=scelta, state="readonly", width=28).pack(padx=16, fill="x")
        ttk.Label(finestra, text="Prezzo", padding=(16, 10, 16, 2)).pack(anchor="w")
        prezzo = StringVar(value=self.prezzo_live.get()); campo = ttk.Entry(finestra, textvariable=prezzo); campo.pack(padx=16); campo.focus()
        def conferma():
            try: valore_prezzo = int(prezzo.get())
            except ValueError: messagebox.showerror("Prezzo non valido", "Inserisci un numero intero.", parent=finestra); return
            if valore_prezzo < 1:
                messagebox.showerror("Prezzo non valido", "Il prezzo deve essere almeno 1.", parent=finestra); return
            manager = next(riga for riga in fantallenatori if riga[1] == scelta.get())
            speso = self.db.execute("SELECT COALESCE(SUM(prezzo), 0) FROM acquisti_lega WHERE fantallenatore_id=?", (manager[0],)).fetchone()[0]
            crediti = self.db.execute("SELECT crediti_iniziali FROM fantallenatori WHERE id=?", (manager[0],)).fetchone()[0]
            conteggio_ruolo = self.db.execute("SELECT COUNT(*) FROM acquisti_lega a JOIN giocatori g ON g.id=a.giocatore_id WHERE a.fantallenatore_id=? AND g.ruolo=?", (manager[0], giocatore[1])).fetchone()[0]
            slot = self.db.execute("SELECT COUNT(*) FROM acquisti_lega WHERE fantallenatore_id=?", (manager[0],)).fetchone()[0]
            massimo = crediti - speso - (sum(ROSA.values()) - slot - 1)
            if conteggio_ruolo >= ROSA[giocatore[1]] or valore_prezzo > massimo:
                messagebox.showerror("Budget o slot", f"{manager[1]} non può registrare questo acquisto a {valore_prezzo} crediti.", parent=finestra); return
            self.db.execute("INSERT INTO acquisti_lega VALUES (?, ?, ?, ?)", (identita, manager[0], valore_prezzo, datetime.now().isoformat(timespec="seconds")))
            self.db.execute("INSERT INTO cronologia_asta(azione, giocatore_id, fantallenatore_id, prezzo, registrato_il) VALUES ('acquisto', ?, ?, ?, ?)",
                            (identita, manager[0], valore_prezzo, datetime.now().isoformat(timespec="seconds")))
            self.salva_modifica_asta(); self.prezzo_live.set(""); finestra.destroy(); self.mostra_giocatore(identita=identita)
        ttk.Button(finestra, text="Conferma", command=conferma).pack(pady=16)

    def acquista(self) -> None:
        self.registra_acquisto()

    def vendi_avversario(self) -> None:
        self.registra_acquisto()

    def rimuovi_acquisto(self) -> None:
        identita = self.giocatore_selezionato()
        if identita is None:
            return
        if self.rimuovi_acquisto_id(identita):
            self.mostra_giocatore(identita=identita)

    def alterna_preferito(self) -> None:
        identita = self.giocatore_selezionato()
        if identita is None:
            return
        self.db.execute("INSERT OR IGNORE INTO preferenze_giocatori(giocatore_id) VALUES (?)", (identita,))
        self.db.execute("UPDATE preferenze_giocatori SET preferito=1-preferito WHERE giocatore_id=?", (identita,))
        self.db.commit(); self.aggiorna_elenco(); self.mostra_giocatore()

    def alterna_escluso(self) -> None:
        identita = self.giocatore_selezionato()
        if identita is None:
            return
        self.db.execute("INSERT OR IGNORE INTO preferenze_giocatori(giocatore_id) VALUES (?)", (identita,))
        self.db.execute("UPDATE preferenze_giocatori SET escluso=1-escluso WHERE giocatore_id=?", (identita,))
        self.db.commit(); self.aggiorna_elenco(); self.mostra_giocatore()

    def modifica_nota(self) -> None:
        identita = self.giocatore_selezionato()
        if identita is None:
            return
        nota_attuale = self.db.execute("SELECT nota FROM preferenze_giocatori WHERE giocatore_id=?", (identita,)).fetchone()
        finestra = Toplevel(self.radice); finestra.title("Nota personale"); finestra.transient(self.radice); finestra.grab_set()
        nota = tk.Text(finestra, width=48, height=5, wrap="word")
        nota.pack(padx=16, pady=16); nota.insert("1.0", nota_attuale[0] if nota_attuale else "")
        def salva():
            self.db.execute("INSERT OR IGNORE INTO preferenze_giocatori(giocatore_id) VALUES (?)", (identita,))
            self.db.execute("UPDATE preferenze_giocatori SET nota=? WHERE giocatore_id=?", (nota.get("1.0", "end-1c").strip(), identita))
            self.db.commit(); finestra.destroy(); self.mostra_giocatore()
        ttk.Button(finestra, text="Salva", command=salva).pack(anchor="e", padx=16, pady=(0, 16))

    def aggiungi_confronto(self) -> None:
        identita = self.giocatore_selezionato()
        if identita is None:
            return
        if identita in self.confronto:
            messagebox.showinfo("Confronto", "Il calciatore è già nel confronto.")
            return
        if len(self.confronto) == 3:
            messagebox.showinfo("Confronto", "Puoi confrontare al massimo tre calciatori.")
            return
        self.confronto.append(identita)
        self.pulsante_confronto.configure(text=f"Confronto ({len(self.confronto)}/3)")

    def svuota_confronto(self) -> None:
        self.confronto.clear()
        self.pulsante_confronto.configure(text="Confronto (0/3)")

    def dati_confronto(self, giocatore_id: int) -> dict:
        giocatore = self.db.execute("SELECT nome, ruolo, squadra FROM giocatori WHERE id=?", (giocatore_id,)).fetchone()
        fascia = self.db.execute("SELECT categoria FROM tag_asta WHERE giocatore_id=? ORDER BY posizione LIMIT 1", (giocatore_id,)).fetchone()
        corrente = self.db.execute("""
            SELECT s.presenze, s.mv, s.fm, s.gol_fatti, s.assist, q.fvm
            FROM statistiche_fanta s LEFT JOIN quotazioni_fanta q ON q.giocatore_id=s.giocatore_id AND q.stagione=s.stagione
            WHERE s.giocatore_id=? AND s.stagione='2026-27'
        """, (giocatore_id,)).fetchone()
        storico = self.db.execute("""
            SELECT s.stagione, s.mv, s.fm, s.gol_fatti, s.assist
            FROM statistiche_fanta s WHERE s.giocatore_id=? ORDER BY s.stagione
        """, (giocatore_id,)).fetchall()
        passato = [riga for riga in storico if riga[0] < "2026-27"]
        def media(indice: int) -> float | None:
            valori = [riga[indice] for riga in passato if riga[indice] is not None]
            return sum(valori) / len(valori) if valori else None
        gol_medi, assist_medi = media(3), media(4)
        piazzati = self.db.execute("SELECT tipo, priorita FROM specialisti_piazzati WHERE giocatore_id=? ORDER BY tipo, priorita", (giocatore_id,)).fetchall()
        etichette = {"rigori": "Rig.", "punizioni": "Pun.", "angoli": "Ang."}
        return {"nome": giocatore[0], "ruolo": giocatore[1], "squadra": giocatore[2], "fascia": fascia[0] if fascia else "Da assegnare",
                "corrente": corrente or (None,) * 6, "fm_storica": media(2),
                "ga_storici": None if gol_medi is None and assist_medi is None else (gol_medi or 0) + (assist_medi or 0),
                "piazzati": " · ".join(f"{etichette[tipo]} #{priorita}" for tipo, priorita in piazzati) or "—", "storico": storico}

    def apri_confronto(self) -> None:
        if len(self.confronto) < 2:
            messagebox.showinfo("Confronto", "Aggiungi almeno due calciatori al confronto.")
            return
        giocatori = [self.dati_confronto(identita) for identita in self.confronto]
        finestra = Toplevel(self.radice); finestra.title("Confronto calciatori"); finestra.transient(self.radice)
        finestra.geometry("980x600"); finestra.minsize(720, 420); finestra.resizable(True, True)
        notebook = ttk.Notebook(finestra); notebook.pack(fill="both", expand=True, padx=12, pady=12)
        sintesi = ttk.Frame(notebook); storico = ttk.Frame(notebook)
        notebook.add(sintesi, text="Sintesi"); notebook.add(storico, text="Storico")

        def crea_griglia(contenitore, intestazioni, righe, larghezza_metrica=20, larghezza_valore=17):
            riquadro = ttk.Frame(contenitore)
            riquadro.pack(fill="both", expand=True)
            tela = tk.Canvas(riquadro, highlightthickness=0, background="#ffffff")
            barra_v = ttk.Scrollbar(riquadro, orient="vertical", command=tela.yview)
            barra_o = ttk.Scrollbar(riquadro, orient="horizontal", command=tela.xview)
            tela.configure(yscrollcommand=barra_v.set, xscrollcommand=barra_o.set)
            corpo = tk.Frame(tela, background="#ffffff")
            finestra_corpo = tela.create_window((0, 0), window=corpo, anchor="nw")

            def aggiorna_scorrimento(_evento=None):
                tela.configure(scrollregion=tela.bbox("all"))

            corpo.bind("<Configure>", aggiorna_scorrimento)
            self.abilita_rotellina(tela, consenti_orizzontale=True, contenuto=corpo)
            for colonna, titolo in enumerate(intestazioni):
                tk.Label(corpo, text=titolo, width=larghezza_metrica if colonna == 0 else larghezza_valore,
                         background="#eaf2ff", foreground="#1d2939", font=("Sans", 10, "bold"),
                         padx=6, pady=6, anchor="w" if colonna == 0 else "center").grid(row=0, column=colonna, sticky="nsew", padx=1, pady=1)
            for indice_riga, (metrica, valori, migliori) in enumerate(righe, start=1):
                sfondo = "#ffffff" if indice_riga % 2 else "#f8fafc"
                tk.Label(corpo, text=metrica, width=larghezza_metrica, background=sfondo, foreground="#344054",
                         font=("Sans", 10), padx=6, pady=5, anchor="w").grid(row=indice_riga, column=0, sticky="nsew", padx=1, pady=1)
                for colonna, valore_cella in enumerate(valori, start=1):
                    migliore = colonna - 1 in migliori
                    testo_valore = f"▲ {valore_cella}" if migliore else valore_cella
                    tk.Label(corpo, text=testo_valore, width=larghezza_valore,
                             background="#e8f7ef" if migliore else sfondo,
                             foreground="#067647" if migliore else "#1d2939",
                             font=("Sans", 10, "bold") if migliore else ("Sans", 10), padx=6, pady=5,
                             anchor="center").grid(row=indice_riga, column=colonna, sticky="nsew", padx=1, pady=1)
            tela.grid(row=0, column=0, sticky="nsew"); barra_v.grid(row=0, column=1, sticky="ns"); barra_o.grid(row=1, column=0, sticky="ew")
            riquadro.rowconfigure(0, weight=1); riquadro.columnconfigure(0, weight=1)
            return finestra_corpo

        def migliori_alti(valori):
            numeri = [valore for valore in valori if isinstance(valore, (int, float))]
            if not numeri:
                return set()
            massimo = max(numeri)
            return {indice for indice, valore in enumerate(valori) if valore == massimo}

        righe = [
            ("Ruolo Classic", [g["ruolo"] for g in giocatori], set()),
            ("Fascia", [g["fascia"] for g in giocatori], set()),
            ("Piazzati", [g["piazzati"] for g in giocatori], set()),
            ("PV 2026-27", [g["corrente"][0] for g in giocatori], None),
            ("MV 2026-27", [g["corrente"][1] for g in giocatori], None),
            ("FM 2026-27", [g["corrente"][2] for g in giocatori], None),
            ("Gol 2026-27", [g["corrente"][3] for g in giocatori], None),
            ("Assist 2026-27", [g["corrente"][4] for g in giocatori], None),
            ("FVM", [g["corrente"][5] for g in giocatori], None),
            ("FM storica", [g["fm_storica"] for g in giocatori], None),
            ("Gol + assist storici", [g["ga_storici"] for g in giocatori], None),
        ]
        righe_formattate = []
        for metrica, valori, migliori in righe:
            if metrica == "Fascia":
                posizioni = [ORDINE_FASCE.get(valore, len(FASCE)) for valore in valori]
                minima = min(posizioni)
                migliori = {indice for indice, posizione in enumerate(posizioni) if posizione == minima and valori[indice] != "Da assegnare"}
            elif migliori is None:
                migliori = migliori_alti(valori)
            righe_formattate.append((metrica, [valore if isinstance(valore, str) else self.formato(valore) for valore in valori], migliori))
        ttk.Label(sintesi, text="I valori migliori per ogni statistica sono evidenziati in verde e grassetto.", style="Sottotitolo.TLabel").pack(anchor="w", pady=(0, 6))
        crea_griglia(sintesi, ["Metrica", *[g["nome"] for g in giocatori]], righe_formattate)

        intestazioni_storico = ["Stagione", *[f"{giocatore['nome']}\n{titolo}" for giocatore in giocatori for titolo in ("MV", "FM", "G+A")]]
        stagioni = sorted({riga[0] for giocatore in giocatori for riga in giocatore["storico"]}, reverse=True)
        righe_storico = []
        for stagione in stagioni:
            valori = []
            valori_metriche = {"mv": [], "fm": [], "ga": []}
            for giocatore in giocatori:
                riga = next((riga for riga in giocatore["storico"] if riga[0] == stagione), None)
                bonus = None if not riga or riga[3] is None and riga[4] is None else (riga[3] or 0) + (riga[4] or 0)
                valori_metriche["mv"].append(riga[1] if riga else None)
                valori_metriche["fm"].append(riga[2] if riga else None)
                valori_metriche["ga"].append(bonus)
                valori += [self.formato(riga[1]) if riga else "—", self.formato(riga[2]) if riga else "—", self.formato(bonus)]
            migliori = set()
            for indice_metrica, metrica in enumerate(("mv", "fm", "ga")):
                migliori |= {indice_giocatore * 3 + indice_metrica for indice_giocatore in migliori_alti(valori_metriche[metrica])}
            righe_storico.append((stagione, valori, migliori))
        crea_griglia(storico, intestazioni_storico, righe_storico, larghezza_metrica=10, larghezza_valore=14)

    def apri_impostazioni(self) -> None:
        finestra = Toplevel(self.radice); finestra.title("Impostazioni aggiornamento"); finestra.transient(self.radice)
        ttk.Label(finestra, text="Chiave di aggiornamento", padding=(16, 16, 16, 4)).pack(anchor="w")
        presente = "trovata" if API_KEY_PATH.exists() and API_KEY_PATH.read_text(encoding="utf-8").strip() else "non trovata"
        ttk.Label(finestra, text=f"La chiave è {presente} nel file locale:\n{API_KEY_PATH.name}\n\nNon viene copiata nel database.", wraplength=430, padding=(16, 0, 16, 16)).pack(anchor="w")

    def avvia_sincronizzazione(self) -> None:
        try:
            chiave_api()
        except RuntimeError as errore:
            messagebox.showerror("Aggiornamento dati", str(errore)); return
        self.pulsante_sincronizza.configure(state="disabled")
        self.stato.set("Aggiornamento dati avviato…")
        def lavora():
            try:
                risultato = sincronizza_serie_a(lambda testo: self.radice.after(0, self.stato.set, testo))
                self.radice.after(0, lambda: messagebox.showinfo("Aggiornamento dati", f"Aggiornamento completato.\nRichieste: {risultato[0]}\nGiocatori collegati: {risultato[1]}\nDa verificare: {risultato[2]}"))
                self.radice.after(0, self.mostra_giocatore)
            except Exception as errore:
                self.radice.after(0, lambda: messagebox.showerror("Aggiornamento dati", str(errore)))
            finally:
                self.radice.after(0, lambda: self.pulsante_sincronizza.configure(state="normal"))
        threading.Thread(target=lavora, daemon=True).start()

    def avvia_download_foto(self) -> None:
        self.pulsante_foto.configure(state="disabled")
        self.stato.set("Download immagini in corso…")
        def lavora():
            try:
                foto = scarica_foto_api(lambda testo: self.radice.after(0, self.stato.set, testo))
                wikimedia = scarica_foto_wikimedia(lambda testo: self.radice.after(0, self.stato.set, testo))
                bandiere = scarica_bandiere_flagsnet(lambda testo: self.radice.after(0, self.stato.set, testo))
                stemmi = scarica_stemmi_api(lambda testo: self.radice.after(0, self.stato.set, testo))
                self.radice.after(0, lambda: messagebox.showinfo("Immagini", f"Foto scaricate: {foto[0]}\nFoto aggiunte: {wikimedia[0]}\nSenza ritratto verificato: {wikimedia[1]}\nBandiere scaricate: {bandiere[0]}\nBandiere non disponibili: {bandiere[1]}\nStemmi scaricati: {stemmi[0]}\nStemmi non disponibili: {stemmi[1]}"))
                self.radice.after(0, self.mostra_giocatore)
            except Exception as errore:
                self.radice.after(0, lambda: messagebox.showerror("Foto e stemmi", str(errore)))
            finally:
                self.radice.after(0, lambda: self.pulsante_foto.configure(state="normal"))
        threading.Thread(target=lavora, daemon=True).start()

    def apri_avvisi(self) -> None:
        avvisi = [riga[0] for riga in self.db.execute("SELECT descrizione FROM problemi_importazione ORDER BY tipo, descrizione")]
        finestra = Toplevel(self.radice); finestra.title("Avvisi sui dati importati"); finestra.transient(self.radice)
        testo = tk.Text(finestra, width=82, height=14, wrap="word")
        testo.pack(fill="both", expand=True, padx=16, pady=16)
        testo.insert("1.0", "Nessun avviso." if not avvisi else "\n".join(f"• {avviso}" for avviso in avvisi))
        testo.configure(state="disabled")

    def avvia(self) -> None:
        self.radice.mainloop()


def prepara_dati() -> None:
    assicura_cartelle_dati()
    connessione = apri_connessione()
    connessione.row_factory = sqlite3.Row
    try:
        crea_database(connessione)
        statistiche, quotazioni = importa_fantacalcio(connessione)
        documento = percorso_fasce_locali()
        fasce, problemi = importa_fasce(connessione, documento) if documento.exists() else (0, [])
        righe_fbref, abbinati_fbref = importa_fbref(connessione)
        squadre_fbref = importa_statistiche_squadre_fbref(connessione)
        collegamenti_manuali = applica_collegamenti_manuali_fbref(connessione)
        tiratori, tiratori_non_abbinati = importa_tiratori(connessione)
        formazione, _ = importa_infografica(connessione)
        nazionalita = importa_nazionalita_fbref(connessione)
        print(f"Importate {statistiche} righe statistiche e {quotazioni} righe quotazioni.")
        print(f"Importate {fasce} assegnazioni di fascia. Abbinamenti da verificare: {len(problemi)}.")
        print(f"Importate {righe_fbref} schede statistiche avanzate; collegate: {abbinati_fbref + collegamenti_manuali}.")
        print(f"Importate {squadre_fbref} schede statistiche delle squadre.")
        print(f"Importate {tiratori} assegnazioni per i piazzati; da verificare: {tiratori_non_abbinati}.")
        print(f"Importate {formazione} indicazioni da formazione tipo e ballottaggi.")
        print(f"Importate {nazionalita} nazionalità.")
    finally:
        connessione.close()


def main() -> None:
    parser = argparse.ArgumentParser(description="Assistente Asta Fantacalcio")
    parser.add_argument("--reimporta", action="store_true", help="ricrea i dati locali dai file sorgente")
    parser.add_argument("--solo-importa", action="store_true", help="importa i dati senza avviare la GUI")
    parser.add_argument("--sincronizza-api", action="store_true", help="aggiorna i dati Serie A")
    parser.add_argument("--scarica-foto", action="store_true", help="scarica localmente le foto dei profili collegati")
    argomenti = parser.parse_args()
    migra_database_legacy()
    if argomenti.reimporta or argomenti.solo_importa or not DB_PATH.exists():
        prepara_dati()
    if argomenti.solo_importa:
        return
    if argomenti.sincronizza_api:
        richieste, abbinati, non_abbinati = sincronizza_serie_a(print)
        print(f"Sincronizzazione completata: {richieste} richieste, {abbinati} abbinati, {non_abbinati} da verificare.")
        return
    if argomenti.scarica_foto:
        connessione = apri_connessione()
        crea_database(connessione)
        importa_nazionalita_fbref(connessione)
        connessione.close()
        scaricate, errori = scarica_foto_api(print)
        wikimedia, errori_wikimedia = scarica_foto_wikimedia(print)
        bandiere, errori_bandiere = scarica_bandiere_flagsnet(print)
        stemmi, errori_stemmi = scarica_stemmi_api(print)
        print(f"Foto scaricate: {scaricate}; aggiunte: {wikimedia}; senza ritratto verificato: {errori_wikimedia}. Bandiere scaricate: {bandiere}; non disponibili: {errori_bandiere}. Stemmi scaricati: {stemmi}; non disponibili: {errori_stemmi}.")
        return
    connessione = apri_connessione()
    crea_database(connessione)
    importa_statistiche_squadre_fbref(connessione)
    importa_tiratori(connessione)
    importa_infografica(connessione)
    applica_collegamenti_manuali_fbref(connessione)
    importa_nazionalita_fbref(connessione)
    Applicazione(connessione).avvia()


if __name__ == "__main__":
    main()
