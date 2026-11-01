# Driftline

Drift-Simulator in der echten Welt. Du wählst einen Ort auf der Karte, und das Spiel baut Straßen, Gebäude, Wald, Wasser und Gelände aus echten Kartendaten. Fährst du weiter, lädt die Umgebung automatisch nach.

## Spielen

Die Seite läuft direkt im Browser (Desktop und Handy), ohne Installation und ohne Build-Schritt.

- **Ort wählen:** Adresse suchen, „Mein Standort“ oder einfach auf die Karte tippen
- **Teilen:** Die Adresszeile enthält die Koordinaten (`#50.05,10.2`). Wer den Link öffnet, startet am selben Ort.

| Taste | Funktion |
|---|---|
| W / ↑ | Gas |
| S / ↓ | Bremse, Rückwärts |
| A / D | Lenken |
| Leertaste | Handbremse, startet den Drift |
| C | Kamera wechseln |
| R | Zurück auf die nächste Straße |
| P / Esc | Pause |

Gamepad: linker Stick lenkt, R2 Gas, L2 Bremse, A Handbremse. Auf dem Handy gibt es Touch-Tasten.

## Datenquellen

- Straßen, Gebäude, Landnutzung: © [OpenStreetMap](https://www.openstreetmap.org/copyright)-Mitwirkende (ODbL), abgefragt über die Overpass API
- Höhendaten: [AWS Terrain Tiles](https://registry.opendata.aws/terrain-tiles/) (Terrarium, Zoom 14)
- Ortssuche: Nominatim
- Kartenauswahl: Leaflet mit OpenStreetMap-Kacheln und Esri-Luftbild

Die öffentlichen Overpass-Server sind kostenlos, aber manchmal ausgelastet. Das Spiel probiert dann automatisch einen anderen Server und versucht es später erneut.

## Aufbau

```
index.html        Oberfläche (Kartenauswahl, Ladebildschirm, HUD)
css/style.css     Gestaltung
js/app.js         Renderer, Auto, Fahrphysik, Kamera, Sound, Steuerung, Kartenauswahl
js/world.js       Welt-Streaming in 400-m-Kacheln: Bodentextur, Gebäude, Bäume, Kollisionen
js/geo.js         Projektion, Overpass, Höhendaten, Ortssuche
js/util.js        Hilfsfunktionen
```

Lokal testen: Ordner mit einem kleinen Webserver öffnen, z. B. `python3 -m http.server`, dann `http://localhost:8000`. Ein direkter Doppelklick auf `index.html` funktioniert nicht, weil der Browser ES-Module nur über einen Server lädt.
