# Absheron Rising (Abşeron Yüksəlir)

A browser city builder set in Baku and the Absheron peninsula, starting in the year 1900. Build the city from the
oil boom onwards: zone housing, shops and industry, lay roads, open oil fields, run the metro and an airport, set
taxes, and raise Baku's landmarks.

**Play it in the browser:** https://nasirmustafayev.github.io/absheron-rising

## Why I built it

I wanted a city builder about my own city, where the map, the history and the landmarks are Baku's instead of a
generic town, and I wanted to see how far I could take a full 3D game in the browser with AI as my main tool.

## Features

- A 3D map of the Absheron peninsula, with the Caspian coast and the towns around Baku
- Zones for housing, commerce and industry; roads, transport, metro and an airport
- Oil fields and the oil economy that shaped Baku
- Budget and taxes, population and a running calendar that starts in 1900
- Landmarks and historic sites, with photos
- Music player with a playlist, and a tutorial for new players
- Azerbaijani interface; saves in the browser; installable as an app (PWA)

## How it's built

- Plain JavaScript in a single page, with no build step, hosted on GitHub Pages
- 3D rendering with Three.js (WebGL), with its own material library (`3d/matlib.js`) and renderer (`3d/render3d.js`)
- Audio engine and playlist in `3d/audio.js`, with tracks levelled to about -20 LUFS
- Game state saved in `localStorage`
- PWA manifest in `pwa/`

## How I built it with AI

I built it with Claude Code as my main tool. I described the systems I wanted (zoning, the economy, the 3D map),
reviewed what it produced, and tested every change by playing the game in the browser before keeping it.

## Credits

- Music: nine CC0 (public domain) tracks from OpenGameArt and one track I made with Suno. Full list in
  [3d/audio/music/CREDITS.md](3d/audio/music/CREDITS.md).

Shared for portfolio review. All rights reserved.
