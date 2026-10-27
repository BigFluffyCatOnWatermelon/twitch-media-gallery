# Anime Site Pet (Tampermonkey)

A small self-contained anime-style site mascot for Twitch and most ordinary websites. The character is drawn using inline SVG, so the script does not download character assets or send data to external services.

## Install

1. Open the raw `.user.js` link in a browser with Tampermonkey installed, or create a new script and paste the file contents.
2. Save and enable it.
3. Refresh the page.

## Controls

- Left-click the character: pet/react.
- Right-click the character: open settings.
- `Alt` + `Shift` + `P`: settings.
- `Alt` + `Shift` + `H`: show/hide the character.

## Features in v0.1.0

- Random autonomous actions: walk, run, hop, sit, sleep, dance, look around, blink, stumble, and recover.
- Pointer curiosity and occasional playful chases.
- Optional platform discovery on page elements such as buttons, images, panels, and video.
- Twitch-specific reactions to chat activity and video pause/play state.
- Persistent settings for size, speed, activity, reduced motion, speech bubbles, and interaction toggles.
- Inline SVG character, Shadow DOM styling, no external API calls, no analytics.

## Notes

This is an early prototype. DOM layouts differ across websites, so platform behavior may be imperfect on some pages. The script runs on ordinary HTML pages and may not be able to inspect content inside cross-origin iframes. It does not control Twitch or send messages in chat.
