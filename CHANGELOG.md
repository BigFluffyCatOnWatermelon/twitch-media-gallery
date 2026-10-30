# Changelog

## [5.9.84] — 2026-10-30

### Added
- Added a separate preview-repeat toggle beside Play, disabled by default and independent from Ping-pong.
- Added source FPS (estimated from decoded frames during playback when supported) and pixel dimensions beside the final-duration summary.

### Fixed
- Reduced the playback stop guard so the playhead can reach the trim endpoint much more closely.
- Hid the playhead while dragging a trim boundary and prevented playback callbacks from repainting the timeline while scrubbing.
- Bumped the userscript version to 5.9.84.

### Verification
- Full userscript syntax check passed.
- Timeline behavior, FPS estimation, and repeat playback still need a real browser test in Twitch.

## [5.9.83] — 2026-10-30

### Added
- Added a mute toggle beside Play in the media editor. Video preview starts muted by default; the setting affects preview playback only and does not remove the audio track from exported video.

### Fixed
- Animated WebP files no longer go through the pinned FFmpeg.wasm decoder when the output is WebP. The browser-native frame pipeline now applies trimming, speed changes, cropping, and ping-pong while rebuilding the animated WebP container.
- Static WebP files that the browser cannot re-encode are kept as-is when the requested output is also WebP, instead of being sent to FFmpeg and failing with an unreadable input stream.
- Bumped the userscript version to 5.9.83.

### Verification
- Full userscript JavaScript syntax check passed.
- Real animated WebP export, crop, trim, and playback must still be verified in Twitch with test files.

## [5.9.82] — 2026-10-30

### Fixed
- Reverse ping-pong preview now caches frames at the video's native resolution instead of shrinking them to 240 px. The cache adapts its sampling interval to the source dimensions and is capped at 256 MiB to avoid unbounded memory use; very large sources may therefore have fewer cached reverse frames.
- Moving the crop rectangle no longer switches the selected aspect-ratio preset to “Свободно”. The preset changes to “Свободно” only when a corner handle changes the crop dimensions.
- Bumped the userscript version to 5.9.82 for Tampermonkey updates.

### Notes
- The end-of-video preview keeps a safety offset of at least 50 ms before the trim boundary so the browser can present the final decoded frame. This offset can grow with playback speed; it is not a 5 ms setting.

### Verification
- Full userscript JavaScript syntax check passed.
- Full-resolution reverse preview and crop interactions still require runtime verification in Twitch.

## [5.9.81] — 2026-10-30

### Fixed
- Fixed an editor startup failure reported after media import (`videoReverseDisplayTime is not defined`). The reverse-preview display position now lives in the editor's shared script scope, so playback and cleanup callbacks can always access it.
- Bumped the userscript version to 5.9.81 so Tampermonkey can detect the correction.

### Verification
- Full userscript JavaScript syntax check passed.
- Runtime import and playback must still be confirmed in Twitch.

All user-visible changes to the userscript are recorded here. New entries go at the top and must describe the behavior change, the affected area, and any compatibility or migration notes.

## [5.9.80] — 2026-10-30

### Fixed
- Fixed restarting video preview when playback stops at the guarded end of the selected trim range. Pressing Play now returns to the selected start instead of issuing a seek just beyond the real stopping point.
- Coalesced rapid timeline scrubbing input and serialized video seek requests. Dragging the playhead no longer floods the media element with overlapping seek operations.
- Added a bounded, downscaled frame cache for reverse ping-pong preview. Reverse playback uses cached preview frames where coverage is available, then seeks to the exact selection start before forward playback resumes. Original media and exported output quality are not reduced by this preview cache.
- Prevented stale asynchronous frame captures from being added back to the reverse cache after the cache is invalidated (for example, when playback jumps backwards).

### Editor
- Restored timecodes above the timeline, on both trim handles, and at the timeline edges.
- Changed crop dimensions from percentages to even pixel dimensions based on the source media.
- Corrected crop aspect-ratio button state. Manual crop adjustments switch the active ratio indicator to Free.
- Renamed the active crop-mode button from Done to Cancel; cancelling the crop mode restores the crop state from before entering the mode.
- Removed the stage instruction overlay.
- Replaced the old HD checkbox with a collapsible Export settings section.
- Added Default, Low, Medium, High, and No compression export presets, editable format/quality/size/FPS/bitrate/codec settings, and locally saved custom presets.

### Developer workflow
- Added a changelog policy, contribution guide, pull-request template, and an automated pull-request check requiring a changelog entry when the userscript changes.

### Verification
- JavaScript syntax check passed for the complete userscript.
- Browser-level playback, scrubbing, and export tests have not been run in a live Twitch session; please verify those workflows with a short and a longer video before relying on the release.