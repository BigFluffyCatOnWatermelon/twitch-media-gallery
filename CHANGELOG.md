# Changelog

## [5.9.90] — 2026-10-30

### Fixed
- The “No compression” preset no longer encodes MP4 with H.264 CRF 0 or WebM with VP8 CRF 0, which could turn a sub-megabyte cropped clip into a multi-megabyte lossless encode.
- MP4/WebM exports with this preset now retain source dimensions and frame cadence while using a bitrate budget derived from the source file's average bitrate. A small share of the budget is reserved for audio, rather than forcing 320 kbps audio.
- Updated the editor's predicted MP4/WebM output size to use the same source-bitrate budget and selected output duration.
- Updated the preset help text to explain that cropping still requires re-encoding even though resolution and FPS are retained.
- Bumped the userscript version to 5.9.90.

### Verification
- Full userscript JavaScript syntax check passed.
- MP4/WebM file sizes must still be verified with the user's sample video in the browser.

## [5.9.89] — 2026-10-30

### Fixed
- The animated WebP estimate no longer silently caps its predicted result at the original file size when edge-frame re-encoding may still exceed it.
- Video size estimates now account for the doubled duration produced by ping-pong export.
- Bumped the userscript version to 5.9.89.

### Verification
- Full userscript JavaScript syntax check passed.
- Estimated sizes remain approximate until the actual encode finishes.

## [5.9.88] — 2026-10-30

### Fixed
- Fixed the animated WebP export failure caused by debug logging reading frame counters outside their local scope.
- Replaced source-file metadata in the editor footer with a live estimate of the exported file's FPS, pixel dimensions, and file size. The estimate updates when trimming, crop geometry, speed, export format, or preset settings change.
- Animated WebP output estimates are calculated from frame timing, frame positions and compressed payload sizes, crop intersections, output scale, trim range, and optional ping-pong duplication.
- Video FPS sampling now uses presented-frame timestamps and media-time deltas from requestVideoFrameCallback instead of trying to infer FPS from timeupdate events.
- Bumped the userscript version to 5.9.88.

### Notes
- The displayed weight is a pre-encoding estimate, not a guaranteed final byte count. Re-encoded edge frames and codec behavior can change the actual size.

### Verification
- Full userscript JavaScript syntax check passed.
- Export, estimate updates, and real video FPS sampling still require browser validation with media files.

## [5.9.87] — 2026-10-30

### Fixed
- For animated WebP exports using the “No compression” preset with cropping, preserve original compressed frame payloads whenever possible and reuse them after shifting their frame offsets.
- If crop-edge frames must be re-encoded and the first full-quality result would exceed the source file size, retry at progressively lower quality only for those re-encoded frames. Unchanged in-crop frames remain byte-for-byte intact.
- Keep the requested crop even if an exceptionally compact source cannot be matched in size; report that exception instead of silently reverting to the original un-cropped file.
- Corrected debug accounting for preserved, re-encoded, and cropped-away frames.
- Bumped the userscript version to 5.9.87.

### Verification
- Full userscript JavaScript syntax check passed.
- Animated WebP crop export must still be verified against the user's actual file in a browser.

## [5.9.86] — 2026-10-30

### Fixed
- Animated WebP crop export now reuses the original compressed ANMF frame payloads whenever a frame remains fully inside the crop and no resize is needed. Only frame patches intersecting the crop boundary are decoded and re-encoded, retaining the source animation's compact delta-frame encoding instead of expanding every frame through Canvas.
- Added debug counts for preserved versus re-encoded animation frames.
- Bumped the userscript version to 5.9.86.

### Verification
- Full userscript JavaScript syntax check passed.
- Animated WebP crop size and playback still need a real browser test with the user's source file.

## [5.9.85] — 2026-10-30

### Added
- Added the original file size beside FPS and pixel dimensions in the media editor.

### Clarified
- Explained that the “No compression” export preset disables downscaling/FPS reduction and uses lossless encoding where supported; transcoding to another format can still produce a larger file.

### Verification
- Full userscript JavaScript syntax check passed.
- The displayed weight is the input file's actual byte size; output size is determined after export.

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