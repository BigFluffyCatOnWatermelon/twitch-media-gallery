# Changelog

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