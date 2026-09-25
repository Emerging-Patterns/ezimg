# Changelog

## [2.0.0](https://github.com/Emerging-Patterns/ezimg/compare/v1.0.0...v2.0.0) (2026-09-25)


### ⚠ BREAKING CHANGES

* premultiply and straight are removed from main.bend.
* encode_jpeg returns Maybe<&2, List<&2, U32>>.

### Features

* prove IMG-PIX-2 (JPEG encode ignores alpha) and IMG-RAS-5 (map) ([#44](https://github.com/Emerging-Patterns/ezimg/issues/44)) ([037b1ee](https://github.com/Emerging-Patterns/ezimg/commit/037b1eedbfc957d06cf35ea5a1a8ad0cc35b75a2))


### Bug Fixes

* encode_jpeg returns Maybe and refuses what encode_png refuses ([#42](https://github.com/Emerging-Patterns/ezimg/issues/42)) ([33a2ef4](https://github.com/Emerging-Patterns/ezimg/commit/33a2ef429506f4abccd46fceef051644d769706b))
* remove premultiply and straight ([#43](https://github.com/Emerging-Patterns/ezimg/issues/43)) ([8573fb1](https://github.com/Emerging-Patterns/ezimg/commit/8573fb16f221e1bee6806614e8ec7bfd3c6fc7b5))

## [1.0.0](https://github.com/Emerging-Patterns/ezimg/compare/v0.2.1...v1.0.0) (2026-09-25)


### ⚠ BREAKING CHANGES

* JPEG samples are 0xAARRGGBB; a gray sample is no longer the bare Y value.
* land SPEC.md and retire the closed laws ([#39](https://github.com/Emerging-Patterns/ezimg/issues/39))

### Features

* land SPEC.md and retire the closed laws ([#39](https://github.com/Emerging-Patterns/ezimg/issues/39)) ([15b3540](https://github.com/Emerging-Patterns/ezimg/commit/15b3540916e2afef53209c1ce06baff7a5091e1e))


### Bug Fixes

* decode 4:2:2 and every other non-square JPEG MCU correctly ([#41](https://github.com/Emerging-Patterns/ezimg/issues/41)) ([e87696d](https://github.com/Emerging-Patterns/ezimg/commit/e87696d745db2e7410c002541809357333f0a223))
* JPEG decode returns opaque 0xAARRGGBB samples ([#40](https://github.com/Emerging-Patterns/ezimg/issues/40)) ([670e134](https://github.com/Emerging-Patterns/ezimg/commit/670e13442656db818ab31ee5f662e33b254ae101))

## [0.2.1](https://github.com/Emerging-Patterns/ezimg/compare/v0.2.0...v0.2.1) (2026-09-22)


### Performance Improvements

* build JPEG cosine kernel once per encode ([#32](https://github.com/Emerging-Patterns/ezimg/issues/32)) ([55d7a74](https://github.com/Emerging-Patterns/ezimg/commit/55d7a7493216837a5005233d581965610714b510))

## [0.2.0](https://github.com/Emerging-Patterns/ezimg/compare/v0.1.0...v0.2.0) (2026-09-22)


### Features

* add Nix Pillow vs ezimg bench check ([#31](https://github.com/Emerging-Patterns/ezimg/issues/31)) ([cad590b](https://github.com/Emerging-Patterns/ezimg/commit/cad590bcf222b7538087727485e2fb0ea253eac3))
