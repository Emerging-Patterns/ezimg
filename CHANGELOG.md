# Changelog

## [1.2.0](https://github.com/Emerging-Patterns/ezimg/compare/v1.1.0...v1.2.0) (2026-09-26)


### Features

* lift the PNG pixel stage to decode_png, and prove the one-block PNG round trip ([#64](https://github.com/Emerging-Patterns/ezimg/issues/64)) ([56a42da](https://github.com/Emerging-Patterns/ezimg/commit/56a42dad5b1f7d8e851de61739099f2d5a02a6e7))
* prove IMG-JPG-2, the JPEG planes from Array.set to decode_jpeg's pixels ([#67](https://github.com/Emerging-Patterns/ezimg/issues/67)) ([75c266c](https://github.com/Emerging-Patterns/ezimg/commit/75c266c4170cc29bf3c40d1f61ef2a01f4f233a9))
* prove IMG-PNG-3 and IMG-PNG-4, the PNG encoder's refusals and IHDR ([#56](https://github.com/Emerging-Patterns/ezimg/issues/56)) ([94e3312](https://github.com/Emerging-Patterns/ezimg/commit/94e3312247570b4ffb4ccbcfd7e024c50fd505de))
* prove IMG-RAS-1 to IMG-RAS-4, the raster helpers ([#58](https://github.com/Emerging-Patterns/ezimg/issues/58)) ([3bd0909](https://github.com/Emerging-Patterns/ezimg/commit/3bd090948d36e8875b62c33217bfaa6359d27ab3))
* prove the PNG round trip (IMG-PNG-2), and IMG-PNG-9 and IMG-PIX-1 with ancillary chunks ([#69](https://github.com/Emerging-Patterns/ezimg/issues/69)) ([316f3ef](https://github.com/Emerging-Patterns/ezimg/commit/316f3ef8010b6929fd533ce9c2eda98b9bc5385b))


### Bug Fixes

* exact T.871 colour conversion in JPEG decode; settle IMG-JPG-2, IMG-JPG-3 and IMG-JPG-6 ([#61](https://github.com/Emerging-Patterns/ezimg/issues/61)) ([f452c29](https://github.com/Emerging-Patterns/ezimg/commit/f452c29229fcf7356a92accd54a5f3651769bc80))

## [1.1.0](https://github.com/Emerging-Patterns/ezimg/compare/v1.0.0...v1.1.0) (2026-09-25)


### ⚠ BREAKING CHANGES

* premultiply and straight are removed from main.bend.
* encode_jpeg returns Maybe<&2, List<&2, U32>>.

### Features

* add U32 equality lemmas and prove IMG-PNG-1 ([#49](https://github.com/Emerging-Patterns/ezimg/issues/49)) ([82b90f8](https://github.com/Emerging-Patterns/ezimg/commit/82b90f8f7787b71baabc8dd8e2ec2006b9fa1f08))
* prove IMG-JPG-1 and IMG-JPG-5, and the JPEG side of IMG-PIX-1 ([#55](https://github.com/Emerging-Patterns/ezimg/issues/55)) ([e8328ed](https://github.com/Emerging-Patterns/ezimg/commit/e8328edf7cbb54b0a73cec87d0a534cd0e19f2e6))
* prove IMG-PIX-2 (JPEG encode ignores alpha) and IMG-RAS-5 (map) ([#44](https://github.com/Emerging-Patterns/ezimg/issues/44)) ([037b1ee](https://github.com/Emerging-Patterns/ezimg/commit/037b1eedbfc957d06cf35ea5a1a8ad0cc35b75a2))
* prove IMG-PNG-1's forward half and reword IMG-JPG-2 ([#47](https://github.com/Emerging-Patterns/ezimg/issues/47)) ([46e42a6](https://github.com/Emerging-Patterns/ezimg/commit/46e42a6f46438312e531ffd0002562ea72e85bd8))
* prove IMG-PNG-5, the chunk CRC is ISO 3309 CRC-32 ([#52](https://github.com/Emerging-Patterns/ezimg/issues/52)) ([1e2d7a3](https://github.com/Emerging-Patterns/ezimg/commit/1e2d7a34f212b7509bf9810f00b28d5ee2103863))
* prove IMG-PNG-6, unfiltering follows the PNG filter definitions ([#53](https://github.com/Emerging-Patterns/ezimg/issues/53)) ([659cd65](https://github.com/Emerging-Patterns/ezimg/commit/659cd65c05dd0d3d21de178c4ef2a4e1b4f3957d))
* prove IMG-PNG-8 and the pixel stage of IMG-PNG-9 ([#51](https://github.com/Emerging-Patterns/ezimg/issues/51)) ([73dbf09](https://github.com/Emerging-Patterns/ezimg/commit/73dbf0975185d5c78b74498a07dd8a29a987413b))


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
