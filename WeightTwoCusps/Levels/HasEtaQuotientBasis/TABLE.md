# Level data for eta-quotient cusp-form folders

Reference data for every level **1 through 500**, extracted from
`M2_Gamma0_Eta_Quotient_Bases_N_1_to_500 (1).txt` (report updated 2026-11-06).
Use this file with the [folder-generation instructions](README.md#instructions-for-agents-adding-a-level).
All spaces here are weight-two cusp forms on `Γ₀(N)` with trivial character over `ℂ`.

## How to use the data

- For `HasEtaQuotientBasis/N/`, select a level with **positive dimension**
  and **Full eta basis = YES**. There are 99 such levels in the report.
- A zero-dimensional space has a full empty basis; the 15 such levels do
  not need a nontrivial level folder.
- When **Full eta basis = NO**, the supplied vectors form only a basis of
  the cuspidal eta-quotient span. They do not give a basis of the whole
  cusp-form space. A zero eta rank means that this list is empty.
- The columns `dim S₂`, `Eta rank`, and `Full eta basis` are exactly the
  report fields `Dimension_S2`, `Dimension_cuspidal_eta_span`, and
  `S2_spanned_by_cuspidal_eta_quotients`. `Cusps` is `Number_of_cusps`.
  Only `Basis_cuspidal_eta_S2` is reproduced below; the report's
  `Basis_eta_M2` belongs to a different space.
- `B` is the weight-two Sturm bound computed from the report's formula:
  `floor([SL₂(ℤ) : Γ₀(N)] / 6)`, with index
  `N * ∏_{p | N} (1 + 1/p)` over distinct primes. It is a derived column;
  the other table columns and all exponent vectors are transcribed data.
- Each basis block is a Lean expression of type `List (Fin N → ℤ)`.
  Give it that expected type when copying. In `sparse![N; i => r]`,
  index `i` represents `η((i + 1)z)^r`; omitted entries are zero.
  Integer exponents may be negative. Every vector has leading coefficient
  one at its first nonzero degree, which need not be degree one.

The report supplies no LMFDB labels or new/old decomposition. Identify those
using the README before choosing names or defining `Old/` lifts. The Lean
constructors and tactics must still certify the forms and the final basis.
The report describes its cusp data as new computations, rather than a
published cusp classification. Its underlying sources include
[Rouse–Webb](https://users.wfu.edu/rouseja/cv/etaquos.pdf) and the
[companion computation files](https://users.wfu.edu/rouseja/eta/).

## Levels with a complete nonzero cuspidal eta basis

[11](#level-11), [14](#level-14), [15](#level-15), [20](#level-20), [22](#level-22), [24](#level-24), [27](#level-27), [28](#level-28), [30](#level-30), [32](#level-32), [33](#level-33), [35](#level-35), [36](#level-36), [40](#level-40), [42](#level-42), [46](#level-46), [48](#level-48), [54](#level-54), [56](#level-56), [60](#level-60), [64](#level-64), [68](#level-68), [70](#level-70), [72](#level-72), [78](#level-78), [80](#level-80), [81](#level-81), [84](#level-84), [88](#level-88), [90](#level-90), [96](#level-96), [100](#level-100), [104](#level-104), [108](#level-108), [110](#level-110), [112](#level-112), [120](#level-120), [126](#level-126), [128](#level-128), [132](#level-132), [135](#level-135), [140](#level-140), [144](#level-144), [150](#level-150), [160](#level-160), [162](#level-162), [168](#level-168), [176](#level-176), [180](#level-180), [192](#level-192), [200](#level-200), [204](#level-204), [208](#level-208), [210](#level-210), [216](#level-216), [220](#level-220), [224](#level-224), [228](#level-228), [234](#level-234), [240](#level-240), [252](#level-252), [256](#level-256), [260](#level-260), [264](#level-264), [270](#level-270), [276](#level-276), [280](#level-280), [288](#level-288), [294](#level-294), [300](#level-300), [308](#level-308), [312](#level-312), [320](#level-320), [324](#level-324), [330](#level-330), [336](#level-336), [340](#level-340), [350](#level-350), [352](#level-352), [360](#level-360), [378](#level-378), [384](#level-384), [390](#level-390), [392](#level-392), [396](#level-396), [400](#level-400), [405](#level-405), [408](#level-408), [416](#level-416), [420](#level-420), [432](#level-432), [440](#level-440), [448](#level-448), [450](#level-450), [456](#level-456), [462](#level-462), [468](#level-468), [480](#level-480), [486](#level-486)

## All levels

| N | Cusps | dim S₂ | Eta rank | Full eta basis | B |
| --- | --- | --- | --- | --- | --- |
| [1](#level-1) | 1 | 0 | 0 | YES | 0 |
| [2](#level-2) | 2 | 0 | 0 | YES | 0 |
| [3](#level-3) | 2 | 0 | 0 | YES | 0 |
| [4](#level-4) | 3 | 0 | 0 | YES | 1 |
| [5](#level-5) | 2 | 0 | 0 | YES | 1 |
| [6](#level-6) | 4 | 0 | 0 | YES | 2 |
| [7](#level-7) | 2 | 0 | 0 | YES | 1 |
| [8](#level-8) | 4 | 0 | 0 | YES | 2 |
| [9](#level-9) | 4 | 0 | 0 | YES | 2 |
| [10](#level-10) | 4 | 0 | 0 | YES | 3 |
| [11](#level-11) | 2 | 1 | 1 | YES | 2 |
| [12](#level-12) | 6 | 0 | 0 | YES | 4 |
| [13](#level-13) | 2 | 0 | 0 | YES | 2 |
| [14](#level-14) | 4 | 1 | 1 | YES | 4 |
| [15](#level-15) | 4 | 1 | 1 | YES | 4 |
| [16](#level-16) | 6 | 0 | 0 | YES | 4 |
| [17](#level-17) | 2 | 1 | 0 | NO | 3 |
| [18](#level-18) | 8 | 0 | 0 | YES | 6 |
| [19](#level-19) | 2 | 1 | 0 | NO | 3 |
| [20](#level-20) | 6 | 1 | 1 | YES | 6 |
| [21](#level-21) | 4 | 1 | 0 | NO | 5 |
| [22](#level-22) | 4 | 2 | 2 | YES | 6 |
| [23](#level-23) | 2 | 2 | 1 | NO | 4 |
| [24](#level-24) | 8 | 1 | 1 | YES | 8 |
| [25](#level-25) | 6 | 0 | 0 | YES | 5 |
| [26](#level-26) | 4 | 2 | 0 | NO | 7 |
| [27](#level-27) | 6 | 1 | 1 | YES | 6 |
| [28](#level-28) | 6 | 2 | 2 | YES | 8 |
| [29](#level-29) | 2 | 2 | 0 | NO | 5 |
| [30](#level-30) | 8 | 3 | 3 | YES | 12 |
| [31](#level-31) | 2 | 2 | 0 | NO | 5 |
| [32](#level-32) | 8 | 1 | 1 | YES | 8 |
| [33](#level-33) | 4 | 3 | 3 | YES | 8 |
| [34](#level-34) | 4 | 3 | 0 | NO | 9 |
| [35](#level-35) | 4 | 3 | 3 | YES | 8 |
| [36](#level-36) | 12 | 1 | 1 | YES | 12 |
| [37](#level-37) | 2 | 2 | 0 | NO | 6 |
| [38](#level-38) | 4 | 4 | 2 | NO | 10 |
| [39](#level-39) | 4 | 3 | 0 | NO | 9 |
| [40](#level-40) | 8 | 3 | 3 | YES | 12 |
| [41](#level-41) | 2 | 3 | 0 | NO | 7 |
| [42](#level-42) | 8 | 5 | 5 | YES | 16 |
| [43](#level-43) | 2 | 3 | 0 | NO | 7 |
| [44](#level-44) | 6 | 4 | 3 | NO | 12 |
| [45](#level-45) | 8 | 3 | 2 | NO | 12 |
| [46](#level-46) | 4 | 5 | 5 | YES | 12 |
| [47](#level-47) | 2 | 4 | 1 | NO | 8 |
| [48](#level-48) | 12 | 3 | 3 | YES | 16 |
| [49](#level-49) | 8 | 1 | 0 | NO | 9 |
| [50](#level-50) | 12 | 2 | 0 | NO | 15 |
| [51](#level-51) | 4 | 5 | 1 | NO | 12 |
| [52](#level-52) | 6 | 5 | 0 | NO | 14 |
| [53](#level-53) | 2 | 4 | 0 | NO | 9 |
| [54](#level-54) | 12 | 4 | 4 | YES | 18 |
| [55](#level-55) | 4 | 5 | 3 | NO | 12 |
| [56](#level-56) | 8 | 5 | 5 | YES | 16 |
| [57](#level-57) | 4 | 5 | 0 | NO | 13 |
| [58](#level-58) | 4 | 6 | 0 | NO | 15 |
| [59](#level-59) | 2 | 5 | 1 | NO | 10 |
| [60](#level-60) | 12 | 7 | 7 | YES | 24 |
| [61](#level-61) | 2 | 4 | 0 | NO | 10 |
| [62](#level-62) | 4 | 7 | 1 | NO | 16 |
| [63](#level-63) | 8 | 5 | 3 | NO | 16 |
| [64](#level-64) | 12 | 3 | 3 | YES | 16 |
| [65](#level-65) | 4 | 5 | 0 | NO | 14 |
| [66](#level-66) | 8 | 9 | 7 | NO | 24 |
| [67](#level-67) | 2 | 5 | 0 | NO | 11 |
| [68](#level-68) | 6 | 7 | 7 | YES | 18 |
| [69](#level-69) | 4 | 7 | 3 | NO | 16 |
| [70](#level-70) | 8 | 9 | 9 | YES | 24 |
| [71](#level-71) | 2 | 6 | 1 | NO | 12 |
| [72](#level-72) | 16 | 5 | 5 | YES | 24 |
| [73](#level-73) | 2 | 5 | 0 | NO | 12 |
| [74](#level-74) | 4 | 8 | 0 | NO | 19 |
| [75](#level-75) | 12 | 5 | 4 | NO | 20 |
| [76](#level-76) | 6 | 8 | 5 | NO | 20 |
| [77](#level-77) | 4 | 7 | 3 | NO | 16 |
| [78](#level-78) | 8 | 11 | 11 | YES | 28 |
| [79](#level-79) | 2 | 6 | 0 | NO | 13 |
| [80](#level-80) | 12 | 7 | 7 | YES | 24 |
| [81](#level-81) | 12 | 4 | 4 | YES | 18 |
| [82](#level-82) | 4 | 9 | 0 | NO | 21 |
| [83](#level-83) | 2 | 7 | 1 | NO | 14 |
| [84](#level-84) | 12 | 11 | 11 | YES | 32 |
| [85](#level-85) | 4 | 7 | 0 | NO | 18 |
| [86](#level-86) | 4 | 10 | 2 | NO | 22 |
| [87](#level-87) | 4 | 9 | 1 | NO | 20 |
| [88](#level-88) | 8 | 9 | 9 | YES | 24 |
| [89](#level-89) | 2 | 7 | 0 | NO | 15 |
| [90](#level-90) | 16 | 11 | 11 | YES | 36 |
| [91](#level-91) | 4 | 7 | 0 | NO | 18 |
| [92](#level-92) | 6 | 10 | 9 | NO | 24 |
| [93](#level-93) | 4 | 9 | 0 | NO | 21 |
| [94](#level-94) | 4 | 11 | 5 | NO | 24 |
| [95](#level-95) | 4 | 9 | 3 | NO | 20 |
| [96](#level-96) | 16 | 9 | 9 | YES | 32 |
| [97](#level-97) | 2 | 7 | 0 | NO | 16 |
| [98](#level-98) | 16 | 7 | 6 | NO | 28 |
| [99](#level-99) | 8 | 9 | 6 | NO | 24 |
| [100](#level-100) | 18 | 7 | 7 | YES | 30 |
| [101](#level-101) | 2 | 8 | 0 | NO | 17 |
| [102](#level-102) | 8 | 15 | 13 | NO | 36 |
| [103](#level-103) | 2 | 8 | 0 | NO | 17 |
| [104](#level-104) | 8 | 11 | 11 | YES | 28 |
| [105](#level-105) | 8 | 13 | 11 | NO | 32 |
| [106](#level-106) | 4 | 12 | 0 | NO | 27 |
| [107](#level-107) | 2 | 9 | 1 | NO | 18 |
| [108](#level-108) | 18 | 10 | 10 | YES | 36 |
| [109](#level-109) | 2 | 8 | 0 | NO | 18 |
| [110](#level-110) | 8 | 15 | 15 | YES | 36 |
| [111](#level-111) | 4 | 11 | 0 | NO | 25 |
| [112](#level-112) | 12 | 11 | 11 | YES | 32 |
| [113](#level-113) | 2 | 9 | 0 | NO | 19 |
| [114](#level-114) | 8 | 17 | 13 | NO | 40 |
| [115](#level-115) | 4 | 11 | 3 | NO | 24 |
| [116](#level-116) | 6 | 13 | 1 | NO | 30 |
| [117](#level-117) | 8 | 11 | 0 | NO | 28 |
| [118](#level-118) | 4 | 14 | 2 | NO | 30 |
| [119](#level-119) | 4 | 11 | 3 | NO | 24 |
| [120](#level-120) | 16 | 17 | 17 | YES | 48 |
| [121](#level-121) | 12 | 6 | 3 | NO | 22 |
| [122](#level-122) | 4 | 14 | 0 | NO | 31 |
| [123](#level-123) | 4 | 13 | 1 | NO | 28 |
| [124](#level-124) | 6 | 14 | 3 | NO | 32 |
| [125](#level-125) | 10 | 8 | 0 | NO | 25 |
| [126](#level-126) | 16 | 17 | 17 | YES | 48 |
| [127](#level-127) | 2 | 10 | 0 | NO | 21 |
| [128](#level-128) | 16 | 9 | 9 | YES | 32 |
| [129](#level-129) | 4 | 13 | 0 | NO | 29 |
| [130](#level-130) | 8 | 17 | 0 | NO | 42 |
| [131](#level-131) | 2 | 11 | 1 | NO | 22 |
| [132](#level-132) | 12 | 19 | 19 | YES | 48 |
| [133](#level-133) | 4 | 11 | 0 | NO | 26 |
| [134](#level-134) | 4 | 16 | 2 | NO | 34 |
| [135](#level-135) | 12 | 13 | 13 | YES | 36 |
| [136](#level-136) | 8 | 15 | 13 | NO | 36 |
| [137](#level-137) | 2 | 11 | 0 | NO | 23 |
| [138](#level-138) | 8 | 21 | 16 | NO | 48 |
| [139](#level-139) | 2 | 11 | 0 | NO | 23 |
| [140](#level-140) | 12 | 19 | 19 | YES | 48 |
| [141](#level-141) | 4 | 15 | 3 | NO | 32 |
| [142](#level-142) | 4 | 17 | 5 | NO | 36 |
| [143](#level-143) | 4 | 13 | 5 | NO | 28 |
| [144](#level-144) | 24 | 13 | 13 | YES | 48 |
| [145](#level-145) | 4 | 13 | 0 | NO | 30 |
| [146](#level-146) | 4 | 17 | 0 | NO | 37 |
| [147](#level-147) | 16 | 11 | 0 | NO | 37 |
| [148](#level-148) | 6 | 17 | 0 | NO | 38 |
| [149](#level-149) | 2 | 12 | 0 | NO | 25 |
| [150](#level-150) | 24 | 19 | 19 | YES | 60 |
| [151](#level-151) | 2 | 12 | 0 | NO | 25 |
| [152](#level-152) | 8 | 17 | 15 | NO | 40 |
| [153](#level-153) | 8 | 15 | 2 | NO | 36 |
| [154](#level-154) | 8 | 21 | 17 | NO | 48 |
| [155](#level-155) | 4 | 15 | 3 | NO | 32 |
| [156](#level-156) | 12 | 23 | 21 | NO | 56 |
| [157](#level-157) | 2 | 12 | 0 | NO | 26 |
| [158](#level-158) | 4 | 19 | 1 | NO | 40 |
| [159](#level-159) | 4 | 17 | 1 | NO | 36 |
| [160](#level-160) | 16 | 17 | 17 | YES | 48 |
| [161](#level-161) | 4 | 15 | 3 | NO | 32 |
| [162](#level-162) | 24 | 16 | 16 | YES | 54 |
| [163](#level-163) | 2 | 13 | 0 | NO | 27 |
| [164](#level-164) | 6 | 19 | 7 | NO | 42 |
| [165](#level-165) | 8 | 21 | 14 | NO | 48 |
| [166](#level-166) | 4 | 20 | 2 | NO | 42 |
| [167](#level-167) | 2 | 14 | 1 | NO | 28 |
| [168](#level-168) | 16 | 25 | 25 | YES | 64 |
| [169](#level-169) | 14 | 8 | 0 | NO | 30 |
| [170](#level-170) | 8 | 23 | 0 | NO | 54 |
| [171](#level-171) | 8 | 17 | 3 | NO | 40 |
| [172](#level-172) | 6 | 20 | 6 | NO | 44 |
| [173](#level-173) | 2 | 14 | 0 | NO | 29 |
| [174](#level-174) | 8 | 27 | 10 | NO | 60 |
| [175](#level-175) | 12 | 15 | 10 | NO | 40 |
| [176](#level-176) | 12 | 19 | 19 | YES | 48 |
| [177](#level-177) | 4 | 19 | 3 | NO | 40 |
| [178](#level-178) | 4 | 21 | 0 | NO | 45 |
| [179](#level-179) | 2 | 15 | 1 | NO | 30 |
| [180](#level-180) | 24 | 25 | 25 | YES | 72 |
| [181](#level-181) | 2 | 14 | 0 | NO | 30 |
| [182](#level-182) | 8 | 25 | 16 | NO | 56 |
| [183](#level-183) | 4 | 19 | 0 | NO | 41 |
| [184](#level-184) | 8 | 21 | 16 | NO | 48 |
| [185](#level-185) | 4 | 17 | 0 | NO | 38 |
| [186](#level-186) | 8 | 29 | 12 | NO | 64 |
| [187](#level-187) | 4 | 17 | 3 | NO | 36 |
| [188](#level-188) | 6 | 22 | 15 | NO | 48 |
| [189](#level-189) | 12 | 19 | 17 | NO | 48 |
| [190](#level-190) | 8 | 27 | 23 | NO | 60 |
| [191](#level-191) | 2 | 16 | 1 | NO | 32 |
| [192](#level-192) | 24 | 21 | 21 | YES | 64 |
| [193](#level-193) | 2 | 15 | 0 | NO | 32 |
| [194](#level-194) | 4 | 23 | 0 | NO | 49 |
| [195](#level-195) | 8 | 25 | 10 | NO | 56 |
| [196](#level-196) | 24 | 17 | 14 | NO | 56 |
| [197](#level-197) | 2 | 16 | 0 | NO | 33 |
| [198](#level-198) | 16 | 29 | 28 | NO | 72 |
| [199](#level-199) | 2 | 16 | 0 | NO | 33 |
| [200](#level-200) | 24 | 19 | 19 | YES | 60 |
| [201](#level-201) | 4 | 21 | 0 | NO | 45 |
| [202](#level-202) | 4 | 24 | 0 | NO | 51 |
| [203](#level-203) | 4 | 19 | 3 | NO | 40 |
| [204](#level-204) | 12 | 31 | 31 | YES | 72 |
| [205](#level-205) | 4 | 19 | 0 | NO | 42 |
| [206](#level-206) | 4 | 25 | 1 | NO | 52 |
| [207](#level-207) | 8 | 21 | 7 | NO | 48 |
| [208](#level-208) | 12 | 23 | 23 | YES | 56 |
| [209](#level-209) | 4 | 19 | 3 | NO | 40 |
| [210](#level-210) | 16 | 41 | 41 | YES | 96 |
| [211](#level-211) | 2 | 17 | 0 | NO | 35 |
| [212](#level-212) | 6 | 25 | 1 | NO | 54 |
| [213](#level-213) | 4 | 23 | 3 | NO | 48 |
| [214](#level-214) | 4 | 26 | 2 | NO | 54 |
| [215](#level-215) | 4 | 21 | 3 | NO | 44 |
| [216](#level-216) | 24 | 25 | 25 | YES | 72 |
| [217](#level-217) | 4 | 19 | 0 | NO | 42 |
| [218](#level-218) | 4 | 26 | 0 | NO | 55 |
| [219](#level-219) | 4 | 23 | 0 | NO | 49 |
| [220](#level-220) | 12 | 31 | 31 | YES | 72 |
| [221](#level-221) | 4 | 19 | 0 | NO | 42 |
| [222](#level-222) | 8 | 35 | 14 | NO | 76 |
| [223](#level-223) | 2 | 18 | 0 | NO | 37 |
| [224](#level-224) | 16 | 25 | 25 | YES | 64 |
| [225](#level-225) | 24 | 19 | 12 | NO | 60 |
| [226](#level-226) | 4 | 27 | 0 | NO | 57 |
| [227](#level-227) | 2 | 19 | 1 | NO | 38 |
| [228](#level-228) | 12 | 35 | 35 | YES | 80 |
| [229](#level-229) | 2 | 18 | 0 | NO | 38 |
| [230](#level-230) | 8 | 33 | 31 | NO | 72 |
| [231](#level-231) | 8 | 29 | 12 | NO | 64 |
| [232](#level-232) | 8 | 27 | 10 | NO | 60 |
| [233](#level-233) | 2 | 19 | 0 | NO | 39 |
| [234](#level-234) | 16 | 35 | 35 | YES | 84 |
| [235](#level-235) | 4 | 23 | 3 | NO | 48 |
| [236](#level-236) | 6 | 28 | 4 | NO | 60 |
| [237](#level-237) | 4 | 25 | 0 | NO | 53 |
| [238](#level-238) | 8 | 33 | 27 | NO | 72 |
| [239](#level-239) | 2 | 20 | 1 | NO | 40 |
| [240](#level-240) | 24 | 37 | 37 | YES | 96 |
| [241](#level-241) | 2 | 19 | 0 | NO | 40 |
| [242](#level-242) | 24 | 22 | 10 | NO | 66 |
| [243](#level-243) | 18 | 19 | 16 | NO | 54 |
| [244](#level-244) | 6 | 29 | 0 | NO | 62 |
| [245](#level-245) | 16 | 21 | 10 | NO | 56 |
| [246](#level-246) | 8 | 39 | 14 | NO | 84 |
| [247](#level-247) | 4 | 21 | 0 | NO | 46 |
| [248](#level-248) | 8 | 29 | 11 | NO | 64 |
| [249](#level-249) | 4 | 27 | 3 | NO | 56 |
| [250](#level-250) | 20 | 28 | 0 | NO | 75 |
| [251](#level-251) | 2 | 21 | 1 | NO | 42 |
| [252](#level-252) | 24 | 37 | 37 | YES | 96 |
| [253](#level-253) | 4 | 23 | 5 | NO | 48 |
| [254](#level-254) | 4 | 31 | 1 | NO | 64 |
| [255](#level-255) | 8 | 33 | 10 | NO | 72 |
| [256](#level-256) | 24 | 21 | 21 | YES | 64 |
| [257](#level-257) | 2 | 21 | 0 | NO | 43 |
| [258](#level-258) | 8 | 41 | 16 | NO | 88 |
| [259](#level-259) | 4 | 23 | 0 | NO | 50 |
| [260](#level-260) | 12 | 37 | 37 | YES | 84 |
| [261](#level-261) | 8 | 27 | 2 | NO | 60 |
| [262](#level-262) | 4 | 32 | 2 | NO | 66 |
| [263](#level-263) | 2 | 22 | 1 | NO | 44 |
| [264](#level-264) | 16 | 41 | 41 | YES | 96 |
| [265](#level-265) | 4 | 25 | 0 | NO | 54 |
| [266](#level-266) | 8 | 37 | 18 | NO | 80 |
| [267](#level-267) | 4 | 29 | 1 | NO | 60 |
| [268](#level-268) | 6 | 32 | 6 | NO | 68 |
| [269](#level-269) | 2 | 22 | 0 | NO | 45 |
| [270](#level-270) | 24 | 43 | 43 | YES | 108 |
| [271](#level-271) | 2 | 22 | 0 | NO | 45 |
| [272](#level-272) | 12 | 31 | 30 | NO | 72 |
| [273](#level-273) | 8 | 33 | 0 | NO | 74 |
| [274](#level-274) | 4 | 33 | 0 | NO | 69 |
| [275](#level-275) | 12 | 25 | 13 | NO | 60 |
| [276](#level-276) | 12 | 43 | 43 | YES | 96 |
| [277](#level-277) | 2 | 22 | 0 | NO | 46 |
| [278](#level-278) | 4 | 34 | 2 | NO | 70 |
| [279](#level-279) | 8 | 29 | 3 | NO | 64 |
| [280](#level-280) | 16 | 41 | 41 | YES | 96 |
| [281](#level-281) | 2 | 23 | 0 | NO | 47 |
| [282](#level-282) | 8 | 45 | 28 | NO | 96 |
| [283](#level-283) | 2 | 23 | 0 | NO | 47 |
| [284](#level-284) | 6 | 34 | 18 | NO | 72 |
| [285](#level-285) | 8 | 37 | 14 | NO | 80 |
| [286](#level-286) | 8 | 39 | 33 | NO | 84 |
| [287](#level-287) | 4 | 27 | 3 | NO | 56 |
| [288](#level-288) | 32 | 33 | 33 | YES | 96 |
| [289](#level-289) | 18 | 17 | 0 | NO | 51 |
| [290](#level-290) | 8 | 41 | 0 | NO | 90 |
| [291](#level-291) | 4 | 31 | 0 | NO | 65 |
| [292](#level-292) | 6 | 35 | 0 | NO | 74 |
| [293](#level-293) | 2 | 24 | 0 | NO | 49 |
| [294](#level-294) | 32 | 41 | 41 | YES | 112 |
| [295](#level-295) | 4 | 29 | 3 | NO | 60 |
| [296](#level-296) | 8 | 35 | 12 | NO | 76 |
| [297](#level-297) | 12 | 31 | 22 | NO | 72 |
| [298](#level-298) | 4 | 36 | 0 | NO | 75 |
| [299](#level-299) | 4 | 27 | 5 | NO | 56 |
| [300](#level-300) | 36 | 43 | 43 | YES | 120 |
| [301](#level-301) | 4 | 27 | 0 | NO | 58 |
| [302](#level-302) | 4 | 37 | 1 | NO | 76 |
| [303](#level-303) | 4 | 33 | 1 | NO | 68 |
| [304](#level-304) | 12 | 35 | 34 | NO | 80 |
| [305](#level-305) | 4 | 29 | 0 | NO | 62 |
| [306](#level-306) | 16 | 47 | 45 | NO | 108 |
| [307](#level-307) | 2 | 25 | 0 | NO | 51 |
| [308](#level-308) | 12 | 43 | 43 | YES | 96 |
| [309](#level-309) | 4 | 33 | 0 | NO | 69 |
| [310](#level-310) | 8 | 45 | 22 | NO | 96 |
| [311](#level-311) | 2 | 26 | 1 | NO | 52 |
| [312](#level-312) | 16 | 49 | 49 | YES | 112 |
| [313](#level-313) | 2 | 25 | 0 | NO | 52 |
| [314](#level-314) | 4 | 38 | 0 | NO | 79 |
| [315](#level-315) | 16 | 41 | 30 | NO | 96 |
| [316](#level-316) | 6 | 38 | 3 | NO | 80 |
| [317](#level-317) | 2 | 26 | 0 | NO | 53 |
| [318](#level-318) | 8 | 51 | 10 | NO | 108 |
| [319](#level-319) | 4 | 29 | 3 | NO | 60 |
| [320](#level-320) | 24 | 37 | 37 | YES | 96 |
| [321](#level-321) | 4 | 35 | 3 | NO | 72 |
| [322](#level-322) | 8 | 45 | 28 | NO | 96 |
| [323](#level-323) | 4 | 29 | 3 | NO | 60 |
| [324](#level-324) | 36 | 37 | 37 | YES | 108 |
| [325](#level-325) | 12 | 29 | 0 | NO | 70 |
| [326](#level-326) | 4 | 40 | 2 | NO | 82 |
| [327](#level-327) | 4 | 35 | 0 | NO | 73 |
| [328](#level-328) | 8 | 39 | 22 | NO | 84 |
| [329](#level-329) | 4 | 31 | 3 | NO | 64 |
| [330](#level-330) | 16 | 65 | 65 | YES | 144 |
| [331](#level-331) | 2 | 27 | 0 | NO | 55 |
| [332](#level-332) | 6 | 40 | 4 | NO | 84 |
| [333](#level-333) | 8 | 35 | 0 | NO | 76 |
| [334](#level-334) | 4 | 41 | 5 | NO | 84 |
| [335](#level-335) | 4 | 33 | 3 | NO | 68 |
| [336](#level-336) | 24 | 53 | 53 | YES | 128 |
| [337](#level-337) | 2 | 27 | 0 | NO | 56 |
| [338](#level-338) | 28 | 32 | 0 | NO | 91 |
| [339](#level-339) | 4 | 37 | 1 | NO | 76 |
| [340](#level-340) | 12 | 49 | 49 | YES | 108 |
| [341](#level-341) | 4 | 31 | 3 | NO | 64 |
| [342](#level-342) | 16 | 53 | 49 | NO | 120 |
| [343](#level-343) | 14 | 26 | 0 | NO | 65 |
| [344](#level-344) | 8 | 41 | 18 | NO | 88 |
| [345](#level-345) | 8 | 45 | 14 | NO | 96 |
| [346](#level-346) | 4 | 42 | 0 | NO | 87 |
| [347](#level-347) | 2 | 29 | 1 | NO | 58 |
| [348](#level-348) | 12 | 55 | 44 | NO | 120 |
| [349](#level-349) | 2 | 28 | 0 | NO | 58 |
| [350](#level-350) | 24 | 49 | 49 | YES | 120 |
| [351](#level-351) | 12 | 37 | 10 | NO | 84 |
| [352](#level-352) | 16 | 41 | 41 | YES | 96 |
| [353](#level-353) | 2 | 29 | 0 | NO | 59 |
| [354](#level-354) | 8 | 57 | 14 | NO | 120 |
| [355](#level-355) | 4 | 35 | 3 | NO | 72 |
| [356](#level-356) | 6 | 43 | 7 | NO | 90 |
| [357](#level-357) | 8 | 45 | 12 | NO | 96 |
| [358](#level-358) | 4 | 44 | 2 | NO | 90 |
| [359](#level-359) | 2 | 30 | 1 | NO | 60 |
| [360](#level-360) | 32 | 57 | 57 | YES | 144 |
| [361](#level-361) | 20 | 22 | 0 | NO | 63 |
| [362](#level-362) | 4 | 44 | 0 | NO | 91 |
| [363](#level-363) | 24 | 33 | 10 | NO | 88 |
| [364](#level-364) | 12 | 51 | 40 | NO | 112 |
| [365](#level-365) | 4 | 35 | 0 | NO | 74 |
| [366](#level-366) | 8 | 59 | 16 | NO | 124 |
| [367](#level-367) | 2 | 30 | 0 | NO | 61 |
| [368](#level-368) | 12 | 43 | 36 | NO | 96 |
| [369](#level-369) | 8 | 39 | 2 | NO | 84 |
| [370](#level-370) | 8 | 53 | 0 | NO | 114 |
| [371](#level-371) | 4 | 35 | 3 | NO | 72 |
| [372](#level-372) | 12 | 59 | 58 | NO | 128 |
| [373](#level-373) | 2 | 30 | 0 | NO | 62 |
| [374](#level-374) | 8 | 51 | 18 | NO | 108 |
| [375](#level-375) | 20 | 41 | 16 | NO | 100 |
| [376](#level-376) | 8 | 45 | 28 | NO | 96 |
| [377](#level-377) | 4 | 33 | 0 | NO | 70 |
| [378](#level-378) | 24 | 61 | 61 | YES | 144 |
| [379](#level-379) | 2 | 31 | 0 | NO | 63 |
| [380](#level-380) | 12 | 55 | 49 | NO | 120 |
| [381](#level-381) | 4 | 41 | 0 | NO | 85 |
| [382](#level-382) | 4 | 47 | 5 | NO | 96 |
| [383](#level-383) | 2 | 32 | 1 | NO | 64 |
| [384](#level-384) | 32 | 49 | 49 | YES | 128 |
| [385](#level-385) | 8 | 45 | 18 | NO | 96 |
| [386](#level-386) | 4 | 47 | 0 | NO | 97 |
| [387](#level-387) | 8 | 41 | 3 | NO | 88 |
| [388](#level-388) | 6 | 47 | 0 | NO | 98 |
| [389](#level-389) | 2 | 32 | 0 | NO | 65 |
| [390](#level-390) | 16 | 77 | 77 | YES | 168 |
| [391](#level-391) | 4 | 35 | 3 | NO | 72 |
| [392](#level-392) | 32 | 41 | 41 | YES | 112 |
| [393](#level-393) | 4 | 43 | 3 | NO | 88 |
| [394](#level-394) | 4 | 48 | 0 | NO | 99 |
| [395](#level-395) | 4 | 39 | 3 | NO | 80 |
| [396](#level-396) | 24 | 61 | 61 | YES | 144 |
| [397](#level-397) | 2 | 32 | 0 | NO | 66 |
| [398](#level-398) | 4 | 49 | 1 | NO | 100 |
| [399](#level-399) | 8 | 49 | 0 | NO | 106 |
| [400](#level-400) | 36 | 43 | 43 | YES | 120 |
| [401](#level-401) | 2 | 33 | 0 | NO | 67 |
| [402](#level-402) | 8 | 65 | 16 | NO | 136 |
| [403](#level-403) | 4 | 35 | 0 | NO | 74 |
| [404](#level-404) | 6 | 49 | 1 | NO | 102 |
| [405](#level-405) | 24 | 43 | 43 | YES | 108 |
| [406](#level-406) | 8 | 57 | 18 | NO | 120 |
| [407](#level-407) | 4 | 37 | 5 | NO | 76 |
| [408](#level-408) | 16 | 65 | 65 | YES | 144 |
| [409](#level-409) | 2 | 33 | 0 | NO | 68 |
| [410](#level-410) | 8 | 59 | 0 | NO | 126 |
| [411](#level-411) | 4 | 45 | 1 | NO | 92 |
| [412](#level-412) | 6 | 50 | 3 | NO | 104 |
| [413](#level-413) | 4 | 39 | 3 | NO | 80 |
| [414](#level-414) | 16 | 65 | 56 | NO | 144 |
| [415](#level-415) | 4 | 41 | 3 | NO | 84 |
| [416](#level-416) | 16 | 49 | 49 | YES | 112 |
| [417](#level-417) | 4 | 45 | 0 | NO | 93 |
| [418](#level-418) | 8 | 57 | 18 | NO | 120 |
| [419](#level-419) | 2 | 35 | 1 | NO | 70 |
| [420](#level-420) | 24 | 85 | 85 | YES | 192 |
| [421](#level-421) | 2 | 34 | 0 | NO | 70 |
| [422](#level-422) | 4 | 52 | 2 | NO | 106 |
| [423](#level-423) | 8 | 45 | 7 | NO | 96 |
| [424](#level-424) | 8 | 51 | 10 | NO | 108 |
| [425](#level-425) | 12 | 39 | 0 | NO | 90 |
| [426](#level-426) | 8 | 69 | 38 | NO | 144 |
| [427](#level-427) | 4 | 39 | 0 | NO | 82 |
| [428](#level-428) | 6 | 52 | 4 | NO | 108 |
| [429](#level-429) | 8 | 53 | 18 | NO | 112 |
| [430](#level-430) | 8 | 63 | 32 | NO | 132 |
| [431](#level-431) | 2 | 36 | 1 | NO | 72 |
| [432](#level-432) | 36 | 55 | 55 | YES | 144 |
| [433](#level-433) | 2 | 35 | 0 | NO | 72 |
| [434](#level-434) | 8 | 61 | 20 | NO | 128 |
| [435](#level-435) | 8 | 57 | 10 | NO | 120 |
| [436](#level-436) | 6 | 53 | 0 | NO | 110 |
| [437](#level-437) | 4 | 39 | 3 | NO | 80 |
| [438](#level-438) | 8 | 71 | 0 | NO | 148 |
| [439](#level-439) | 2 | 36 | 0 | NO | 73 |
| [440](#level-440) | 16 | 65 | 65 | YES | 144 |
| [441](#level-441) | 32 | 41 | 13 | NO | 112 |
| [442](#level-442) | 8 | 59 | 0 | NO | 126 |
| [443](#level-443) | 2 | 37 | 1 | NO | 74 |
| [444](#level-444) | 12 | 71 | 52 | NO | 152 |
| [445](#level-445) | 4 | 43 | 0 | NO | 90 |
| [446](#level-446) | 4 | 55 | 1 | NO | 112 |
| [447](#level-447) | 4 | 49 | 1 | NO | 100 |
| [448](#level-448) | 24 | 53 | 53 | YES | 128 |
| [449](#level-449) | 2 | 37 | 0 | NO | 75 |
| [450](#level-450) | 48 | 67 | 67 | YES | 180 |
| [451](#level-451) | 4 | 41 | 3 | NO | 84 |
| [452](#level-452) | 6 | 55 | 7 | NO | 114 |
| [453](#level-453) | 4 | 49 | 0 | NO | 101 |
| [454](#level-454) | 4 | 56 | 2 | NO | 114 |
| [455](#level-455) | 8 | 53 | 18 | NO | 112 |
| [456](#level-456) | 16 | 73 | 73 | YES | 160 |
| [457](#level-457) | 2 | 37 | 0 | NO | 76 |
| [458](#level-458) | 4 | 56 | 0 | NO | 115 |
| [459](#level-459) | 12 | 49 | 14 | NO | 108 |
| [460](#level-460) | 12 | 67 | 66 | NO | 144 |
| [461](#level-461) | 2 | 38 | 0 | NO | 77 |
| [462](#level-462) | 16 | 89 | 89 | YES | 192 |
| [463](#level-463) | 2 | 38 | 0 | NO | 77 |
| [464](#level-464) | 12 | 55 | 37 | NO | 120 |
| [465](#level-465) | 8 | 61 | 14 | NO | 128 |
| [466](#level-466) | 4 | 57 | 0 | NO | 117 |
| [467](#level-467) | 2 | 39 | 1 | NO | 78 |
| [468](#level-468) | 24 | 73 | 73 | YES | 168 |
| [469](#level-469) | 4 | 43 | 0 | NO | 90 |
| [470](#level-470) | 8 | 69 | 32 | NO | 144 |
| [471](#level-471) | 4 | 51 | 0 | NO | 105 |
| [472](#level-472) | 8 | 57 | 21 | NO | 120 |
| [473](#level-473) | 4 | 43 | 3 | NO | 88 |
| [474](#level-474) | 8 | 77 | 12 | NO | 160 |
| [475](#level-475) | 12 | 45 | 10 | NO | 100 |
| [476](#level-476) | 12 | 67 | 66 | NO | 144 |
| [477](#level-477) | 8 | 51 | 2 | NO | 108 |
| [478](#level-478) | 4 | 59 | 5 | NO | 120 |
| [479](#level-479) | 2 | 40 | 1 | NO | 80 |
| [480](#level-480) | 32 | 81 | 81 | YES | 192 |
| [481](#level-481) | 4 | 41 | 0 | NO | 88 |
| [482](#level-482) | 4 | 59 | 0 | NO | 121 |
| [483](#level-483) | 8 | 61 | 12 | NO | 128 |
| [484](#level-484) | 36 | 49 | 20 | NO | 132 |
| [485](#level-485) | 4 | 47 | 0 | NO | 98 |
| [486](#level-486) | 36 | 64 | 64 | YES | 162 |
| [487](#level-487) | 2 | 40 | 0 | NO | 81 |
| [488](#level-488) | 8 | 59 | 12 | NO | 124 |
| [489](#level-489) | 4 | 53 | 0 | NO | 109 |
| [490](#level-490) | 32 | 69 | 61 | NO | 168 |
| [491](#level-491) | 2 | 41 | 1 | NO | 82 |
| [492](#level-492) | 12 | 79 | 67 | NO | 168 |
| [493](#level-493) | 4 | 43 | 0 | NO | 90 |
| [494](#level-494) | 8 | 67 | 18 | NO | 140 |
| [495](#level-495) | 16 | 65 | 44 | NO | 144 |
| [496](#level-496) | 12 | 59 | 39 | NO | 128 |
| [497](#level-497) | 4 | 47 | 3 | NO | 96 |
| [498](#level-498) | 8 | 81 | 14 | NO | 168 |
| [499](#level-499) | 2 | 41 | 0 | NO | 83 |
| [500](#level-500) | 30 | 61 | 49 | NO | 150 |

## Cuspidal eta exponent vectors by level

The vectors retain their order in the source report. A `NO` flag means a partial span only.

### Level 1

dim S₂ = **0**; eta rank = **0**; full eta basis = **YES**; Sturm bound B = **0**.

Empty basis of the zero space. No nontrivial folder is required.

`Basis_cuspidal_eta_S2 = []`.

### Level 2

dim S₂ = **0**; eta rank = **0**; full eta basis = **YES**; Sturm bound B = **0**.

Empty basis of the zero space. No nontrivial folder is required.

`Basis_cuspidal_eta_S2 = []`.

### Level 3

dim S₂ = **0**; eta rank = **0**; full eta basis = **YES**; Sturm bound B = **0**.

Empty basis of the zero space. No nontrivial folder is required.

`Basis_cuspidal_eta_S2 = []`.

### Level 4

dim S₂ = **0**; eta rank = **0**; full eta basis = **YES**; Sturm bound B = **1**.

Empty basis of the zero space. No nontrivial folder is required.

`Basis_cuspidal_eta_S2 = []`.

### Level 5

dim S₂ = **0**; eta rank = **0**; full eta basis = **YES**; Sturm bound B = **1**.

Empty basis of the zero space. No nontrivial folder is required.

`Basis_cuspidal_eta_S2 = []`.

### Level 6

dim S₂ = **0**; eta rank = **0**; full eta basis = **YES**; Sturm bound B = **2**.

Empty basis of the zero space. No nontrivial folder is required.

`Basis_cuspidal_eta_S2 = []`.

### Level 7

dim S₂ = **0**; eta rank = **0**; full eta basis = **YES**; Sturm bound B = **1**.

Empty basis of the zero space. No nontrivial folder is required.

`Basis_cuspidal_eta_S2 = []`.

### Level 8

dim S₂ = **0**; eta rank = **0**; full eta basis = **YES**; Sturm bound B = **2**.

Empty basis of the zero space. No nontrivial folder is required.

`Basis_cuspidal_eta_S2 = []`.

### Level 9

dim S₂ = **0**; eta rank = **0**; full eta basis = **YES**; Sturm bound B = **2**.

Empty basis of the zero space. No nontrivial folder is required.

`Basis_cuspidal_eta_S2 = []`.

### Level 10

dim S₂ = **0**; eta rank = **0**; full eta basis = **YES**; Sturm bound B = **3**.

Empty basis of the zero space. No nontrivial folder is required.

`Basis_cuspidal_eta_S2 = []`.

### Level 11

dim S₂ = **1**; eta rank = **1**; full eta basis = **YES**; Sturm bound B = **2**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![11; 0 => 2, 10 => 2],
]
```

### Level 12

dim S₂ = **0**; eta rank = **0**; full eta basis = **YES**; Sturm bound B = **4**.

Empty basis of the zero space. No nontrivial folder is required.

`Basis_cuspidal_eta_S2 = []`.

### Level 13

dim S₂ = **0**; eta rank = **0**; full eta basis = **YES**; Sturm bound B = **2**.

Empty basis of the zero space. No nontrivial folder is required.

`Basis_cuspidal_eta_S2 = []`.

### Level 14

dim S₂ = **1**; eta rank = **1**; full eta basis = **YES**; Sturm bound B = **4**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![14; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
]
```

### Level 15

dim S₂ = **1**; eta rank = **1**; full eta basis = **YES**; Sturm bound B = **4**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![15; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
]
```

### Level 16

dim S₂ = **0**; eta rank = **0**; full eta basis = **YES**; Sturm bound B = **4**.

Empty basis of the zero space. No nontrivial folder is required.

`Basis_cuspidal_eta_S2 = []`.

### Level 17

dim S₂ = **1**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **3**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 18

dim S₂ = **0**; eta rank = **0**; full eta basis = **YES**; Sturm bound B = **6**.

Empty basis of the zero space. No nontrivial folder is required.

`Basis_cuspidal_eta_S2 = []`.

### Level 19

dim S₂ = **1**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **3**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 20

dim S₂ = **1**; eta rank = **1**; full eta basis = **YES**; Sturm bound B = **6**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![20; 1 => 2, 9 => 2],
]
```

### Level 21

dim S₂ = **1**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **5**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 22

dim S₂ = **2**; eta rank = **2**; full eta basis = **YES**; Sturm bound B = **6**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![22; 0 => 2, 10 => 2],
  sparse![22; 1 => 2, 21 => 2],
]
```

### Level 23

dim S₂ = **2**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **4**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![23; 0 => 2, 22 => 2],
]
```

### Level 24

dim S₂ = **1**; eta rank = **1**; full eta basis = **YES**; Sturm bound B = **8**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![24; 1 => 1, 3 => 1, 5 => 1, 11 => 1],
]
```

### Level 25

dim S₂ = **0**; eta rank = **0**; full eta basis = **YES**; Sturm bound B = **5**.

Empty basis of the zero space. No nontrivial folder is required.

`Basis_cuspidal_eta_S2 = []`.

### Level 26

dim S₂ = **2**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **7**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 27

dim S₂ = **1**; eta rank = **1**; full eta basis = **YES**; Sturm bound B = **6**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![27; 2 => 2, 8 => 2],
]
```

### Level 28

dim S₂ = **2**; eta rank = **2**; full eta basis = **YES**; Sturm bound B = **8**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![28; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![28; 1 => 1, 3 => 1, 13 => 1, 27 => 1],
]
```

### Level 29

dim S₂ = **2**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **5**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 30

dim S₂ = **3**; eta rank = **3**; full eta basis = **YES**; Sturm bound B = **12**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![30; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![30; 1 => 1, 5 => 1, 9 => 1, 29 => 1],
  sparse![30; 0 => 1, 1 => 1, 14 => 1, 29 => 1],
]
```

### Level 31

dim S₂ = **2**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **5**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 32

dim S₂ = **1**; eta rank = **1**; full eta basis = **YES**; Sturm bound B = **8**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![32; 3 => 2, 7 => 2],
]
```

### Level 33

dim S₂ = **3**; eta rank = **3**; full eta basis = **YES**; Sturm bound B = **8**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![33; 0 => 2, 10 => 2],
  sparse![33; 2 => 2, 32 => 2],
  sparse![33; 0 => 1, 2 => 1, 10 => 1, 32 => 1],
]
```

### Level 34

dim S₂ = **3**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **9**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 35

dim S₂ = **3**; eta rank = **3**; full eta basis = **YES**; Sturm bound B = **8**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![35; 0 => 2, 34 => 2],
  sparse![35; 0 => 1, 4 => 1, 6 => 1, 34 => 1],
  sparse![35; 4 => 2, 6 => 2],
]
```

### Level 36

dim S₂ = **1**; eta rank = **1**; full eta basis = **YES**; Sturm bound B = **12**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![36; 5 => 4],
]
```

### Level 37

dim S₂ = **2**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **6**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 38

dim S₂ = **4**; eta rank = **2**; full eta basis = **NO**; Sturm bound B = **10**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![38; 0 => 3, 1 => -1, 18 => -1, 37 => 3],
  sparse![38; 0 => -1, 1 => 3, 18 => 3, 37 => -1],
]
```

### Level 39

dim S₂ = **3**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **9**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 40

dim S₂ = **3**; eta rank = **3**; full eta basis = **YES**; Sturm bound B = **12**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![40; 1 => 2, 9 => 2],
  sparse![40; 3 => 2, 19 => 2],
  sparse![40; 0 => -2, 1 => 5, 3 => -1, 4 => 2, 9 => -1, 19 => 1],
]
```

### Level 41

dim S₂ = **3**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **7**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 42

dim S₂ = **5**; eta rank = **5**; full eta basis = **YES**; Sturm bound B = **16**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![42; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![42; 2 => 1, 5 => 1, 20 => 1, 41 => 1],
  sparse![42; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 6 => 4, 13 => -2, 20 => -1, 41 => 1],
  sparse![42; 0 => -1, 1 => 1, 2 => 4, 5 => -2, 6 => 1, 13 => -1, 20 => -2, 41 => 4],
  sparse![42; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 6 => -1, 13 => 2, 20 => 2, 41 => -1],
]
```

### Level 43

dim S₂ = **3**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **7**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 44

dim S₂ = **4**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **12**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![44; 0 => 2, 10 => 2],
  sparse![44; 1 => 2, 21 => 2],
  sparse![44; 3 => 2, 43 => 2],
]
```

### Level 45

dim S₂ = **3**; eta rank = **2**; full eta basis = **NO**; Sturm bound B = **12**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![45; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![45; 2 => 1, 8 => 1, 14 => 1, 44 => 1],
]
```

### Level 46

dim S₂ = **5**; eta rank = **5**; full eta basis = **YES**; Sturm bound B = **12**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![46; 0 => 2, 22 => 2],
  sparse![46; 1 => 2, 45 => 2],
  sparse![46; 0 => -1, 1 => 3, 22 => -1, 45 => 3],
  sparse![46; 0 => 1, 1 => 1, 22 => 1, 45 => 1],
  sparse![46; 0 => 3, 1 => -1, 22 => 3, 45 => -1],
]
```

### Level 47

dim S₂ = **4**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **8**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![47; 0 => 2, 46 => 2],
]
```

### Level 48

dim S₂ = **3**; eta rank = **3**; full eta basis = **YES**; Sturm bound B = **16**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![48; 1 => 1, 3 => 1, 5 => 1, 11 => 1],
  sparse![48; 3 => 1, 7 => 1, 11 => 1, 23 => 1],
  sparse![48; 0 => -2, 1 => 4, 2 => 2, 5 => -2, 11 => 2],
]
```

### Level 49

dim S₂ = **1**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **9**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 50

dim S₂ = **2**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **15**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 51

dim S₂ = **5**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **12**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![51; 0 => 1, 2 => 1, 16 => 1, 50 => 1],
]
```

### Level 52

dim S₂ = **5**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **14**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 53

dim S₂ = **4**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **9**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 54

dim S₂ = **4**; eta rank = **4**; full eta basis = **YES**; Sturm bound B = **18**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![54; 2 => 2, 8 => 2],
  sparse![54; 5 => 2, 17 => 2],
  sparse![54; 0 => -1, 1 => 2, 5 => 2, 8 => 1],
  sparse![54; 0 => -1, 1 => 2, 2 => 1, 17 => 1, 26 => 2, 53 => -1],
]
```

### Level 55

dim S₂ = **5**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **12**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![55; 0 => 2, 10 => 2],
  sparse![55; 4 => 2, 54 => 2],
  sparse![55; 0 => 1, 4 => 1, 10 => 1, 54 => 1],
]
```

### Level 56

dim S₂ = **5**; eta rank = **5**; full eta basis = **YES**; Sturm bound B = **16**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![56; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![56; 1 => 1, 3 => 1, 13 => 1, 27 => 1],
  sparse![56; 3 => 1, 7 => 1, 27 => 1, 55 => 1],
  sparse![56; 0 => 1, 6 => 1, 7 => 1, 55 => 1],
  sparse![56; 1 => -1, 3 => 3, 13 => 3, 27 => -1],
]
```

### Level 57

dim S₂ = **5**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **13**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 58

dim S₂ = **6**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **15**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 59

dim S₂ = **5**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **10**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![59; 0 => 2, 58 => 2],
]
```

### Level 60

dim S₂ = **7**; eta rank = **7**; full eta basis = **YES**; Sturm bound B = **24**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![60; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![60; 1 => 1, 5 => 1, 9 => 1, 29 => 1],
  sparse![60; 3 => 1, 11 => 1, 19 => 1, 59 => 1],
  sparse![60; 1 => 2, 9 => 2],
  sparse![60; 5 => 2, 29 => 2],
  sparse![60; 0 => 1, 1 => 1, 14 => 1, 29 => 1],
  sparse![60; 1 => 1, 3 => 1, 29 => 1, 59 => 1],
]
```

### Level 61

dim S₂ = **4**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **10**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 62

dim S₂ = **7**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **16**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![62; 0 => 1, 1 => 1, 30 => 1, 61 => 1],
]
```

### Level 63

dim S₂ = **5**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **16**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![63; 2 => 2, 20 => 2],
  sparse![63; 0 => -1, 2 => 4, 6 => 1, 8 => -1, 62 => 1],
  sparse![63; 0 => 1, 6 => -1, 8 => 1, 20 => 4, 62 => -1],
]
```

### Level 64

dim S₂ = **3**; eta rank = **3**; full eta basis = **YES**; Sturm bound B = **16**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![64; 3 => 2, 7 => 2],
  sparse![64; 7 => 2, 15 => 2],
  sparse![64; 0 => -2, 1 => 5, 3 => -2, 7 => 3],
]
```

### Level 65

dim S₂ = **5**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **14**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 66

dim S₂ = **9**; eta rank = **7**; full eta basis = **NO**; Sturm bound B = **24**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![66; 0 => 2, 10 => 2],
  sparse![66; 1 => 2, 21 => 2],
  sparse![66; 2 => 2, 32 => 2],
  sparse![66; 5 => 2, 65 => 2],
  sparse![66; 0 => 1, 2 => 1, 10 => 1, 32 => 1],
  sparse![66; 1 => 1, 5 => 1, 21 => 1, 65 => 1],
  sparse![66; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 10 => -1, 21 => 1, 32 => 3, 65 => -1],
]
```

### Level 67

dim S₂ = **5**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **11**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 68

dim S₂ = **7**; eta rank = **7**; full eta basis = **YES**; Sturm bound B = **18**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![68; 0 => 2, 1 => -1, 3 => 1, 16 => -2, 33 => 5, 67 => -1],
  sparse![68; 0 => 1, 1 => -1, 3 => 2, 16 => -1, 33 => 5, 67 => -2],
  sparse![68; 0 => 1, 1 => 2, 3 => -1, 16 => -1, 33 => 2, 67 => 1],
  sparse![68; 1 => 2, 33 => 2],
  sparse![68; 0 => -1, 1 => 2, 3 => 1, 16 => 1, 33 => 2, 67 => -1],
  sparse![68; 0 => -1, 1 => 5, 3 => -2, 16 => 1, 33 => -1, 67 => 2],
  sparse![68; 0 => -2, 1 => 5, 3 => -1, 16 => 2, 33 => -1, 67 => 1],
]
```

### Level 69

dim S₂ = **7**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **16**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![69; 0 => 2, 22 => 2],
  sparse![69; 2 => 2, 68 => 2],
  sparse![69; 0 => 1, 2 => 1, 22 => 1, 68 => 1],
]
```

### Level 70

dim S₂ = **9**; eta rank = **9**; full eta basis = **YES**; Sturm bound B = **24**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![70; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![70; 4 => 1, 9 => 1, 34 => 1, 69 => 1],
  sparse![70; 0 => 2, 34 => 2],
  sparse![70; 0 => 1, 4 => 1, 6 => 1, 34 => 1],
  sparse![70; 4 => 2, 6 => 2],
  sparse![70; 1 => 2, 69 => 2],
  sparse![70; 1 => 1, 9 => 1, 13 => 1, 69 => 1],
  sparse![70; 9 => 2, 13 => 2],
  sparse![70; 0 => 1, 4 => 2, 9 => -1, 13 => 1, 34 => -1, 69 => 2],
]
```

### Level 71

dim S₂ = **6**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **12**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![71; 0 => 2, 70 => 2],
]
```

### Level 72

dim S₂ = **5**; eta rank = **5**; full eta basis = **YES**; Sturm bound B = **24**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![72; 1 => 1, 3 => 1, 5 => 1, 11 => 1],
  sparse![72; 5 => 1, 11 => 1, 17 => 1, 35 => 1],
  sparse![72; 5 => 4],
  sparse![72; 11 => 4],
  sparse![72; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -1, 11 => 2],
]
```

### Level 73

dim S₂ = **5**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **12**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 74

dim S₂ = **8**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **19**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 75

dim S₂ = **5**; eta rank = **4**; full eta basis = **NO**; Sturm bound B = **20**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![75; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![75; 4 => 1, 14 => 1, 24 => 1, 74 => 1],
  sparse![75; 0 => 1, 4 => 1, 14 => 1, 74 => 1],
  sparse![75; 2 => 1, 4 => 1, 14 => 1, 24 => 1],
]
```

### Level 76

dim S₂ = **8**; eta rank = **5**; full eta basis = **NO**; Sturm bound B = **20**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![76; 0 => 3, 1 => -1, 18 => -1, 37 => 3],
  sparse![76; 0 => -1, 1 => 3, 18 => 3, 37 => -1],
  sparse![76; 1 => 3, 3 => -1, 37 => -1, 75 => 3],
  sparse![76; 1 => -1, 3 => 3, 37 => 3, 75 => -1],
  sparse![76; 0 => 1, 3 => 1, 18 => -3, 37 => 8, 75 => -3],
]
```

### Level 77

dim S₂ = **7**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **16**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![77; 0 => 2, 10 => 2],
  sparse![77; 6 => 2, 76 => 2],
  sparse![77; 0 => 1, 6 => 1, 10 => 1, 76 => 1],
]
```

### Level 78

dim S₂ = **11**; eta rank = **11**; full eta basis = **YES**; Sturm bound B = **28**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![78; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 12 => 3, 25 => -2, 38 => -2, 77 => 3],
  sparse![78; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 12 => -2, 25 => 3, 38 => 3, 77 => -2],
  sparse![78; 0 => 1, 1 => 1, 38 => 1, 77 => 1],
  sparse![78; 0 => 1, 5 => 1, 25 => 1, 38 => 1],
  sparse![78; 1 => 1, 2 => 1, 12 => 1, 77 => 1],
  sparse![78; 2 => 1, 5 => 1, 12 => 1, 25 => 1],
  sparse![78; 0 => -1, 1 => 1, 2 => 2, 12 => 2, 38 => -1, 77 => 1],
  sparse![78; 0 => -1, 1 => 2, 5 => 1, 12 => 2, 25 => -1, 38 => 1],
  sparse![78; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 12 => 2, 25 => -1, 38 => -1, 77 => 2],
  sparse![78; 1 => 1, 2 => -1, 5 => 2, 12 => 1, 38 => 2, 77 => -1],
  sparse![78; 0 => 1, 1 => -1, 5 => 2, 25 => 2, 38 => 1, 77 => -1],
]
```

### Level 79

dim S₂ = **6**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **13**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 80

dim S₂ = **7**; eta rank = **7**; full eta basis = **YES**; Sturm bound B = **24**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![80; 1 => 2, 9 => 2],
  sparse![80; 3 => 2, 19 => 2],
  sparse![80; 7 => 2, 39 => 2],
  sparse![80; 0 => -2, 1 => 5, 3 => -1, 4 => 2, 9 => -1, 19 => 1],
  sparse![80; 1 => -2, 3 => 5, 7 => -1, 9 => 2, 19 => -1, 39 => 1],
  sparse![80; 0 => -2, 1 => 5, 3 => -1, 4 => -2, 9 => 5, 19 => -1],
  sparse![80; 0 => -1, 1 => 1, 3 => 2, 4 => 1, 9 => 1],
]
```

### Level 81

dim S₂ = **4**; eta rank = **4**; full eta basis = **YES**; Sturm bound B = **18**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![81; 2 => 2, 8 => 2],
  sparse![81; 8 => 2, 26 => 2],
  sparse![81; 2 => -1, 8 => 6, 26 => -1],
  sparse![81; 2 => 1, 8 => 2, 26 => 1],
]
```

### Level 82

dim S₂ = **9**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **21**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 83

dim S₂ = **7**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **14**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![83; 0 => 2, 82 => 2],
]
```

### Level 84

dim S₂ = **11**; eta rank = **11**; full eta basis = **YES**; Sturm bound B = **32**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![84; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![84; 1 => 1, 3 => 1, 13 => 1, 27 => 1],
  sparse![84; 2 => 1, 5 => 1, 20 => 1, 41 => 1],
  sparse![84; 5 => 1, 11 => 1, 41 => 1, 83 => 1],
  sparse![84; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 6 => 4, 13 => -2, 20 => -1, 41 => 1],
  sparse![84; 0 => -1, 1 => 1, 2 => 4, 5 => -2, 6 => 1, 13 => -1, 20 => -2, 41 => 4],
  sparse![84; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 6 => -1, 13 => 2, 20 => 2, 41 => -1],
  sparse![84; 1 => -2, 3 => 4, 5 => 1, 11 => -1, 13 => 4, 27 => -2, 41 => -1, 83 => 1],
  sparse![84; 1 => -1, 3 => 1, 5 => 4, 11 => -2, 13 => 1, 27 => -1, 41 => -2, 83 => 4],
  sparse![84; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -2, 11 => 1, 13 => 4, 27 => -2, 41 => -1, 83 => 1],
  sparse![84; 0 => -3, 1 => 7, 2 => 2, 3 => -2, 5 => -3, 6 => 1, 11 => 1, 13 => -3, 20 => -2, 27 => 2, 41 => 7, 83 => -3],
]
```

### Level 85

dim S₂ = **7**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **18**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 86

dim S₂ = **10**; eta rank = **2**; full eta basis = **NO**; Sturm bound B = **22**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![86; 0 => 3, 1 => -1, 42 => -1, 85 => 3],
  sparse![86; 0 => -1, 1 => 3, 42 => 3, 85 => -1],
]
```

### Level 87

dim S₂ = **9**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **20**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![87; 0 => 1, 2 => 1, 28 => 1, 86 => 1],
]
```

### Level 88

dim S₂ = **9**; eta rank = **9**; full eta basis = **YES**; Sturm bound B = **24**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![88; 0 => 2, 10 => 2],
  sparse![88; 1 => 2, 21 => 2],
  sparse![88; 3 => 2, 43 => 2],
  sparse![88; 7 => 2, 87 => 2],
  sparse![88; 0 => 1, 3 => -1, 7 => 2, 10 => 1, 21 => -2, 43 => 5, 87 => -2],
  sparse![88; 1 => 1, 3 => 1, 21 => 1, 43 => 1],
  sparse![88; 0 => -2, 1 => 4, 3 => 1, 7 => -1, 10 => 2, 21 => -2, 43 => 3, 87 => -1],
  sparse![88; 0 => -2, 1 => 5, 3 => -2, 7 => 1, 10 => 2, 21 => -1, 87 => 1],
  sparse![88; 0 => -2, 1 => 5, 3 => -1, 10 => -2, 21 => 5, 43 => -1],
]
```

### Level 89

dim S₂ = **7**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **15**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 90

dim S₂ = **11**; eta rank = **11**; full eta basis = **YES**; Sturm bound B = **36**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![90; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![90; 1 => 1, 5 => 1, 9 => 1, 29 => 1],
  sparse![90; 2 => 1, 8 => 1, 14 => 1, 44 => 1],
  sparse![90; 5 => 1, 17 => 1, 29 => 1, 89 => 1],
  sparse![90; 0 => 1, 1 => 1, 14 => 1, 29 => 1],
  sparse![90; 2 => 1, 5 => 1, 44 => 1, 89 => 1],
  sparse![90; 0 => -2, 1 => 1, 2 => 7, 5 => -3, 8 => -2, 14 => 1, 17 => 1, 29 => 1],
  sparse![90; 0 => -2, 1 => 3, 2 => 2, 4 => 1, 5 => -1, 14 => 1],
  sparse![90; 0 => -1, 1 => 1, 2 => 1, 4 => 1, 5 => 1, 8 => 1, 17 => -1, 89 => 1],
  sparse![90; 0 => -1, 1 => 2, 8 => 1, 14 => 3, 29 => -1, 44 => -1, 89 => 1],
  sparse![90; 0 => -1, 1 => 2, 5 => 1, 8 => 1, 17 => -1, 29 => 1, 89 => 1],
]
```

### Level 91

dim S₂ = **7**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **18**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 92

dim S₂ = **10**; eta rank = **9**; full eta basis = **NO**; Sturm bound B = **24**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![92; 0 => 2, 22 => 2],
  sparse![92; 1 => 2, 45 => 2],
  sparse![92; 3 => 2, 91 => 2],
  sparse![92; 0 => -1, 1 => 3, 22 => -1, 45 => 3],
  sparse![92; 0 => 1, 1 => 1, 22 => 1, 45 => 1],
  sparse![92; 0 => 3, 1 => -1, 22 => 3, 45 => -1],
  sparse![92; 1 => -1, 3 => 3, 45 => -1, 91 => 3],
  sparse![92; 1 => 1, 3 => 1, 45 => 1, 91 => 1],
  sparse![92; 0 => 1, 1 => -1, 3 => 2, 22 => 1, 45 => -1, 91 => 2],
]
```

### Level 93

dim S₂ = **9**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **21**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 94

dim S₂ = **11**; eta rank = **5**; full eta basis = **NO**; Sturm bound B = **24**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![94; 0 => 2, 46 => 2],
  sparse![94; 1 => 2, 93 => 2],
  sparse![94; 0 => -1, 1 => 3, 46 => -1, 93 => 3],
  sparse![94; 0 => 1, 1 => 1, 46 => 1, 93 => 1],
  sparse![94; 0 => 3, 1 => -1, 46 => 3, 93 => -1],
]
```

### Level 95

dim S₂ = **9**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **20**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![95; 0 => 2, 94 => 2],
  sparse![95; 0 => 1, 4 => 1, 18 => 1, 94 => 1],
  sparse![95; 4 => 2, 18 => 2],
]
```

### Level 96

dim S₂ = **9**; eta rank = **9**; full eta basis = **YES**; Sturm bound B = **32**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![96; 1 => 1, 3 => 1, 5 => 1, 11 => 1],
  sparse![96; 3 => 1, 7 => 1, 11 => 1, 23 => 1],
  sparse![96; 7 => 1, 15 => 1, 23 => 1, 47 => 1],
  sparse![96; 3 => 2, 7 => 2],
  sparse![96; 11 => 2, 23 => 2],
  sparse![96; 0 => -2, 1 => 4, 2 => 2, 5 => -2, 11 => 2],
  sparse![96; 1 => -2, 3 => 4, 5 => 2, 11 => -2, 23 => 2],
  sparse![96; 1 => 1, 5 => 1, 15 => 1, 47 => 1],
  sparse![96; 0 => -2, 1 => 2, 2 => 2, 3 => 3, 7 => -1, 11 => -1, 23 => 1],
]
```

### Level 97

dim S₂ = **7**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **16**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 98

dim S₂ = **7**; eta rank = **6**; full eta basis = **NO**; Sturm bound B = **28**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![98; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![98; 6 => 1, 13 => 1, 48 => 1, 97 => 1],
  sparse![98; 0 => 2, 1 => -1, 6 => 1, 13 => 1, 48 => -1, 97 => 2],
  sparse![98; 0 => 1, 6 => 1, 13 => 1, 97 => 1],
  sparse![98; 1 => 1, 6 => 1, 13 => 1, 48 => 1],
  sparse![98; 0 => -1, 1 => 2, 6 => 1, 13 => 1, 48 => 2, 97 => -1],
]
```

### Level 99

dim S₂ = **9**; eta rank = **6**; full eta basis = **NO**; Sturm bound B = **24**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![99; 0 => 2, 10 => 2],
  sparse![99; 2 => 2, 32 => 2],
  sparse![99; 8 => 2, 98 => 2],
  sparse![99; 0 => 1, 2 => 1, 10 => 1, 32 => 1],
  sparse![99; 2 => 1, 8 => 1, 32 => 1, 98 => 1],
  sparse![99; 0 => 1, 8 => 1, 10 => 1, 98 => 1],
]
```

### Level 100

dim S₂ = **7**; eta rank = **7**; full eta basis = **YES**; Sturm bound B = **30**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![100; 1 => 2, 9 => 2],
  sparse![100; 9 => 2, 49 => 2],
  sparse![100; 1 => 1, 9 => 2, 49 => 1],
  sparse![100; 0 => -1, 1 => 2, 3 => -1, 4 => 2, 19 => 2, 24 => -1, 49 => 2, 99 => -1],
  sparse![100; 0 => -1, 1 => 2, 9 => 2, 24 => 1],
  sparse![100; 0 => -1, 1 => 3, 3 => -1, 9 => 2, 24 => 1, 49 => -1, 99 => 1],
  sparse![100; 1 => -1, 3 => 1, 9 => 6, 19 => -2, 49 => -1, 99 => 1],
]
```

### Level 101

dim S₂ = **8**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **17**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 102

dim S₂ = **15**; eta rank = **13**; full eta basis = **NO**; Sturm bound B = **36**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![102; 0 => 1, 2 => 1, 16 => 1, 50 => 1],
  sparse![102; 1 => 1, 5 => 1, 33 => 1, 101 => 1],
  sparse![102; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 16 => 1, 101 => 1],
  sparse![102; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 33 => 1, 50 => 1],
  sparse![102; 1 => 2, 2 => 1, 5 => -1, 16 => -1, 33 => 1, 50 => 2],
  sparse![102; 0 => 2, 2 => -1, 5 => 1, 16 => 1, 33 => -1, 101 => 2],
  sparse![102; 0 => 1, 1 => -1, 5 => 2, 16 => 2, 50 => -1, 101 => 1],
  sparse![102; 0 => -1, 1 => 1, 2 => 2, 33 => 2, 50 => 1, 101 => -1],
  sparse![102; 0 => -1, 1 => 3, 2 => 1, 5 => -1, 16 => 1, 33 => -1, 50 => -1, 101 => 3],
  sparse![102; 0 => 3, 1 => -1, 2 => -1, 5 => 1, 16 => -1, 33 => 1, 50 => 3, 101 => -1],
  sparse![102; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 16 => 3, 33 => -1, 50 => -1, 101 => 1],
  sparse![102; 1 => 1, 2 => 1, 16 => 3, 33 => -2, 50 => -2, 101 => 3],
  sparse![102; 0 => 1, 1 => -1, 2 => -1, 5 => 3, 16 => -1, 33 => 3, 50 => 1, 101 => -1],
]
```

### Level 103

dim S₂ = **8**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **17**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 104

dim S₂ = **11**; eta rank = **11**; full eta basis = **YES**; Sturm bound B = **28**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![104; 0 => 1, 3 => 2, 7 => -1, 12 => -1, 25 => 2, 103 => 1],
  sparse![104; 0 => -1, 1 => 1, 3 => 3, 7 => -1, 12 => 1, 25 => 1, 51 => -1, 103 => 1],
  sparse![104; 0 => -1, 1 => 2, 7 => 1, 12 => 1, 51 => 2, 103 => -1],
  sparse![104; 0 => -1, 1 => 2, 3 => 2, 7 => -1, 12 => 1, 103 => 1],
  sparse![104; 0 => -1, 1 => 3, 3 => -1, 7 => 1, 12 => 1, 25 => -1, 51 => 3, 103 => -1],
  sparse![104; 0 => -1, 1 => 3, 3 => 1, 7 => -1, 12 => 1, 25 => -1, 51 => 1, 103 => 1],
  sparse![104; 0 => -1, 1 => 4, 3 => -2, 7 => 1, 12 => 1, 25 => -2, 51 => 4, 103 => -1],
  sparse![104; 0 => 1, 1 => -2, 3 => 4, 7 => -1, 12 => -1, 25 => 4, 51 => -2, 103 => 1],
  sparse![104; 0 => 1, 1 => -1, 3 => 1, 7 => 1, 12 => -1, 25 => 3, 51 => 1, 103 => -1],
  sparse![104; 0 => 1, 1 => -1, 3 => 3, 7 => -1, 12 => -1, 25 => 3, 51 => -1, 103 => 1],
  sparse![104; 0 => 1, 7 => 1, 12 => -1, 25 => 2, 51 => 2, 103 => -1],
]
```

### Level 105

dim S₂ = **13**; eta rank = **11**; full eta basis = **NO**; Sturm bound B = **32**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![105; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![105; 6 => 1, 20 => 1, 34 => 1, 104 => 1],
  sparse![105; 0 => 2, 34 => 2],
  sparse![105; 0 => 1, 4 => 1, 6 => 1, 34 => 1],
  sparse![105; 4 => 2, 6 => 2],
  sparse![105; 2 => 2, 104 => 2],
  sparse![105; 2 => 1, 14 => 1, 20 => 1, 104 => 1],
  sparse![105; 14 => 2, 20 => 2],
  sparse![105; 0 => 1, 14 => 1, 20 => 1, 34 => 1],
  sparse![105; 2 => 1, 4 => 1, 6 => 1, 104 => 1],
  sparse![105; 0 => 1, 2 => 1, 34 => 1, 104 => 1],
]
```

### Level 106

dim S₂ = **12**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **27**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 107

dim S₂ = **9**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **18**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![107; 0 => 2, 106 => 2],
]
```

### Level 108

dim S₂ = **10**; eta rank = **10**; full eta basis = **YES**; Sturm bound B = **36**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![108; 2 => 2, 8 => 2],
  sparse![108; 5 => 2, 17 => 2],
  sparse![108; 11 => 2, 35 => 2],
  sparse![108; 5 => 4],
  sparse![108; 17 => 4],
  sparse![108; 0 => -1, 1 => 2, 5 => 2, 8 => 1],
  sparse![108; 0 => -1, 1 => 2, 2 => 1, 17 => 1, 26 => 2, 53 => -1],
  sparse![108; 1 => -1, 3 => 2, 11 => 2, 17 => 1],
  sparse![108; 1 => -1, 3 => 2, 5 => 1, 35 => 1, 53 => 2, 107 => -1],
  sparse![108; 1 => 3, 17 => 1],
]
```

### Level 109

dim S₂ = **8**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **18**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 110

dim S₂ = **15**; eta rank = **15**; full eta basis = **YES**; Sturm bound B = **36**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![110; 0 => 2, 10 => 2],
  sparse![110; 1 => 2, 21 => 2],
  sparse![110; 4 => 2, 54 => 2],
  sparse![110; 9 => 2, 109 => 2],
  sparse![110; 0 => 1, 4 => 1, 10 => 1, 54 => 1],
  sparse![110; 1 => 1, 9 => 1, 21 => 1, 109 => 1],
  sparse![110; 0 => 2, 1 => -1, 4 => -1, 9 => 2, 10 => -1, 21 => 2, 54 => 2, 109 => -1],
  sparse![110; 0 => -1, 1 => 2, 9 => 1, 10 => 1, 54 => 2, 109 => -1],
  sparse![110; 1 => 1, 4 => -1, 9 => 2, 10 => 2, 21 => -1, 54 => 1],
  sparse![110; 0 => -1, 1 => 2, 4 => 1, 10 => -1, 21 => 2, 54 => 1],
  sparse![110; 0 => 1, 4 => -1, 9 => 2, 10 => 1, 54 => -1, 109 => 2],
  sparse![110; 0 => 1, 1 => 1, 54 => 1, 109 => 1],
  sparse![110; 4 => 1, 9 => 1, 10 => 1, 21 => 1],
  sparse![110; 0 => 1, 1 => -1, 4 => -1, 9 => 3, 10 => -1, 21 => 3, 54 => 1, 109 => -1],
  sparse![110; 0 => 3, 1 => -1, 4 => -1, 9 => 1, 10 => -1, 21 => 1, 54 => 3, 109 => -1],
]
```

### Level 111

dim S₂ = **11**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **25**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 112

dim S₂ = **11**; eta rank = **11**; full eta basis = **YES**; Sturm bound B = **32**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![112; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![112; 1 => 1, 3 => 1, 13 => 1, 27 => 1],
  sparse![112; 3 => 1, 7 => 1, 27 => 1, 55 => 1],
  sparse![112; 7 => 1, 15 => 1, 55 => 1, 111 => 1],
  sparse![112; 0 => 1, 6 => 1, 7 => 1, 55 => 1],
  sparse![112; 1 => -1, 3 => 3, 13 => 3, 27 => -1],
  sparse![112; 1 => 1, 13 => 1, 15 => 1, 111 => 1],
  sparse![112; 3 => -1, 7 => 3, 27 => 3, 55 => -1],
  sparse![112; 0 => -3, 1 => 7, 3 => -2, 6 => 1, 13 => 1],
  sparse![112; 0 => -2, 1 => 4, 6 => 2, 13 => -2, 27 => 2],
  sparse![112; 0 => -2, 1 => 5, 3 => -2, 7 => 2, 15 => -1, 55 => 1, 111 => 1],
]
```

### Level 113

dim S₂ = **9**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **19**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 114

dim S₂ = **17**; eta rank = **13**; full eta basis = **NO**; Sturm bound B = **40**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![114; 0 => 3, 1 => -1, 18 => -1, 37 => 3],
  sparse![114; 0 => -1, 1 => 3, 18 => 3, 37 => -1],
  sparse![114; 2 => 3, 5 => -1, 56 => -1, 113 => 3],
  sparse![114; 2 => -1, 5 => 3, 56 => 3, 113 => -1],
  sparse![114; 1 => 1, 2 => 2, 5 => -1, 18 => 1, 56 => -1, 113 => 2],
  sparse![114; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 18 => 1, 113 => 1],
  sparse![114; 0 => 2, 1 => -1, 5 => 1, 18 => -1, 37 => 2, 56 => 1],
  sparse![114; 0 => -1, 1 => 2, 2 => 1, 18 => 2, 37 => -1, 113 => 1],
  sparse![114; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 37 => 1, 56 => 1],
  sparse![114; 0 => -1, 1 => 1, 2 => 2, 18 => 1, 37 => -1, 113 => 2],
  sparse![114; 1 => 1, 2 => 1, 18 => -2, 37 => 3, 56 => 3, 113 => -2],
  sparse![114; 1 => 2, 2 => 1, 5 => -1, 18 => 2, 56 => -1, 113 => 1],
  sparse![114; 0 => 1, 2 => -1, 5 => 2, 37 => 1, 56 => 2, 113 => -1],
]
```

### Level 115

dim S₂ = **11**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **24**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![115; 0 => 2, 22 => 2],
  sparse![115; 4 => 2, 114 => 2],
  sparse![115; 0 => 1, 4 => 1, 22 => 1, 114 => 1],
]
```

### Level 116

dim S₂ = **13**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **30**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![116; 1 => 2, 57 => 2],
]
```

### Level 117

dim S₂ = **11**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **28**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 118

dim S₂ = **14**; eta rank = **2**; full eta basis = **NO**; Sturm bound B = **30**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![118; 0 => 2, 58 => 2],
  sparse![118; 1 => 2, 117 => 2],
]
```

### Level 119

dim S₂ = **11**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **24**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![119; 0 => 2, 118 => 2],
  sparse![119; 0 => 1, 6 => 1, 16 => 1, 118 => 1],
  sparse![119; 6 => 2, 16 => 2],
]
```

### Level 120

dim S₂ = **17**; eta rank = **17**; full eta basis = **YES**; Sturm bound B = **48**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![120; 0 => -5, 1 => 11, 2 => 1, 3 => -4, 4 => 5, 5 => -2, 9 => -4, 11 => 1, 14 => -1, 19 => 1, 29 => 1],
  sparse![120; 0 => -5, 1 => 11, 2 => 5, 3 => -4, 4 => 1, 5 => -4, 9 => -2, 11 => 1, 14 => -1, 19 => 1, 29 => 1],
  sparse![120; 0 => -4, 1 => 8, 2 => 1, 3 => -1, 4 => 4, 5 => -2, 7 => -1, 9 => -3, 11 => 1, 14 => -1, 29 => 1, 39 => 1],
  sparse![120; 0 => -4, 1 => 8, 2 => 2, 3 => -2, 4 => 4, 5 => -3, 9 => -4, 11 => 1, 14 => -2, 19 => 2, 29 => 3, 59 => -1],
  sparse![120; 0 => -4, 1 => 10, 2 => 2, 3 => -4, 4 => 1, 5 => -4, 9 => -3, 11 => 2, 14 => -1, 19 => 2, 29 => 3],
  sparse![120; 0 => -3, 1 => 5, 2 => 1, 3 => 2, 4 => 3, 5 => -2, 7 => -2, 9 => -2, 11 => 1, 14 => -1, 19 => -1, 29 => 1, 39 => 2],
  sparse![120; 0 => -3, 1 => 5, 2 => 3, 4 => 3, 5 => -3, 7 => -1, 9 => -3, 14 => -3, 23 => 1, 29 => 5, 39 => 1, 119 => -1],
  sparse![120; 0 => -3, 1 => 6, 2 => 2, 3 => -2, 4 => 1, 5 => -1, 29 => -1, 59 => 2],
  sparse![120; 0 => -3, 1 => 6, 2 => 2, 3 => -2, 4 => 3, 5 => -3, 9 => -3, 11 => 3, 14 => -2, 19 => 1, 23 => -1, 29 => 4, 59 => -2, 119 => 1],
  sparse![120; 0 => -3, 1 => 6, 2 => 2, 4 => 2, 5 => -3, 7 => -1, 9 => -3, 14 => -3, 23 => 1, 29 => 6, 39 => 1, 119 => -1],
  sparse![120; 0 => -3, 1 => 7, 2 => 1, 3 => -1, 4 => -3, 5 => -2, 7 => -1, 9 => 8, 14 => 1, 19 => -4, 23 => 1, 29 => -3, 39 => 1, 59 => 3, 119 => -1],
  sparse![120; 0 => -2, 1 => 2, 2 => 3, 3 => 1, 4 => 3, 5 => -2, 7 => -1, 9 => -2, 14 => -2, 23 => 1, 29 => 2, 39 => 1, 59 => 1, 119 => -1],
  sparse![120; 0 => -2, 1 => 2, 2 => 4, 4 => 1, 5 => -2, 14 => -1, 19 => 1, 59 => 1],
  sparse![120; 0 => -2, 1 => 3, 2 => 1, 3 => -1, 4 => 3, 5 => 1, 9 => -2, 19 => 1],
  sparse![120; 0 => -2, 1 => 3, 2 => 1, 3 => 1, 4 => 2, 7 => -1, 9 => -2, 14 => -1, 29 => 3, 39 => 1, 59 => -1],
  sparse![120; 0 => -1, 1 => -2, 2 => 2, 3 => 6, 4 => 2, 5 => 1, 7 => -2, 9 => 1, 11 => -3, 14 => -1, 19 => -3, 23 => 1, 29 => -2, 39 => 1, 59 => 6, 119 => -2],
  sparse![120; 0 => -1, 1 => -1, 2 => 2, 3 => 3, 4 => 2, 5 => 1, 7 => -1, 9 => 1, 11 => -2, 14 => -1, 19 => -2, 23 => 1, 29 => -1, 39 => 1, 59 => 3, 119 => -1],
]
```

### Level 121

dim S₂ = **6**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **22**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![121; 0 => 2, 10 => 2],
  sparse![121; 10 => 2, 120 => 2],
  sparse![121; 0 => 1, 10 => 2, 120 => 1],
]
```

### Level 122

dim S₂ = **14**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **31**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 123

dim S₂ = **13**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **28**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![123; 0 => 1, 2 => 1, 40 => 1, 122 => 1],
]
```

### Level 124

dim S₂ = **14**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **32**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![124; 0 => 1, 1 => 1, 30 => 1, 61 => 1],
  sparse![124; 1 => 1, 3 => 1, 61 => 1, 123 => 1],
  sparse![124; 0 => -1, 1 => 4, 3 => -1, 30 => -1, 61 => 4, 123 => -1],
]
```

### Level 125

dim S₂ = **8**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **25**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 126

dim S₂ = **17**; eta rank = **17**; full eta basis = **YES**; Sturm bound B = **48**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![126; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![126; 2 => 1, 5 => 1, 20 => 1, 41 => 1],
  sparse![126; 8 => 1, 17 => 1, 62 => 1, 125 => 1],
  sparse![126; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 6 => 4, 13 => -2, 20 => -1, 41 => 1],
  sparse![126; 0 => -1, 1 => 1, 2 => 4, 5 => -2, 6 => 1, 13 => -1, 20 => -2, 41 => 4],
  sparse![126; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 6 => -1, 13 => 2, 20 => 2, 41 => -1],
  sparse![126; 2 => -2, 5 => 4, 8 => 1, 17 => -1, 20 => 4, 41 => -2, 62 => -1, 125 => 1],
  sparse![126; 2 => -1, 5 => 1, 8 => 4, 17 => -2, 20 => 1, 41 => -1, 62 => -2, 125 => 4],
  sparse![126; 2 => -1, 5 => 2, 8 => 2, 17 => -1, 20 => -1, 41 => 2, 62 => 2, 125 => -1],
  sparse![126; 2 => 2, 20 => 2],
  sparse![126; 0 => -1, 2 => 4, 6 => 1, 8 => -1, 62 => 1],
  sparse![126; 5 => 2, 41 => 2],
  sparse![126; 1 => -1, 5 => 4, 13 => 1, 17 => -1, 125 => 1],
  sparse![126; 2 => -1, 5 => 1, 8 => 4, 17 => -2, 20 => -1, 41 => 1, 62 => 4, 125 => -2],
  sparse![126; 0 => 1, 1 => 1, 62 => 1, 125 => 1],
  sparse![126; 0 => 1, 13 => 1, 17 => 1, 62 => 1],
  sparse![126; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 8 => -1, 13 => 1, 17 => 1, 20 => -1, 41 => 2, 62 => 1, 125 => -1],
]
```

### Level 127

dim S₂ = **10**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **21**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 128

dim S₂ = **9**; eta rank = **9**; full eta basis = **YES**; Sturm bound B = **32**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![128; 3 => 2, 7 => 2],
  sparse![128; 7 => 2, 15 => 2],
  sparse![128; 15 => 2, 31 => 2],
  sparse![128; 0 => -2, 1 => 5, 3 => -2, 7 => 3],
  sparse![128; 1 => -2, 3 => 5, 7 => -2, 15 => 3],
  sparse![128; 1 => -2, 3 => 5, 7 => -1, 15 => 1, 31 => -1, 63 => 2],
  sparse![128; 1 => 2, 3 => 1, 15 => 1],
  sparse![128; 3 => 2, 31 => 2],
  sparse![128; 7 => 1, 31 => 1, 63 => 2],
]
```

### Level 129

dim S₂ = **13**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **29**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 130

dim S₂ = **17**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **42**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 131

dim S₂ = **11**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **22**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![131; 0 => 2, 130 => 2],
]
```

### Level 132

dim S₂ = **19**; eta rank = **19**; full eta basis = **YES**; Sturm bound B = **48**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![132; 0 => 2, 10 => 2],
  sparse![132; 1 => 2, 21 => 2],
  sparse![132; 2 => 2, 32 => 2],
  sparse![132; 3 => 2, 43 => 2],
  sparse![132; 5 => 2, 65 => 2],
  sparse![132; 11 => 2, 131 => 2],
  sparse![132; 0 => 1, 2 => 1, 10 => 1, 32 => 1],
  sparse![132; 1 => 1, 5 => 1, 21 => 1, 65 => 1],
  sparse![132; 3 => 1, 11 => 1, 43 => 1, 131 => 1],
  sparse![132; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 10 => -1, 21 => 1, 32 => 3, 65 => -1],
  sparse![132; 1 => -1, 3 => 1, 5 => 3, 11 => -1, 21 => -1, 43 => 1, 65 => 3, 131 => -1],
  sparse![132; 0 => -4, 1 => 9, 2 => 2, 3 => -3, 5 => -3, 10 => 2, 11 => 1],
  sparse![132; 0 => -4, 1 => 10, 2 => 2, 3 => -4, 5 => -4, 11 => 2, 32 => -2, 65 => 6, 131 => -2],
  sparse![132; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 5 => -3, 10 => 1, 11 => 1, 32 => -1, 65 => 3, 131 => -1],
  sparse![132; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -1, 131 => 2],
  sparse![132; 0 => -3, 1 => 8, 2 => 1, 3 => -3, 5 => -2, 10 => -1, 11 => 1, 21 => 1, 32 => 3, 65 => -1],
  sparse![132; 0 => -3, 1 => 9, 2 => 1, 3 => -4, 5 => -3, 11 => 2, 43 => 2],
  sparse![132; 0 => -2, 1 => 6, 3 => -2, 21 => -1, 32 => 2, 43 => 1, 65 => 1, 131 => -1],
  sparse![132; 0 => -2, 1 => 7, 3 => -3, 5 => -1, 11 => 1, 32 => 2],
]
```

### Level 133

dim S₂ = **11**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **26**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 134

dim S₂ = **16**; eta rank = **2**; full eta basis = **NO**; Sturm bound B = **34**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![134; 0 => 3, 1 => -1, 66 => -1, 133 => 3],
  sparse![134; 0 => -1, 1 => 3, 66 => 3, 133 => -1],
]
```

### Level 135

dim S₂ = **13**; eta rank = **13**; full eta basis = **YES**; Sturm bound B = **36**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![135; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![135; 2 => 1, 8 => 1, 14 => 1, 44 => 1],
  sparse![135; 8 => 1, 26 => 1, 44 => 1, 134 => 1],
  sparse![135; 2 => 2, 8 => 2],
  sparse![135; 14 => 2, 44 => 2],
  sparse![135; 0 => 1, 4 => 1, 26 => 1, 134 => 1],
  sparse![135; 2 => 2, 44 => 2],
  sparse![135; 8 => 2, 14 => 2],
  sparse![135; 0 => -1, 2 => 2, 4 => 2, 8 => 1],
  sparse![135; 0 => -1, 2 => 3, 4 => 2, 14 => -1, 44 => 1],
  sparse![135; 2 => -1, 8 => 3, 14 => 3, 44 => -1],
  sparse![135; 14 => 1, 26 => 2, 44 => 2, 134 => -1],
  sparse![135; 8 => 3, 14 => 1, 26 => -1, 44 => -1, 134 => 2],
]
```

### Level 136

dim S₂ = **15**; eta rank = **13**; full eta basis = **NO**; Sturm bound B = **36**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![136; 0 => 2, 1 => -1, 3 => 1, 16 => -2, 33 => 5, 67 => -1],
  sparse![136; 0 => 1, 1 => -1, 3 => 2, 16 => -1, 33 => 5, 67 => -2],
  sparse![136; 0 => 1, 1 => 2, 3 => -1, 16 => -1, 33 => 2, 67 => 1],
  sparse![136; 1 => 2, 33 => 2],
  sparse![136; 0 => -1, 1 => 2, 3 => 1, 16 => 1, 33 => 2, 67 => -1],
  sparse![136; 0 => -1, 1 => 5, 3 => -2, 16 => 1, 33 => -1, 67 => 2],
  sparse![136; 0 => -2, 1 => 5, 3 => -1, 16 => 2, 33 => -1, 67 => 1],
  sparse![136; 1 => 2, 3 => -1, 7 => 1, 33 => -2, 67 => 5, 135 => -1],
  sparse![136; 1 => 1, 3 => -1, 7 => 2, 33 => -1, 67 => 5, 135 => -2],
  sparse![136; 3 => 2, 67 => 2],
  sparse![136; 1 => -1, 3 => 2, 7 => 1, 33 => 1, 67 => 2, 135 => -1],
  sparse![136; 0 => -1, 1 => 1, 3 => 3, 7 => -1, 16 => 1, 33 => -1, 67 => 1, 135 => 1],
  sparse![136; 0 => -1, 1 => 3, 3 => 1, 7 => -1, 16 => 1, 33 => 1, 67 => -1, 135 => 1],
]
```

### Level 137

dim S₂ = **11**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **23**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 138

dim S₂ = **21**; eta rank = **16**; full eta basis = **NO**; Sturm bound B = **48**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![138; 0 => 2, 22 => 2],
  sparse![138; 1 => 2, 45 => 2],
  sparse![138; 2 => 2, 68 => 2],
  sparse![138; 5 => 2, 137 => 2],
  sparse![138; 0 => -1, 1 => 3, 22 => -1, 45 => 3],
  sparse![138; 0 => 1, 1 => 1, 22 => 1, 45 => 1],
  sparse![138; 0 => 3, 1 => -1, 22 => 3, 45 => -1],
  sparse![138; 2 => -1, 5 => 3, 68 => -1, 137 => 3],
  sparse![138; 2 => 1, 5 => 1, 68 => 1, 137 => 1],
  sparse![138; 2 => 3, 5 => -1, 68 => 3, 137 => -1],
  sparse![138; 0 => 1, 2 => 1, 22 => 1, 68 => 1],
  sparse![138; 1 => 1, 5 => 1, 45 => 1, 137 => 1],
  sparse![138; 0 => 1, 1 => -1, 2 => -2, 5 => 4, 22 => 1, 45 => -1, 68 => -2, 137 => 4],
  sparse![138; 0 => 1, 1 => -1, 2 => -1, 5 => 3, 22 => 1, 45 => -1, 68 => -1, 137 => 3],
  sparse![138; 0 => -1, 1 => 1, 2 => 2, 22 => -1, 45 => 1, 68 => 2],
  sparse![138; 0 => 1, 1 => -1, 5 => 2, 22 => 1, 45 => -1, 137 => 2],
]
```

### Level 139

dim S₂ = **11**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **23**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 140

dim S₂ = **19**; eta rank = **19**; full eta basis = **YES**; Sturm bound B = **48**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![140; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![140; 1 => 1, 3 => 1, 13 => 1, 27 => 1],
  sparse![140; 4 => 1, 9 => 1, 34 => 1, 69 => 1],
  sparse![140; 9 => 1, 19 => 1, 69 => 1, 139 => 1],
  sparse![140; 1 => 2, 9 => 2],
  sparse![140; 13 => 2, 69 => 2],
  sparse![140; 0 => 2, 34 => 2],
  sparse![140; 0 => 1, 4 => 1, 6 => 1, 34 => 1],
  sparse![140; 4 => 2, 6 => 2],
  sparse![140; 1 => 2, 69 => 2],
  sparse![140; 1 => 1, 9 => 1, 13 => 1, 69 => 1],
  sparse![140; 9 => 2, 13 => 2],
  sparse![140; 3 => 2, 139 => 2],
  sparse![140; 3 => 1, 19 => 1, 27 => 1, 139 => 1],
  sparse![140; 19 => 2, 27 => 2],
  sparse![140; 0 => 1, 4 => 2, 9 => -1, 13 => 1, 34 => -1, 69 => 2],
  sparse![140; 1 => 1, 9 => 2, 19 => -1, 27 => 1, 69 => -1, 139 => 2],
  sparse![140; 0 => 1, 6 => 1, 19 => 1, 139 => 1],
  sparse![140; 0 => -2, 1 => 4, 3 => -1, 4 => 2, 9 => -1, 13 => 2, 27 => -1, 69 => 1],
]
```

### Level 141

dim S₂ = **15**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **32**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![141; 0 => 2, 46 => 2],
  sparse![141; 2 => 2, 140 => 2],
  sparse![141; 0 => 1, 2 => 1, 46 => 1, 140 => 1],
]
```

### Level 142

dim S₂ = **17**; eta rank = **5**; full eta basis = **NO**; Sturm bound B = **36**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![142; 0 => 2, 70 => 2],
  sparse![142; 1 => 2, 141 => 2],
  sparse![142; 0 => -1, 1 => 3, 70 => -1, 141 => 3],
  sparse![142; 0 => 1, 1 => 1, 70 => 1, 141 => 1],
  sparse![142; 0 => 3, 1 => -1, 70 => 3, 141 => -1],
]
```

### Level 143

dim S₂ = **13**; eta rank = **5**; full eta basis = **NO**; Sturm bound B = **28**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![143; 0 => 2, 10 => 2],
  sparse![143; 12 => 2, 142 => 2],
  sparse![143; 0 => 2, 142 => 2],
  sparse![143; 0 => 1, 10 => 1, 12 => 1, 142 => 1],
  sparse![143; 10 => 2, 12 => 2],
]
```

### Level 144

dim S₂ = **13**; eta rank = **13**; full eta basis = **YES**; Sturm bound B = **48**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![144; 0 => -4, 1 => 10, 3 => -4, 11 => 2],
  sparse![144; 0 => -3, 1 => 6, 2 => 1, 3 => 1, 5 => -2, 7 => -2, 11 => 1, 23 => 2],
  sparse![144; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -1, 11 => 2],
  sparse![144; 0 => -2, 1 => 1, 2 => 2, 3 => 6, 5 => -1, 7 => -3, 23 => 1],
  sparse![144; 0 => -2, 1 => 1, 2 => 8, 5 => -4, 8 => -2, 11 => 2, 17 => 1],
  sparse![144; 0 => -2, 1 => 3, 2 => 2, 3 => 1, 5 => -2, 7 => -1, 11 => 2, 17 => 1, 35 => -1, 71 => 1],
  sparse![144; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -1, 8 => -1, 11 => 1, 17 => 1, 23 => 2, 47 => -1, 71 => -1, 143 => 1],
  sparse![144; 0 => -2, 1 => 3, 2 => 5, 3 => -1, 5 => -3, 8 => -1, 11 => 2, 35 => 1],
  sparse![144; 0 => -2, 1 => 5, 2 => -1, 3 => -2, 5 => 2, 8 => 1, 11 => 1, 17 => -1, 35 => 1],
  sparse![144; 0 => -2, 1 => 5, 3 => -4, 7 => 5, 11 => 2, 15 => -2],
  sparse![144; 0 => -1, 1 => -1, 2 => 1, 3 => 6, 7 => -1, 15 => -1, 47 => 1],
  sparse![144; 0 => -1, 2 => 2, 3 => 1, 5 => 2, 8 => -1, 35 => 1],
  sparse![144; 0 => -1, 2 => 3, 3 => 1, 11 => 1],
]
```

### Level 145

dim S₂ = **13**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **30**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 146

dim S₂ = **17**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **37**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 147

dim S₂ = **11**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **37**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 148

dim S₂ = **17**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **38**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 149

dim S₂ = **12**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **25**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 150

dim S₂ = **19**; eta rank = **19**; full eta basis = **YES**; Sturm bound B = **60**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![150; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![150; 1 => 1, 5 => 1, 9 => 1, 29 => 1],
  sparse![150; 4 => 1, 14 => 1, 24 => 1, 74 => 1],
  sparse![150; 9 => 1, 29 => 1, 49 => 1, 149 => 1],
  sparse![150; 0 => 1, 1 => 1, 14 => 1, 29 => 1],
  sparse![150; 4 => 1, 9 => 1, 74 => 1, 149 => 1],
  sparse![150; 0 => 1, 4 => 1, 14 => 1, 74 => 1],
  sparse![150; 2 => 1, 4 => 1, 14 => 1, 24 => 1],
  sparse![150; 1 => 1, 9 => 1, 29 => 1, 149 => 1],
  sparse![150; 5 => 1, 9 => 1, 29 => 1, 49 => 1],
  sparse![150; 0 => 1, 14 => 1, 29 => 1, 49 => 1],
  sparse![150; 1 => 1, 14 => 1, 24 => 1, 29 => 1],
  sparse![150; 2 => 1, 4 => 1, 9 => 1, 149 => 1],
  sparse![150; 4 => 1, 5 => 1, 9 => 1, 74 => 1],
  sparse![150; 0 => -1, 1 => 1, 4 => 3, 9 => -1, 14 => 3, 29 => -1, 74 => -1, 149 => 1],
  sparse![150; 0 => -1, 1 => 1, 2 => 1, 4 => 1, 14 => 1, 24 => 2, 49 => -1],
  sparse![150; 0 => -1, 1 => 1, 2 => 1, 4 => 1, 9 => 1, 24 => 1, 49 => -1, 149 => 1],
  sparse![150; 0 => -1, 1 => 2, 14 => 1, 24 => 2, 29 => 1, 49 => -1],
  sparse![150; 0 => -1, 1 => 2, 9 => 1, 24 => 1, 29 => 1, 49 => -1, 149 => 1],
]
```

### Level 151

dim S₂ = **12**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **25**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 152

dim S₂ = **17**; eta rank = **15**; full eta basis = **NO**; Sturm bound B = **40**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![152; 0 => 3, 1 => -1, 18 => -1, 37 => 3],
  sparse![152; 0 => -1, 1 => 3, 18 => 3, 37 => -1],
  sparse![152; 1 => 3, 3 => -1, 37 => -1, 75 => 3],
  sparse![152; 1 => -1, 3 => 3, 37 => 3, 75 => -1],
  sparse![152; 3 => 3, 7 => -1, 75 => -1, 151 => 3],
  sparse![152; 3 => -1, 7 => 3, 75 => 3, 151 => -1],
  sparse![152; 0 => 1, 3 => 1, 18 => -3, 37 => 8, 75 => -3],
  sparse![152; 1 => 1, 7 => 1, 37 => -3, 75 => 8, 151 => -3],
  sparse![152; 0 => -1, 1 => 1, 3 => 3, 7 => -1, 18 => -1, 37 => 3, 75 => 1, 151 => -1],
  sparse![152; 0 => -1, 1 => 3, 3 => 1, 7 => -1, 18 => -1, 37 => 1, 75 => 3, 151 => -1],
  sparse![152; 1 => 1, 3 => 1, 37 => 1, 75 => 1],
  sparse![152; 0 => -1, 1 => 2, 7 => 1, 18 => -1, 37 => 4, 75 => -2, 151 => 1],
  sparse![152; 0 => -1, 1 => 4, 3 => -2, 7 => 1, 18 => -1, 37 => 2, 151 => 1],
  sparse![152; 0 => 1, 1 => -2, 3 => 4, 7 => -1, 18 => 1, 75 => 2, 151 => -1],
  sparse![152; 0 => 1, 3 => 2, 7 => -1, 18 => 1, 37 => -2, 75 => 4, 151 => -1],
]
```

### Level 153

dim S₂ = **15**; eta rank = **2**; full eta basis = **NO**; Sturm bound B = **36**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![153; 0 => 1, 2 => 1, 16 => 1, 50 => 1],
  sparse![153; 2 => 1, 8 => 1, 50 => 1, 152 => 1],
]
```

### Level 154

dim S₂ = **21**; eta rank = **17**; full eta basis = **NO**; Sturm bound B = **48**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![154; 0 => 2, 10 => 2],
  sparse![154; 1 => 2, 21 => 2],
  sparse![154; 6 => 2, 76 => 2],
  sparse![154; 13 => 2, 153 => 2],
  sparse![154; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![154; 10 => 1, 21 => 1, 76 => 1, 153 => 1],
  sparse![154; 0 => 1, 6 => 1, 10 => 1, 76 => 1],
  sparse![154; 1 => 1, 13 => 1, 21 => 1, 153 => 1],
  sparse![154; 0 => -1, 1 => 2, 6 => -1, 10 => 2, 13 => 2, 21 => -1, 76 => 2, 153 => -1],
  sparse![154; 0 => -1, 1 => 2, 6 => 2, 10 => 1, 13 => -1, 153 => 1],
  sparse![154; 1 => 1, 6 => 1, 10 => 2, 21 => -1, 76 => -1, 153 => 2],
  sparse![154; 0 => -1, 1 => 2, 6 => 1, 10 => -1, 21 => 2, 76 => 1],
  sparse![154; 0 => 1, 6 => -1, 10 => 1, 13 => 2, 76 => -1, 153 => 2],
  sparse![154; 1 => 1, 6 => 2, 13 => -1, 21 => 1, 76 => 2, 153 => -1],
  sparse![154; 0 => 2, 1 => -1, 10 => 2, 13 => 1, 21 => -1, 153 => 1],
  sparse![154; 0 => 1, 10 => -1, 13 => 1, 21 => 2, 76 => 2, 153 => -1],
  sparse![154; 0 => 2, 1 => -1, 6 => -1, 13 => 2, 21 => 1, 76 => 1],
]
```

### Level 155

dim S₂ = **15**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **32**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![155; 0 => 2, 154 => 2],
  sparse![155; 0 => 1, 4 => 1, 30 => 1, 154 => 1],
  sparse![155; 4 => 2, 30 => 2],
]
```

### Level 156

dim S₂ = **23**; eta rank = **21**; full eta basis = **NO**; Sturm bound B = **56**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![156; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 12 => 3, 25 => -2, 38 => -2, 77 => 3],
  sparse![156; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 12 => -2, 25 => 3, 38 => 3, 77 => -2],
  sparse![156; 0 => 1, 1 => 1, 38 => 1, 77 => 1],
  sparse![156; 0 => 1, 5 => 1, 25 => 1, 38 => 1],
  sparse![156; 1 => 1, 2 => 1, 12 => 1, 77 => 1],
  sparse![156; 2 => 1, 5 => 1, 12 => 1, 25 => 1],
  sparse![156; 0 => -1, 1 => 1, 2 => 2, 12 => 2, 38 => -1, 77 => 1],
  sparse![156; 0 => -1, 1 => 2, 5 => 1, 12 => 2, 25 => -1, 38 => 1],
  sparse![156; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 12 => 2, 25 => -1, 38 => -1, 77 => 2],
  sparse![156; 1 => 1, 2 => -1, 5 => 2, 12 => 1, 38 => 2, 77 => -1],
  sparse![156; 0 => 1, 1 => -1, 5 => 2, 25 => 2, 38 => 1, 77 => -1],
  sparse![156; 1 => -2, 3 => 3, 5 => 3, 11 => -2, 25 => 3, 51 => -2, 77 => -2, 155 => 3],
  sparse![156; 1 => 3, 3 => -2, 5 => -2, 11 => 3, 25 => -2, 51 => 3, 77 => 3, 155 => -2],
  sparse![156; 1 => 1, 3 => 1, 77 => 1, 155 => 1],
  sparse![156; 1 => 1, 11 => 1, 51 => 1, 77 => 1],
  sparse![156; 3 => 1, 5 => 1, 25 => 1, 155 => 1],
  sparse![156; 5 => 1, 11 => 1, 25 => 1, 51 => 1],
  sparse![156; 1 => -1, 3 => 2, 11 => 1, 25 => 2, 51 => -1, 77 => 1],
  sparse![156; 3 => 1, 5 => -1, 11 => 2, 25 => 1, 77 => 2, 155 => -1],
  sparse![156; 0 => 2, 1 => 1, 2 => -1, 3 => -1, 11 => 1, 12 => -1, 38 => 2, 51 => 1, 77 => 1, 155 => -1],
  sparse![156; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -2, 11 => 1, 12 => 3, 25 => -2, 38 => -2, 51 => 1, 77 => 3, 155 => -1],
]
```

### Level 157

dim S₂ = **12**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **26**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 158

dim S₂ = **19**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **40**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![158; 0 => 1, 1 => 1, 78 => 1, 157 => 1],
]
```

### Level 159

dim S₂ = **17**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **36**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![159; 0 => 1, 2 => 1, 52 => 1, 158 => 1],
]
```

### Level 160

dim S₂ = **17**; eta rank = **17**; full eta basis = **YES**; Sturm bound B = **48**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![160; 1 => 2, 9 => 2],
  sparse![160; 3 => 2, 19 => 2],
  sparse![160; 7 => 2, 39 => 2],
  sparse![160; 15 => 2, 79 => 2],
  sparse![160; 3 => 2, 7 => 2],
  sparse![160; 19 => 2, 39 => 2],
  sparse![160; 0 => -2, 1 => 5, 3 => -1, 4 => 2, 9 => -1, 19 => 1],
  sparse![160; 1 => -2, 3 => 5, 7 => -1, 9 => 2, 19 => -1, 39 => 1],
  sparse![160; 3 => -2, 7 => 5, 15 => -1, 19 => 2, 39 => -1, 79 => 1],
  sparse![160; 0 => -2, 1 => 5, 3 => -1, 4 => -2, 9 => 5, 19 => -1],
  sparse![160; 0 => -1, 1 => 1, 3 => 2, 4 => 1, 9 => 1],
  sparse![160; 1 => -2, 3 => 5, 7 => -1, 9 => -2, 19 => 5, 39 => -1],
  sparse![160; 1 => -1, 3 => 1, 7 => 2, 9 => 1, 19 => 1],
  sparse![160; 3 => 1, 7 => 1, 19 => 1, 39 => 1],
  sparse![160; 0 => -2, 1 => 3, 3 => 2, 4 => 2, 7 => -1, 9 => -3, 19 => 4, 39 => -1],
  sparse![160; 0 => -2, 1 => 4, 3 => -2, 4 => 2, 7 => 2],
  sparse![160; 0 => -2, 1 => 5, 3 => -3, 7 => 3, 15 => -1, 19 => 1, 39 => 2, 79 => -1],
]
```

### Level 161

dim S₂ = **15**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **32**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![161; 0 => 2, 22 => 2],
  sparse![161; 6 => 2, 160 => 2],
  sparse![161; 0 => 1, 6 => 1, 22 => 1, 160 => 1],
]
```

### Level 162

dim S₂ = **16**; eta rank = **16**; full eta basis = **YES**; Sturm bound B = **54**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![162; 2 => 2, 8 => 2],
  sparse![162; 5 => 2, 17 => 2],
  sparse![162; 8 => 2, 26 => 2],
  sparse![162; 17 => 2, 53 => 2],
  sparse![162; 0 => -1, 1 => 2, 5 => 2, 8 => 1],
  sparse![162; 0 => -1, 1 => 2, 2 => 1, 17 => 1, 26 => 2, 53 => -1],
  sparse![162; 2 => -1, 5 => 2, 17 => 2, 26 => 1],
  sparse![162; 2 => -1, 5 => 2, 8 => 1, 53 => 1, 80 => 2, 161 => -1],
  sparse![162; 2 => -1, 8 => 6, 26 => -1],
  sparse![162; 2 => 1, 8 => 2, 26 => 1],
  sparse![162; 5 => -1, 17 => 6, 53 => -1],
  sparse![162; 5 => 1, 17 => 2, 53 => 1],
  sparse![162; 0 => -1, 1 => 2, 2 => -1, 5 => 2, 8 => 1, 26 => 1],
  sparse![162; 0 => -1, 1 => 2, 5 => -1, 8 => 1, 17 => 4, 53 => -1],
  sparse![162; 0 => -1, 1 => 2, 5 => -1, 8 => 2, 17 => 2, 26 => -1, 80 => 2, 161 => -1],
  sparse![162; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 17 => 1, 26 => 2],
]
```

### Level 163

dim S₂ = **13**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **27**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 164

dim S₂ = **19**; eta rank = **7**; full eta basis = **NO**; Sturm bound B = **42**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![164; 0 => 2, 1 => -1, 3 => 1, 40 => -2, 81 => 5, 163 => -1],
  sparse![164; 0 => 1, 1 => -1, 3 => 2, 40 => -1, 81 => 5, 163 => -2],
  sparse![164; 0 => 1, 1 => 2, 3 => -1, 40 => -1, 81 => 2, 163 => 1],
  sparse![164; 1 => 2, 81 => 2],
  sparse![164; 0 => -1, 1 => 2, 3 => 1, 40 => 1, 81 => 2, 163 => -1],
  sparse![164; 0 => -1, 1 => 5, 3 => -2, 40 => 1, 81 => -1, 163 => 2],
  sparse![164; 0 => -2, 1 => 5, 3 => -1, 40 => 2, 81 => -1, 163 => 1],
]
```

### Level 165

dim S₂ = **21**; eta rank = **14**; full eta basis = **NO**; Sturm bound B = **48**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![165; 0 => 2, 10 => 2],
  sparse![165; 2 => 2, 32 => 2],
  sparse![165; 4 => 2, 54 => 2],
  sparse![165; 14 => 2, 164 => 2],
  sparse![165; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![165; 10 => 1, 32 => 1, 54 => 1, 164 => 1],
  sparse![165; 0 => 1, 2 => 1, 10 => 1, 32 => 1],
  sparse![165; 4 => 1, 14 => 1, 54 => 1, 164 => 1],
  sparse![165; 0 => 1, 4 => 1, 10 => 1, 54 => 1],
  sparse![165; 2 => 1, 14 => 1, 32 => 1, 164 => 1],
  sparse![165; 0 => -1, 2 => 2, 4 => 2, 10 => 2, 14 => -1, 32 => -1, 54 => -1, 164 => 2],
  sparse![165; 2 => 1, 4 => 1, 32 => 1, 54 => 1],
  sparse![165; 0 => 1, 10 => 1, 14 => 1, 164 => 1],
  sparse![165; 0 => 2, 2 => -1, 4 => -1, 10 => -1, 14 => 2, 32 => 2, 54 => 2, 164 => -1],
]
```

### Level 166

dim S₂ = **20**; eta rank = **2**; full eta basis = **NO**; Sturm bound B = **42**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![166; 0 => 2, 82 => 2],
  sparse![166; 1 => 2, 165 => 2],
]
```

### Level 167

dim S₂ = **14**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **28**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![167; 0 => 2, 166 => 2],
]
```

### Level 168

dim S₂ = **25**; eta rank = **25**; full eta basis = **YES**; Sturm bound B = **64**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![168; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![168; 1 => 1, 3 => 1, 13 => 1, 27 => 1],
  sparse![168; 2 => 1, 5 => 1, 20 => 1, 41 => 1],
  sparse![168; 3 => 1, 7 => 1, 27 => 1, 55 => 1],
  sparse![168; 5 => 1, 11 => 1, 41 => 1, 83 => 1],
  sparse![168; 11 => 1, 23 => 1, 83 => 1, 167 => 1],
  sparse![168; 1 => 1, 3 => 1, 5 => 1, 11 => 1],
  sparse![168; 13 => 1, 27 => 1, 41 => 1, 83 => 1],
  sparse![168; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 6 => 4, 13 => -2, 20 => -1, 41 => 1],
  sparse![168; 0 => -1, 1 => 1, 2 => 4, 5 => -2, 6 => 1, 13 => -1, 20 => -2, 41 => 4],
  sparse![168; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 6 => -1, 13 => 2, 20 => 2, 41 => -1],
  sparse![168; 1 => -2, 3 => 4, 5 => 1, 11 => -1, 13 => 4, 27 => -2, 41 => -1, 83 => 1],
  sparse![168; 1 => -1, 3 => 1, 5 => 4, 11 => -2, 13 => 1, 27 => -1, 41 => -2, 83 => 4],
  sparse![168; 3 => -2, 7 => 4, 11 => 1, 23 => -1, 27 => 4, 55 => -2, 83 => -1, 167 => 1],
  sparse![168; 3 => -1, 7 => 1, 11 => 4, 23 => -2, 27 => 1, 55 => -1, 83 => -2, 167 => 4],
  sparse![168; 0 => 1, 6 => 1, 7 => 1, 55 => 1],
  sparse![168; 1 => -1, 3 => 3, 13 => 3, 27 => -1],
  sparse![168; 2 => 1, 20 => 1, 23 => 1, 167 => 1],
  sparse![168; 5 => -1, 11 => 3, 41 => 3, 83 => -1],
  sparse![168; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -2, 11 => 1, 13 => 4, 27 => -2, 41 => -1, 83 => 1],
  sparse![168; 0 => -3, 1 => 7, 2 => 2, 3 => -2, 5 => -3, 6 => 1, 11 => 1, 13 => -3, 20 => -2, 27 => 2, 41 => 7, 83 => -3],
  sparse![168; 1 => -3, 3 => 7, 5 => 1, 7 => -2, 11 => -2, 23 => 1, 27 => 4, 55 => -2, 83 => -1, 167 => 1],
  sparse![168; 1 => -3, 3 => 7, 5 => 2, 7 => -2, 11 => -3, 13 => 1, 23 => 1, 27 => -3, 41 => -2, 55 => 2, 83 => 7, 167 => -3],
  sparse![168; 1 => 2, 3 => -2, 5 => -1, 7 => 1, 11 => 3, 23 => -1, 41 => 1, 55 => 1, 83 => 1, 167 => -1],
  sparse![168; 1 => -1, 3 => 3, 5 => 2, 7 => -1, 11 => -2, 13 => 1, 23 => 1, 27 => 1, 55 => -1, 167 => 1],
]
```

### Level 169

dim S₂ = **8**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **30**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 170

dim S₂ = **23**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **54**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 171

dim S₂ = **17**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **40**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![171; 0 => 1, 8 => 1, 18 => -1, 56 => 4, 170 => -1],
  sparse![171; 2 => 2, 56 => 2],
  sparse![171; 0 => -1, 2 => 4, 8 => -1, 18 => 1, 170 => 1],
]
```

### Level 172

dim S₂ = **20**; eta rank = **6**; full eta basis = **NO**; Sturm bound B = **44**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![172; 0 => 3, 1 => -1, 42 => -1, 85 => 3],
  sparse![172; 0 => -1, 1 => 3, 42 => 3, 85 => -1],
  sparse![172; 1 => 3, 3 => -1, 85 => -1, 171 => 3],
  sparse![172; 1 => -1, 3 => 3, 85 => 3, 171 => -1],
  sparse![172; 0 => 1, 3 => 1, 42 => -3, 85 => 8, 171 => -3],
  sparse![172; 0 => -3, 1 => 8, 3 => -3, 42 => 1, 171 => 1],
]
```

### Level 173

dim S₂ = **14**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **29**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 174

dim S₂ = **27**; eta rank = **10**; full eta basis = **NO**; Sturm bound B = **60**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![174; 0 => 1, 2 => 1, 28 => 1, 86 => 1],
  sparse![174; 1 => 1, 5 => 1, 57 => 1, 173 => 1],
  sparse![174; 0 => -1, 1 => 3, 2 => 1, 5 => -1, 28 => 1, 57 => -1, 86 => -1, 173 => 3],
  sparse![174; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 28 => 2, 57 => -1, 86 => -1, 173 => 2],
  sparse![174; 0 => 1, 1 => 1, 86 => 1, 173 => 1],
  sparse![174; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 28 => 3, 57 => -1, 86 => -1, 173 => 1],
  sparse![174; 2 => 1, 5 => 1, 28 => 1, 57 => 1],
  sparse![174; 0 => 1, 1 => -1, 2 => -1, 5 => 3, 28 => -1, 57 => 3, 86 => 1, 173 => -1],
  sparse![174; 0 => 2, 1 => -1, 2 => -1, 5 => 2, 28 => -1, 57 => 2, 86 => 2, 173 => -1],
  sparse![174; 0 => 3, 1 => -1, 2 => -1, 5 => 1, 28 => -1, 57 => 1, 86 => 3, 173 => -1],
]
```

### Level 175

dim S₂ = **15**; eta rank = **10**; full eta basis = **NO**; Sturm bound B = **40**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![175; 0 => 2, 34 => 2],
  sparse![175; 0 => 1, 4 => 1, 6 => 1, 34 => 1],
  sparse![175; 4 => 2, 6 => 2],
  sparse![175; 4 => 2, 174 => 2],
  sparse![175; 4 => 1, 24 => 1, 34 => 1, 174 => 1],
  sparse![175; 24 => 2, 34 => 2],
  sparse![175; 0 => 1, 4 => 1, 34 => 1, 174 => 1],
  sparse![175; 4 => 2, 6 => 1, 174 => 1],
  sparse![175; 0 => 1, 24 => 1, 34 => 2],
  sparse![175; 4 => 1, 6 => 1, 24 => 1, 34 => 1],
]
```

### Level 176

dim S₂ = **19**; eta rank = **19**; full eta basis = **YES**; Sturm bound B = **48**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![176; 0 => 2, 10 => 2],
  sparse![176; 1 => 2, 21 => 2],
  sparse![176; 3 => 2, 43 => 2],
  sparse![176; 7 => 2, 87 => 2],
  sparse![176; 15 => 2, 175 => 2],
  sparse![176; 0 => 1, 3 => -1, 7 => 2, 10 => 1, 21 => -2, 43 => 5, 87 => -2],
  sparse![176; 1 => 1, 3 => 1, 21 => 1, 43 => 1],
  sparse![176; 0 => -2, 1 => 4, 3 => 1, 7 => -1, 10 => 2, 21 => -2, 43 => 3, 87 => -1],
  sparse![176; 0 => -2, 1 => 5, 3 => -2, 7 => 1, 10 => 2, 21 => -1, 87 => 1],
  sparse![176; 0 => -2, 1 => 5, 3 => -1, 10 => -2, 21 => 5, 43 => -1],
  sparse![176; 1 => 1, 7 => -1, 15 => 2, 21 => 1, 43 => -2, 87 => 5, 175 => -2],
  sparse![176; 3 => 1, 7 => 1, 43 => 1, 87 => 1],
  sparse![176; 1 => -2, 3 => 4, 7 => 1, 15 => -1, 21 => 2, 43 => -2, 87 => 3, 175 => -1],
  sparse![176; 1 => -2, 3 => 5, 7 => -1, 21 => -2, 43 => 5, 87 => -1],
  sparse![176; 0 => 1, 10 => -1, 15 => 1, 21 => 3, 43 => -2, 87 => 3, 175 => -1],
  sparse![176; 1 => 1, 7 => 1, 21 => 1, 87 => 1],
  sparse![176; 0 => -2, 1 => 4, 10 => 2, 21 => -2, 43 => 2],
  sparse![176; 0 => -2, 1 => 4, 3 => 1, 7 => -1, 10 => -2, 21 => 4, 43 => 1, 87 => -1],
  sparse![176; 0 => -2, 1 => 6, 3 => -2, 21 => 1, 43 => -2, 87 => 5, 175 => -2],
]
```

### Level 177

dim S₂ = **19**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **40**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![177; 0 => 2, 58 => 2],
  sparse![177; 2 => 2, 176 => 2],
  sparse![177; 0 => 1, 2 => 1, 58 => 1, 176 => 1],
]
```

### Level 178

dim S₂ = **21**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **45**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 179

dim S₂ = **15**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **30**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![179; 0 => 2, 178 => 2],
]
```

### Level 180

dim S₂ = **25**; eta rank = **25**; full eta basis = **YES**; Sturm bound B = **72**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![180; 0 => -4, 1 => 8, 2 => 3, 3 => -3, 4 => 2, 5 => -3, 9 => -1, 11 => 1, 14 => -1, 29 => 2],
  sparse![180; 0 => -4, 1 => 9, 2 => 2, 3 => -3, 4 => 1, 5 => -3, 9 => -1, 11 => 1, 14 => -1, 29 => 3],
  sparse![180; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 11 => 1, 14 => -1, 29 => 4, 59 => -1],
  sparse![180; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 8 => 1, 11 => 1, 14 => 1, 17 => -2, 29 => -2, 35 => 1, 44 => -3, 59 => 1, 89 => 8, 179 => -3],
  sparse![180; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 4 => 2, 5 => -3, 9 => -3, 11 => 2, 14 => 1, 19 => 1, 29 => 2, 59 => -1],
  sparse![180; 0 => -4, 1 => 10, 2 => 2, 3 => -4, 4 => 1, 5 => -3, 9 => -3, 11 => 1, 14 => -1, 19 => 2, 29 => 2, 59 => 1],
  sparse![180; 0 => -3, 1 => 2, 2 => 7, 4 => 3, 5 => -3, 8 => -2, 9 => -1, 14 => -1, 17 => 1, 29 => 1],
  sparse![180; 0 => -3, 1 => 4, 2 => 4, 3 => -1, 4 => 3, 5 => -2, 8 => -1, 9 => -1, 14 => -1, 29 => 1, 35 => 1],
  sparse![180; 0 => -3, 1 => 4, 2 => 6, 3 => -1, 5 => -3, 8 => -2, 9 => 1, 14 => -1, 17 => 1, 19 => -1, 44 => 2, 59 => 2, 89 => -1],
  sparse![180; 0 => -3, 1 => 5, 2 => 1, 4 => 3, 5 => -1, 9 => -1, 14 => -1, 29 => 1],
  sparse![180; 0 => -3, 1 => 5, 2 => 3, 3 => -1, 4 => 2, 5 => -2, 8 => -1, 9 => -1, 14 => -1, 17 => 1, 59 => 2, 89 => 1, 179 => -1],
  sparse![180; 0 => -3, 1 => 6, 2 => 1, 3 => -2, 4 => 3, 5 => -2, 9 => -1, 11 => 1, 14 => -1, 17 => 2, 29 => 1, 35 => -1],
  sparse![180; 0 => -3, 1 => 6, 2 => 2, 3 => -2, 4 => 1, 5 => -2, 11 => 1, 59 => 1],
  sparse![180; 0 => -3, 1 => 6, 2 => 2, 3 => -2, 4 => 3, 5 => -3, 8 => -1, 9 => -3, 11 => 2, 14 => -2, 17 => 2, 19 => 1, 29 => 3, 35 => -1, 44 => 1, 89 => -1],
  sparse![180; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 5 => -2, 8 => -1, 9 => 1, 14 => -1, 19 => -1, 35 => 1, 44 => 2, 59 => 2, 89 => -1],
  sparse![180; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 4 => 1, 5 => -3, 8 => -1, 9 => -2, 11 => 1, 14 => -1, 17 => 2, 19 => 1, 29 => 3, 35 => -1, 44 => 1, 59 => -1, 89 => -2, 179 => 2],
  sparse![180; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 4 => 1, 5 => -3, 9 => -2, 11 => 1, 14 => -3, 19 => 1, 29 => 6, 44 => 2, 59 => -2, 89 => -1],
  sparse![180; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -2, 11 => 1, 17 => 1, 29 => 1, 35 => -1, 59 => -1, 89 => -1, 179 => 3],
  sparse![180; 0 => -2, 1 => 1, 2 => 5, 4 => 2, 5 => -2, 8 => -1, 9 => -1, 14 => 1, 17 => 1, 44 => -1, 89 => 1],
  sparse![180; 0 => -2, 1 => 1, 2 => 5, 4 => 2, 5 => -2, 9 => -1, 14 => -1, 29 => 2],
  sparse![180; 0 => -2, 1 => 1, 2 => 5, 4 => 2, 5 => -1, 8 => -1, 9 => -1, 14 => -2, 29 => 2, 89 => 1],
  sparse![180; 0 => -2, 1 => 1, 2 => 6, 4 => 2, 5 => -3, 8 => -3, 9 => -1, 14 => -1, 17 => 4, 35 => -1, 59 => 2, 89 => 1, 179 => -1],
  sparse![180; 0 => -2, 1 => 1, 2 => 7, 5 => -3, 8 => -3, 14 => -1, 17 => 2, 29 => 1, 44 => 3, 89 => -1],
  sparse![180; 0 => -2, 1 => 1, 2 => 7, 5 => -3, 8 => -2, 14 => 1, 17 => 1, 29 => 1],
  sparse![180; 0 => -2, 1 => 2, 2 => 3, 3 => 1, 4 => 2, 5 => -2, 8 => -1, 9 => -1, 14 => -3, 17 => 1, 29 => 6, 44 => 1, 59 => -2, 89 => -2, 179 => 1],
]
```

### Level 181

dim S₂ = **14**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **30**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 182

dim S₂ = **25**; eta rank = **16**; full eta basis = **NO**; Sturm bound B = **56**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![182; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![182; 12 => 1, 25 => 1, 90 => 1, 181 => 1],
  sparse![182; 0 => -1, 1 => 3, 90 => 3, 181 => -1],
  sparse![182; 0 => 3, 1 => -1, 90 => -1, 181 => 3],
  sparse![182; 1 => 1, 6 => 1, 12 => -1, 25 => 2, 90 => 2, 181 => -1],
  sparse![182; 0 => -1, 1 => 2, 6 => 2, 13 => -1, 25 => 1, 90 => 1],
  sparse![182; 0 => 2, 1 => -1, 6 => 2, 12 => -1, 13 => -1, 25 => 2, 90 => -1, 181 => 2],
  sparse![182; 0 => 2, 1 => -1, 12 => -1, 13 => 1, 25 => 2, 90 => 1],
  sparse![182; 0 => 1, 6 => 1, 25 => 1, 181 => 1],
  sparse![182; 1 => 1, 6 => 2, 12 => 1, 13 => -1, 90 => -1, 181 => 2],
  sparse![182; 0 => 1, 6 => -1, 13 => 2, 25 => 1, 90 => 2, 181 => -1],
  sparse![182; 1 => 1, 12 => 1, 13 => 1, 90 => 1],
  sparse![182; 0 => -1, 1 => 2, 6 => 1, 12 => 2, 25 => -1, 181 => 1],
  sparse![182; 0 => -1, 1 => 2, 6 => -1, 12 => 2, 13 => 2, 25 => -1, 90 => 2, 181 => -1],
  sparse![182; 0 => 2, 1 => -1, 6 => -1, 12 => 1, 13 => 2, 181 => 1],
  sparse![182; 0 => 1, 12 => 2, 13 => 1, 25 => -1, 90 => -1, 181 => 2],
]
```

### Level 183

dim S₂ = **19**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **41**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 184

dim S₂ = **21**; eta rank = **16**; full eta basis = **NO**; Sturm bound B = **48**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![184; 0 => 2, 22 => 2],
  sparse![184; 1 => 2, 45 => 2],
  sparse![184; 3 => 2, 91 => 2],
  sparse![184; 7 => 2, 183 => 2],
  sparse![184; 0 => -1, 1 => 3, 22 => -1, 45 => 3],
  sparse![184; 0 => 1, 1 => 1, 22 => 1, 45 => 1],
  sparse![184; 0 => 3, 1 => -1, 22 => 3, 45 => -1],
  sparse![184; 1 => -1, 3 => 3, 45 => -1, 91 => 3],
  sparse![184; 1 => 1, 3 => 1, 45 => 1, 91 => 1],
  sparse![184; 3 => -1, 7 => 3, 91 => -1, 183 => 3],
  sparse![184; 3 => 1, 7 => 1, 91 => 1, 183 => 1],
  sparse![184; 0 => 1, 1 => -1, 3 => 2, 22 => 1, 45 => -1, 91 => 2],
  sparse![184; 1 => 1, 3 => -1, 7 => 2, 45 => 1, 91 => -1, 183 => 2],
  sparse![184; 0 => 1, 1 => -2, 3 => 5, 7 => -2, 22 => 1, 45 => -2, 91 => 5, 183 => -2],
  sparse![184; 0 => 2, 1 => -2, 3 => 3, 7 => -1, 22 => 2, 45 => -2, 91 => 3, 183 => -1],
  sparse![184; 0 => 1, 1 => -2, 3 => 4, 7 => -1, 22 => 1, 45 => -2, 91 => 4, 183 => -1],
]
```

### Level 185

dim S₂ = **17**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **38**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 186

dim S₂ = **29**; eta rank = **12**; full eta basis = **NO**; Sturm bound B = **64**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![186; 0 => 1, 1 => 1, 30 => 1, 61 => 1],
  sparse![186; 2 => 1, 5 => 1, 92 => 1, 185 => 1],
  sparse![186; 0 => 1, 1 => -1, 2 => -2, 5 => 4, 30 => -1, 61 => 1, 92 => 4, 185 => -2],
  sparse![186; 0 => -1, 1 => 1, 2 => 4, 5 => -2, 30 => 1, 61 => -1, 92 => -2, 185 => 4],
  sparse![186; 0 => 2, 1 => -1, 5 => 1, 30 => -1, 61 => 2, 92 => 1],
  sparse![186; 0 => 1, 2 => -1, 5 => 2, 61 => 1, 92 => 2, 185 => -1],
  sparse![186; 0 => 2, 1 => -1, 2 => -1, 5 => 2, 30 => 2, 61 => -1, 92 => -1, 185 => 2],
  sparse![186; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 30 => -1, 61 => 2, 92 => 2, 185 => -1],
  sparse![186; 1 => 1, 2 => 2, 5 => -1, 30 => 1, 92 => -1, 185 => 2],
  sparse![186; 0 => -1, 1 => 2, 2 => 1, 30 => 2, 61 => -1, 185 => 1],
  sparse![186; 0 => 4, 1 => -2, 2 => -1, 5 => 1, 30 => -2, 61 => 4, 92 => 1, 185 => -1],
  sparse![186; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 30 => 4, 61 => -2, 92 => -1, 185 => 1],
]
```

### Level 187

dim S₂ = **17**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **36**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![187; 0 => 2, 10 => 2],
  sparse![187; 16 => 2, 186 => 2],
  sparse![187; 0 => 1, 10 => 1, 16 => 1, 186 => 1],
]
```

### Level 188

dim S₂ = **22**; eta rank = **15**; full eta basis = **NO**; Sturm bound B = **48**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![188; 0 => 2, 46 => 2],
  sparse![188; 1 => 2, 93 => 2],
  sparse![188; 3 => 2, 187 => 2],
  sparse![188; 0 => -1, 1 => 3, 46 => -1, 93 => 3],
  sparse![188; 0 => 1, 1 => 1, 46 => 1, 93 => 1],
  sparse![188; 0 => 3, 1 => -1, 46 => 3, 93 => -1],
  sparse![188; 1 => -1, 3 => 3, 93 => -1, 187 => 3],
  sparse![188; 1 => 1, 3 => 1, 93 => 1, 187 => 1],
  sparse![188; 1 => 3, 3 => -1, 93 => 3, 187 => -1],
  sparse![188; 0 => 1, 1 => -1, 3 => 2, 46 => 1, 93 => -1, 187 => 2],
  sparse![188; 0 => -1, 1 => 2, 3 => 1, 46 => -1, 93 => 2, 187 => 1],
  sparse![188; 0 => 1, 3 => 1, 46 => 1, 187 => 1],
  sparse![188; 0 => 2, 1 => -1, 3 => 1, 46 => 2, 93 => -1, 187 => 1],
  sparse![188; 0 => -1, 1 => 4, 3 => -1, 46 => -1, 93 => 4, 187 => -1],
  sparse![188; 0 => 1, 1 => 2, 3 => -1, 46 => 1, 93 => 2, 187 => -1],
]
```

### Level 189

dim S₂ = **19**; eta rank = **17**; full eta basis = **NO**; Sturm bound B = **48**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![189; 2 => 2, 8 => 2],
  sparse![189; 20 => 2, 62 => 2],
  sparse![189; 2 => 2, 20 => 2],
  sparse![189; 0 => -1, 2 => 4, 6 => 1, 8 => -1, 62 => 1],
  sparse![189; 0 => 1, 6 => -1, 8 => 1, 20 => 4, 62 => -1],
  sparse![189; 8 => 2, 62 => 2],
  sparse![189; 2 => -1, 8 => 4, 20 => 1, 26 => -1, 188 => 1],
  sparse![189; 2 => 1, 20 => -1, 26 => 1, 62 => 4, 188 => -1],
  sparse![189; 0 => 1, 6 => 2, 8 => 1],
  sparse![189; 0 => 2, 6 => 1, 62 => 1],
  sparse![189; 2 => 1, 8 => 1, 20 => 1, 62 => 1],
  sparse![189; 0 => -1, 2 => 3, 6 => 1, 20 => -1, 62 => 2],
  sparse![189; 2 => -1, 8 => 3, 20 => 3, 62 => -1],
  sparse![189; 2 => 1, 26 => 1, 188 => 2],
  sparse![189; 20 => 1, 26 => 2, 188 => 1],
  sparse![189; 8 => 3, 20 => 2, 26 => -1, 62 => -1, 188 => 1],
  sparse![189; 2 => 2, 8 => -1, 26 => 1, 62 => 3, 188 => -1],
]
```

### Level 190

dim S₂ = **27**; eta rank = **23**; full eta basis = **NO**; Sturm bound B = **60**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![190; 0 => 3, 1 => -1, 18 => -1, 37 => 3],
  sparse![190; 0 => -1, 1 => 3, 18 => 3, 37 => -1],
  sparse![190; 4 => 3, 9 => -1, 94 => -1, 189 => 3],
  sparse![190; 4 => -1, 9 => 3, 94 => 3, 189 => -1],
  sparse![190; 0 => 2, 94 => 2],
  sparse![190; 0 => 1, 4 => 1, 18 => 1, 94 => 1],
  sparse![190; 4 => 2, 18 => 2],
  sparse![190; 1 => 2, 189 => 2],
  sparse![190; 1 => 1, 9 => 1, 37 => 1, 189 => 1],
  sparse![190; 9 => 2, 37 => 2],
  sparse![190; 0 => 3, 1 => -1, 18 => 4, 37 => -2, 94 => -1, 189 => 1],
  sparse![190; 0 => 4, 1 => -2, 4 => -1, 9 => 1, 18 => 3, 37 => -1],
  sparse![190; 0 => -2, 1 => 4, 4 => 1, 9 => -1, 18 => 4, 37 => -2, 94 => -1, 189 => 1],
  sparse![190; 0 => 4, 1 => -2, 4 => -1, 9 => 1, 18 => -2, 37 => 4, 94 => 1, 189 => -1],
  sparse![190; 0 => 1, 1 => 1, 94 => 1, 189 => 1],
  sparse![190; 0 => -1, 1 => 2, 4 => 2, 9 => -1, 18 => 2, 37 => -1, 94 => -1, 189 => 2],
  sparse![190; 1 => 1, 4 => 2, 9 => -1, 18 => 2, 37 => -1, 189 => 1],
  sparse![190; 0 => 1, 4 => 2, 9 => -1, 18 => 2, 37 => -1, 94 => 1],
  sparse![190; 0 => -1, 1 => 2, 4 => 1, 18 => 1, 94 => -1, 189 => 2],
  sparse![190; 1 => 1, 4 => 1, 18 => 1, 189 => 1],
  sparse![190; 0 => 1, 9 => 1, 37 => 1, 94 => 1],
  sparse![190; 4 => 1, 9 => 1, 18 => 1, 37 => 1],
  sparse![190; 0 => -1, 1 => 3, 4 => 1, 9 => -1, 18 => 1, 37 => -1, 94 => -1, 189 => 3],
]
```

### Level 191

dim S₂ = **16**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **32**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![191; 0 => 2, 190 => 2],
]
```

### Level 192

dim S₂ = **21**; eta rank = **21**; full eta basis = **YES**; Sturm bound B = **64**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![192; 0 => -4, 1 => 9, 2 => 2, 3 => -4, 5 => -2, 7 => 1, 11 => 2],
  sparse![192; 0 => -4, 1 => 11, 2 => 2, 3 => -3, 5 => -4, 11 => 1, 23 => 1],
  sparse![192; 0 => -3, 1 => 7, 2 => 1, 3 => -4, 5 => -1, 7 => 3, 11 => 2, 15 => -1, 23 => -1, 47 => 1],
  sparse![192; 0 => -3, 1 => 7, 2 => 1, 3 => -3, 5 => -1, 7 => 1, 11 => 1, 15 => -1, 31 => 2, 47 => 1, 63 => -1, 95 => -1, 191 => 1],
  sparse![192; 0 => -3, 1 => 9, 2 => 1, 3 => -4, 5 => -3, 7 => 2, 11 => 2],
  sparse![192; 0 => -3, 1 => 9, 2 => 1, 3 => -3, 5 => -3, 11 => 1, 23 => 1, 31 => 2, 63 => -1, 95 => -1, 191 => 1],
  sparse![192; 0 => -2, 1 => 2, 3 => 7, 5 => 1, 7 => -3, 11 => -3, 23 => 2],
  sparse![192; 0 => -2, 1 => 2, 2 => 2, 3 => 3, 7 => -1, 11 => -1, 23 => 1],
  sparse![192; 0 => -2, 1 => 2, 2 => 4, 3 => -1, 5 => -1, 7 => 1, 11 => 1],
  sparse![192; 0 => -2, 1 => 3, 2 => 2, 3 => 1, 5 => -1, 7 => -1, 15 => 2, 23 => 1, 31 => -1, 47 => -1, 95 => 1],
  sparse![192; 0 => -2, 1 => 4, 5 => -1, 11 => 4, 23 => -1],
  sparse![192; 0 => -2, 1 => 4, 2 => 2, 3 => -4, 5 => -2, 7 => 6, 11 => 2, 15 => -2],
  sparse![192; 0 => -2, 1 => 4, 2 => 2, 3 => -3, 5 => -2, 7 => 4, 11 => 1, 15 => -2, 23 => 1, 31 => 2, 63 => -1, 95 => -1, 191 => 1],
  sparse![192; 0 => -2, 1 => 4, 2 => 2, 3 => -2, 5 => -2, 7 => 1, 15 => 2, 23 => 1, 31 => -1, 47 => 2, 95 => -1],
  sparse![192; 0 => -1, 2 => 1, 3 => 3, 5 => 1, 7 => -1, 11 => -1, 23 => 1, 31 => 2, 63 => -1, 95 => -1, 191 => 1],
  sparse![192; 0 => -1, 2 => 1, 3 => 4, 5 => 1, 7 => -1, 11 => -2, 15 => -1, 23 => 1, 31 => 2, 47 => 1, 63 => -1, 95 => -1, 191 => 1],
  sparse![192; 0 => -1, 2 => 3, 3 => -1, 7 => 3, 11 => 1, 15 => -1, 23 => -1, 47 => 1],
  sparse![192; 0 => -1, 2 => 3, 7 => 1, 15 => -1, 31 => 2, 47 => 1, 63 => -1, 95 => -1, 191 => 1],
  sparse![192; 0 => -1, 1 => 1, 2 => 1, 3 => 1, 7 => -1, 15 => 2, 23 => 1, 31 => 1, 47 => -1, 63 => -1, 191 => 1],
  sparse![192; 1 => -3, 3 => 6, 5 => 1, 7 => 3, 11 => -2, 15 => -3, 31 => 2, 47 => 1, 63 => -1, 95 => -1, 191 => 1],
  sparse![192; 1 => -2, 3 => 5, 7 => -2, 15 => 2, 23 => 1, 31 => -1, 47 => -3, 95 => 6, 191 => -2],
]
```

### Level 193

dim S₂ = **15**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **32**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 194

dim S₂ = **23**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **49**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 195

dim S₂ = **25**; eta rank = **10**; full eta basis = **NO**; Sturm bound B = **56**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![195; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![195; 12 => 1, 38 => 1, 64 => 1, 194 => 1],
  sparse![195; 0 => 1, 2 => 1, 64 => 1, 194 => 1],
  sparse![195; 0 => -1, 2 => 2, 4 => 2, 12 => 2, 14 => -1, 38 => -1, 64 => -1, 194 => 2],
  sparse![195; 0 => 1, 4 => 1, 38 => 1, 194 => 1],
  sparse![195; 2 => 1, 4 => 1, 12 => 1, 194 => 1],
  sparse![195; 0 => 1, 14 => 1, 38 => 1, 64 => 1],
  sparse![195; 2 => 1, 12 => 1, 14 => 1, 64 => 1],
  sparse![195; 0 => 2, 2 => -1, 4 => -1, 12 => -1, 14 => 2, 38 => 2, 64 => 2, 194 => -1],
  sparse![195; 4 => 1, 12 => 1, 14 => 1, 38 => 1],
]
```

### Level 196

dim S₂ = **17**; eta rank = **14**; full eta basis = **NO**; Sturm bound B = **56**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![196; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![196; 1 => 1, 3 => 1, 13 => 1, 27 => 1],
  sparse![196; 6 => 1, 13 => 1, 48 => 1, 97 => 1],
  sparse![196; 13 => 1, 27 => 1, 97 => 1, 195 => 1],
  sparse![196; 0 => 2, 1 => -1, 6 => 1, 13 => 1, 48 => -1, 97 => 2],
  sparse![196; 0 => 1, 6 => 1, 13 => 1, 97 => 1],
  sparse![196; 1 => 1, 6 => 1, 13 => 1, 48 => 1],
  sparse![196; 0 => -1, 1 => 2, 6 => 1, 13 => 1, 48 => 2, 97 => -1],
  sparse![196; 1 => 2, 3 => -1, 13 => 1, 27 => 1, 97 => -1, 195 => 2],
  sparse![196; 1 => 1, 13 => 1, 27 => 1, 195 => 1],
  sparse![196; 3 => 1, 13 => 1, 27 => 1, 97 => 1],
  sparse![196; 1 => -1, 3 => 2, 13 => 1, 27 => 1, 97 => 2, 195 => -1],
  sparse![196; 0 => -2, 1 => 5, 3 => -2, 6 => -1, 13 => 4, 27 => -1, 48 => 1, 97 => -1, 195 => 1],
  sparse![196; 0 => -1, 1 => 2, 6 => -1, 13 => 4, 27 => -1, 97 => 2, 195 => -1],
]
```

### Level 197

dim S₂ = **16**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **33**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 198

dim S₂ = **29**; eta rank = **28**; full eta basis = **NO**; Sturm bound B = **72**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![198; 0 => 2, 10 => 2],
  sparse![198; 1 => 2, 21 => 2],
  sparse![198; 2 => 2, 32 => 2],
  sparse![198; 5 => 2, 65 => 2],
  sparse![198; 8 => 2, 98 => 2],
  sparse![198; 17 => 2, 197 => 2],
  sparse![198; 0 => 1, 2 => 1, 10 => 1, 32 => 1],
  sparse![198; 1 => 1, 5 => 1, 21 => 1, 65 => 1],
  sparse![198; 2 => 1, 8 => 1, 32 => 1, 98 => 1],
  sparse![198; 5 => 1, 17 => 1, 65 => 1, 197 => 1],
  sparse![198; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 10 => -1, 21 => 1, 32 => 3, 65 => -1],
  sparse![198; 2 => -1, 5 => 1, 8 => 3, 17 => -1, 32 => -1, 65 => 1, 98 => 3, 197 => -1],
  sparse![198; 0 => 1, 8 => 1, 10 => 1, 98 => 1],
  sparse![198; 1 => 1, 17 => 1, 21 => 1, 197 => 1],
  sparse![198; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 10 => -1, 17 => 1, 21 => 2, 32 => 1, 65 => -1, 197 => 1],
  sparse![198; 0 => 1, 2 => -1, 5 => 1, 8 => 2, 10 => 1, 17 => -1, 32 => -1, 65 => 1, 98 => 2, 197 => -1],
  sparse![198; 2 => 1, 5 => -1, 8 => -1, 10 => -1, 17 => 3, 21 => 2, 32 => 1, 65 => -1, 197 => 1],
  sparse![198; 2 => -1, 5 => 1, 8 => 3, 10 => 2, 17 => -1, 21 => -1, 32 => -1, 65 => 1, 98 => 1],
  sparse![198; 0 => -1, 1 => 3, 2 => 1, 5 => -1, 21 => 1, 32 => 1, 65 => -1, 98 => -1, 197 => 2],
  sparse![198; 0 => 2, 1 => -1, 2 => -1, 5 => 1, 8 => 1, 10 => 2, 21 => -1, 32 => -1, 65 => 1, 98 => 1],
  sparse![198; 0 => -2, 1 => 1, 2 => 6, 5 => -2, 8 => -2, 10 => 2, 17 => 1, 21 => -1, 32 => -2, 65 => 2, 98 => 2, 197 => -1],
  sparse![198; 0 => -2, 1 => 2, 2 => 5, 5 => -3, 8 => -2, 10 => 1, 17 => 2, 21 => -1, 32 => -1, 65 => 3, 98 => 1, 197 => -1],
  sparse![198; 0 => -2, 1 => 3, 2 => 2, 5 => -1, 10 => 1, 32 => 1],
  sparse![198; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 8 => -1, 10 => -1, 17 => 1, 21 => 1, 32 => 2, 65 => -1, 98 => 1],
  sparse![198; 0 => -1, 2 => 3, 5 => 1, 8 => -1, 21 => 1, 32 => 1, 65 => -1, 197 => 1],
  sparse![198; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 8 => -1, 10 => 2, 17 => 1, 21 => -2, 32 => -3, 65 => 5, 98 => 2, 197 => -2],
  sparse![198; 0 => -1, 1 => 2, 5 => 1, 8 => 1, 17 => -1, 65 => 1, 197 => 1],
  sparse![198; 0 => -1, 1 => 2, 2 => 1, 65 => 1, 98 => 2, 197 => -1],
]
```

### Level 199

dim S₂ = **16**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **33**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 200

dim S₂ = **19**; eta rank = **19**; full eta basis = **YES**; Sturm bound B = **60**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![200; 1 => 2, 9 => 2],
  sparse![200; 3 => 2, 19 => 2],
  sparse![200; 9 => 2, 49 => 2],
  sparse![200; 19 => 2, 99 => 2],
  sparse![200; 0 => -2, 1 => 5, 3 => -1, 4 => 2, 9 => -1, 19 => 1],
  sparse![200; 4 => -2, 9 => 5, 19 => -1, 24 => 2, 49 => -1, 99 => 1],
  sparse![200; 1 => 1, 9 => 2, 49 => 1],
  sparse![200; 0 => -1, 1 => 2, 3 => -1, 4 => 2, 19 => 2, 24 => -1, 49 => 2, 99 => -1],
  sparse![200; 0 => -1, 1 => 2, 9 => 2, 24 => 1],
  sparse![200; 0 => -1, 1 => 3, 3 => -1, 9 => 2, 24 => 1, 49 => -1, 99 => 1],
  sparse![200; 1 => -1, 3 => 1, 9 => 6, 19 => -2, 49 => -1, 99 => 1],
  sparse![200; 3 => 1, 19 => 2, 99 => 1],
  sparse![200; 1 => -1, 3 => 2, 7 => -1, 9 => 2, 39 => 2, 49 => -1, 99 => 2, 199 => -1],
  sparse![200; 1 => -1, 3 => 2, 19 => 2, 49 => 1],
  sparse![200; 1 => 1, 4 => 1, 24 => -1, 39 => 1, 49 => 1, 99 => 2, 199 => -1],
  sparse![200; 0 => -1, 1 => 2, 3 => 1, 4 => 1, 7 => -1, 39 => 1, 99 => 1],
  sparse![200; 3 => 1, 4 => 1, 24 => -1, 39 => 1, 49 => 2, 99 => 1, 199 => -1],
  sparse![200; 0 => -1, 1 => 2, 3 => -1, 9 => 3, 19 => 1, 24 => 1, 49 => -1],
  sparse![200; 0 => -1, 1 => 2, 4 => 1, 9 => -1, 19 => 3, 39 => -1, 49 => 1, 99 => -1, 199 => 1],
]
```

### Level 201

dim S₂ = **21**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **45**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 202

dim S₂ = **24**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **51**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 203

dim S₂ = **19**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **40**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![203; 0 => 2, 202 => 2],
  sparse![203; 0 => 1, 6 => 1, 28 => 1, 202 => 1],
  sparse![203; 6 => 2, 28 => 2],
]
```

### Level 204

dim S₂ = **31**; eta rank = **31**; full eta basis = **YES**; Sturm bound B = **72**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![204; 0 => 1, 2 => 1, 16 => 1, 50 => 1],
  sparse![204; 1 => 1, 5 => 1, 33 => 1, 101 => 1],
  sparse![204; 3 => 1, 11 => 1, 67 => 1, 203 => 1],
  sparse![204; 0 => 2, 1 => -1, 3 => 1, 16 => -2, 33 => 5, 67 => -1],
  sparse![204; 0 => 1, 1 => -1, 3 => 2, 16 => -1, 33 => 5, 67 => -2],
  sparse![204; 0 => 1, 1 => 2, 3 => -1, 16 => -1, 33 => 2, 67 => 1],
  sparse![204; 1 => 2, 33 => 2],
  sparse![204; 0 => -1, 1 => 2, 3 => 1, 16 => 1, 33 => 2, 67 => -1],
  sparse![204; 0 => -1, 1 => 5, 3 => -2, 16 => 1, 33 => -1, 67 => 2],
  sparse![204; 0 => -2, 1 => 5, 3 => -1, 16 => 2, 33 => -1, 67 => 1],
  sparse![204; 2 => 2, 5 => -1, 11 => 1, 50 => -2, 101 => 5, 203 => -1],
  sparse![204; 2 => 1, 5 => -1, 11 => 2, 50 => -1, 101 => 5, 203 => -2],
  sparse![204; 2 => 1, 5 => 2, 11 => -1, 50 => -1, 101 => 2, 203 => 1],
  sparse![204; 5 => 2, 101 => 2],
  sparse![204; 2 => -1, 5 => 2, 11 => 1, 50 => 1, 101 => 2, 203 => -1],
  sparse![204; 2 => -1, 5 => 5, 11 => -2, 50 => 1, 101 => -1, 203 => 2],
  sparse![204; 2 => -2, 5 => 5, 11 => -1, 50 => 2, 101 => -1, 203 => 1],
  sparse![204; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 16 => 1, 101 => 1],
  sparse![204; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 33 => 1, 50 => 1],
  sparse![204; 1 => 2, 2 => 1, 5 => -1, 16 => -1, 33 => 1, 50 => 2],
  sparse![204; 0 => 2, 2 => -1, 5 => 1, 16 => 1, 33 => -1, 101 => 2],
  sparse![204; 0 => -1, 1 => 3, 2 => 1, 5 => -1, 16 => 1, 33 => -1, 50 => -1, 101 => 3],
  sparse![204; 0 => 3, 1 => -1, 2 => -1, 5 => 1, 16 => -1, 33 => 1, 50 => 3, 101 => -1],
  sparse![204; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 16 => 3, 33 => -1, 50 => -1, 101 => 1],
  sparse![204; 1 => -2, 3 => 3, 5 => 3, 11 => -2, 33 => 1, 203 => 1],
  sparse![204; 1 => 3, 3 => -2, 5 => -2, 11 => 3, 67 => 1, 101 => 1],
  sparse![204; 3 => 2, 5 => 1, 11 => -1, 33 => -1, 67 => 1, 101 => 2],
  sparse![204; 1 => 2, 5 => -1, 11 => 1, 33 => 1, 67 => -1, 203 => 2],
  sparse![204; 1 => 3, 3 => -1, 5 => -1, 11 => 1, 33 => -1, 67 => 1, 101 => 3, 203 => -1],
  sparse![204; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 5 => -3, 11 => 1, 16 => -1, 33 => 3, 50 => 1, 67 => -1],
  sparse![204; 0 => -3, 1 => 8, 2 => 1, 3 => -3, 5 => -2, 11 => 1, 16 => -3, 33 => 8, 50 => 1, 67 => -3, 101 => -2, 203 => 1],
]
```

### Level 205

dim S₂ = **19**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **42**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 206

dim S₂ = **25**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **52**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![206; 0 => 1, 1 => 1, 102 => 1, 205 => 1],
]
```

### Level 207

dim S₂ = **21**; eta rank = **7**; full eta basis = **NO**; Sturm bound B = **48**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![207; 0 => 2, 22 => 2],
  sparse![207; 2 => 2, 68 => 2],
  sparse![207; 8 => 2, 206 => 2],
  sparse![207; 0 => 1, 2 => 1, 22 => 1, 68 => 1],
  sparse![207; 2 => 1, 8 => 1, 68 => 1, 206 => 1],
  sparse![207; 0 => 1, 8 => 1, 22 => 1, 206 => 1],
  sparse![207; 0 => -1, 2 => 4, 8 => -1, 22 => -1, 68 => 4, 206 => -1],
]
```

### Level 208

dim S₂ = **23**; eta rank = **23**; full eta basis = **YES**; Sturm bound B = **56**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![208; 0 => 1, 3 => 2, 7 => -1, 12 => -1, 25 => 2, 103 => 1],
  sparse![208; 0 => -1, 1 => 1, 3 => 3, 7 => -1, 12 => 1, 25 => 1, 51 => -1, 103 => 1],
  sparse![208; 0 => -1, 1 => 2, 7 => 1, 12 => 1, 51 => 2, 103 => -1],
  sparse![208; 0 => -1, 1 => 2, 3 => 2, 7 => -1, 12 => 1, 103 => 1],
  sparse![208; 0 => -1, 1 => 3, 3 => -1, 7 => 1, 12 => 1, 25 => -1, 51 => 3, 103 => -1],
  sparse![208; 0 => -1, 1 => 3, 3 => 1, 7 => -1, 12 => 1, 25 => -1, 51 => 1, 103 => 1],
  sparse![208; 0 => -1, 1 => 4, 3 => -2, 7 => 1, 12 => 1, 25 => -2, 51 => 4, 103 => -1],
  sparse![208; 0 => 1, 1 => -2, 3 => 4, 7 => -1, 12 => -1, 25 => 4, 51 => -2, 103 => 1],
  sparse![208; 0 => 1, 1 => -1, 3 => 1, 7 => 1, 12 => -1, 25 => 3, 51 => 1, 103 => -1],
  sparse![208; 0 => 1, 1 => -1, 3 => 3, 7 => -1, 12 => -1, 25 => 3, 51 => -1, 103 => 1],
  sparse![208; 0 => 1, 7 => 1, 12 => -1, 25 => 2, 51 => 2, 103 => -1],
  sparse![208; 1 => 1, 7 => 2, 15 => -1, 25 => -1, 51 => 2, 207 => 1],
  sparse![208; 1 => -1, 3 => 1, 7 => 3, 15 => -1, 25 => 1, 51 => 1, 103 => -1, 207 => 1],
  sparse![208; 1 => -1, 3 => 2, 7 => 2, 15 => -1, 25 => 1, 207 => 1],
  sparse![208; 1 => -1, 3 => 3, 7 => 1, 15 => -1, 25 => 1, 51 => -1, 103 => 1, 207 => 1],
  sparse![208; 1 => 1, 3 => -2, 7 => 4, 15 => -1, 25 => -1, 51 => 4, 103 => -2, 207 => 1],
  sparse![208; 1 => 1, 3 => -1, 7 => 3, 15 => -1, 25 => -1, 51 => 3, 103 => -1, 207 => 1],
  sparse![208; 0 => -1, 1 => 1, 3 => 2, 12 => 1, 25 => 1],
  sparse![208; 0 => -1, 1 => 2, 3 => 1, 12 => 1, 51 => 1],
  sparse![208; 0 => -1, 1 => 3, 12 => 1, 25 => -1, 51 => 2],
  sparse![208; 0 => -1, 1 => 4, 3 => -1, 12 => 1, 25 => -2, 51 => 3],
  sparse![208; 3 => -1, 7 => 4, 15 => -1, 51 => 3, 103 => -2, 207 => 1],
  sparse![208; 3 => 2, 7 => 1, 15 => -1, 103 => 1, 207 => 1],
]
```

### Level 209

dim S₂ = **19**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **40**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![209; 0 => 2, 10 => 2],
  sparse![209; 18 => 2, 208 => 2],
  sparse![209; 0 => 1, 10 => 1, 18 => 1, 208 => 1],
]
```

### Level 210

dim S₂ = **41**; eta rank = **41**; full eta basis = **YES**; Sturm bound B = **96**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![210; 0 => -3, 1 => 4, 2 => 4, 4 => 1, 5 => -3, 6 => 2, 9 => -1, 13 => -1, 14 => -1, 20 => -1, 29 => 1, 41 => 2],
  sparse![210; 0 => -3, 1 => 5, 2 => 2, 4 => 2, 5 => -2, 6 => 2, 9 => -2, 13 => -2, 14 => -1, 20 => -1, 29 => 1, 34 => -3, 41 => 1, 69 => 5, 104 => 2, 209 => -2],
  sparse![210; 0 => -2, 1 => 1, 2 => 4, 4 => 4, 5 => -2, 6 => 1, 9 => -2, 14 => -2, 20 => -1, 29 => 1, 34 => -1, 41 => 1, 69 => 1, 104 => 1],
  sparse![210; 0 => -2, 1 => 2, 2 => 1, 4 => 5, 5 => -1, 6 => 5, 9 => -3, 13 => -3, 14 => -2, 20 => -2, 29 => 2, 34 => -2, 41 => 2, 69 => 2, 104 => 1, 209 => -1],
  sparse![210; 0 => -2, 1 => 2, 2 => 3, 4 => 3, 5 => -2, 6 => 1, 9 => -2, 13 => -1, 14 => -2, 29 => 2, 41 => 1, 69 => 1, 104 => 1, 209 => -1],
  sparse![210; 0 => -2, 1 => 2, 2 => 3, 4 => 3, 5 => -2, 6 => 1, 9 => -2, 14 => -2, 20 => -1, 29 => 2, 34 => -1, 41 => 1, 69 => 1, 104 => 1],
  sparse![210; 0 => -2, 1 => 2, 2 => 5, 4 => 1, 5 => -3, 6 => 1, 9 => -1, 13 => -1, 14 => -2, 20 => -2, 29 => 2, 34 => -2, 41 => 2, 69 => 2, 104 => 5, 209 => -3],
  sparse![210; 0 => -2, 1 => 3, 2 => 1, 4 => 2, 5 => -1, 6 => 2, 9 => -1, 13 => -1, 14 => -1, 20 => -1, 29 => 1, 34 => -2, 41 => 1, 69 => 3, 104 => 1, 209 => -1],
  sparse![210; 0 => -2, 1 => 3, 2 => 1, 4 => 2, 5 => -1, 6 => 3, 9 => -1, 13 => -2, 20 => -1, 34 => -1, 41 => 1, 69 => 2],
  sparse![210; 0 => -2, 1 => 3, 2 => 2, 4 => 1, 5 => -1, 9 => -1, 69 => 1, 104 => -1, 209 => 2],
  sparse![210; 0 => -2, 1 => 3, 2 => 2, 4 => 1, 5 => -1, 6 => 1, 9 => -1, 13 => -1, 14 => -1, 20 => -1, 29 => 1, 34 => -2, 41 => 1, 69 => 3, 104 => 2, 209 => -1],
  sparse![210; 0 => -2, 1 => 3, 2 => 2, 4 => 2, 5 => -2, 6 => 1, 9 => -2, 13 => -1, 14 => -2, 29 => 3, 41 => 1, 69 => 1, 104 => 1, 209 => -1],
  sparse![210; 0 => -2, 1 => 3, 2 => 2, 4 => 2, 5 => -2, 6 => 1, 9 => -2, 14 => -2, 20 => -1, 29 => 3, 34 => -1, 41 => 1, 69 => 1, 104 => 1],
  sparse![210; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 6 => 1, 13 => -1, 20 => -1, 34 => -1, 41 => 1, 69 => 2, 104 => 2, 209 => -1],
  sparse![210; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 6 => 4, 13 => -2, 20 => -1, 41 => 1],
  sparse![210; 0 => -2, 1 => 4, 2 => 1, 4 => 1, 5 => -2, 6 => 1, 9 => -2, 13 => -1, 14 => -2, 29 => 4, 41 => 1, 69 => 1, 104 => 1, 209 => -1],
  sparse![210; 0 => -1, 4 => 4, 5 => 1, 6 => 4, 9 => -1, 13 => -1, 14 => -1, 20 => -1, 34 => -1, 209 => 1],
  sparse![210; 0 => -1, 2 => 1, 4 => 3, 6 => 3, 14 => -1, 20 => -1, 34 => -1, 104 => 1],
  sparse![210; 0 => -1, 2 => 1, 4 => 3, 5 => 1, 6 => 1, 9 => -1, 14 => -1, 20 => 1, 34 => 1, 41 => -1, 69 => -1, 104 => -1, 209 => 2],
  sparse![210; 0 => -1, 2 => 1, 4 => 3, 5 => 1, 6 => 1, 9 => -1, 13 => 1, 14 => -1, 41 => -1, 69 => -1, 104 => -1, 209 => 3],
  sparse![210; 0 => -1, 2 => 2, 4 => 2, 13 => 1, 14 => -1, 20 => 1, 34 => 1, 41 => -1, 69 => -1, 209 => 1],
  sparse![210; 0 => -1, 2 => 3, 4 => -1, 5 => -1, 6 => 2, 9 => 3, 13 => -1, 29 => -1, 104 => -1, 209 => 2],
  sparse![210; 0 => -1, 2 => 3, 4 => 1, 5 => -1, 6 => -1, 9 => 1, 13 => 2, 14 => -1, 20 => 1, 34 => 1, 41 => -1, 69 => -1, 104 => 1],
  sparse![210; 0 => -1, 2 => 3, 4 => 1, 5 => -1, 6 => -1, 9 => 1, 13 => 3, 14 => -1, 41 => -1, 69 => -1, 104 => 1, 209 => 1],
  sparse![210; 0 => -1, 2 => 3, 4 => 1, 6 => 1, 14 => -1, 20 => -1, 34 => -1, 104 => 3],
  sparse![210; 0 => -1, 2 => 4, 5 => -1, 9 => 1, 13 => 1, 14 => -1, 20 => -1, 34 => -1, 104 => 4, 209 => -1],
  sparse![210; 0 => -1, 1 => 1, 4 => 1, 5 => 1, 6 => 2, 13 => -1, 14 => 1, 29 => -1, 104 => -1, 209 => 2],
  sparse![210; 0 => -1, 1 => 1, 4 => 2, 6 => 2, 9 => -1, 13 => -1, 14 => 1, 20 => 1, 34 => -1, 69 => 1],
  sparse![210; 0 => -1, 1 => 1, 4 => 2, 5 => 1, 6 => 1, 9 => -1, 14 => -1, 20 => 1, 29 => 1, 34 => 1, 41 => -1, 69 => -1, 104 => -1, 209 => 2],
  sparse![210; 0 => -1, 1 => 1, 4 => 2, 5 => 1, 6 => 1, 9 => -1, 13 => 1, 14 => -1, 29 => 1, 41 => -1, 69 => -1, 104 => -1, 209 => 3],
  sparse![210; 0 => -1, 1 => 1, 4 => 3, 6 => 1, 9 => -2, 14 => -1, 20 => 2, 29 => 2, 41 => -1],
  sparse![210; 0 => -1, 1 => 1, 4 => 3, 6 => 3, 9 => -1, 13 => -1, 34 => -1, 69 => 1],
  sparse![210; 0 => -1, 1 => 1, 2 => 1, 6 => 1, 9 => 1, 14 => 1, 29 => -1, 209 => 1],
  sparse![210; 0 => -1, 1 => 1, 2 => 1, 4 => 1, 5 => -1, 6 => 2, 13 => -1, 20 => -1, 29 => 1, 41 => 2],
  sparse![210; 0 => -1, 1 => 1, 2 => 1, 4 => 1, 14 => -1, 20 => 2, 29 => 1, 34 => 2, 41 => -1, 69 => -1],
  sparse![210; 0 => -1, 1 => 1, 2 => 1, 4 => 1, 6 => 2, 13 => -1, 20 => -1, 41 => 1, 209 => 1],
  sparse![210; 0 => -1, 1 => 1, 2 => 1, 4 => 2, 5 => -1, 6 => 2, 9 => -1, 13 => -1, 14 => -2, 20 => -2, 29 => 3, 34 => -1, 41 => 3, 69 => 1, 104 => 1, 209 => -1],
  sparse![210; 0 => -1, 1 => 1, 2 => 1, 4 => 2, 5 => -1, 6 => 3, 9 => -1, 13 => -2, 14 => -1, 20 => -2, 29 => 2, 41 => 3],
  sparse![210; 0 => -1, 1 => 1, 2 => 1, 4 => 2, 6 => -1, 9 => -1, 13 => 1, 14 => -1, 20 => 2, 29 => 1, 41 => -1, 69 => 1],
  sparse![210; 0 => -1, 1 => 1, 2 => 1, 4 => 2, 9 => -1, 20 => 2, 34 => 1, 41 => -1, 104 => -1, 209 => 1],
  sparse![210; 0 => -1, 1 => 1, 2 => 1, 4 => 2, 9 => -1, 13 => 1, 20 => 1, 41 => -1, 104 => -1, 209 => 2],
]
```

### Level 211

dim S₂ = **17**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **35**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 212

dim S₂ = **25**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **54**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![212; 1 => 2, 105 => 2],
]
```

### Level 213

dim S₂ = **23**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **48**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![213; 0 => 2, 70 => 2],
  sparse![213; 2 => 2, 212 => 2],
  sparse![213; 0 => 1, 2 => 1, 70 => 1, 212 => 1],
]
```

### Level 214

dim S₂ = **26**; eta rank = **2**; full eta basis = **NO**; Sturm bound B = **54**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![214; 0 => 2, 106 => 2],
  sparse![214; 1 => 2, 213 => 2],
]
```

### Level 215

dim S₂ = **21**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **44**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![215; 0 => 2, 214 => 2],
  sparse![215; 0 => 1, 4 => 1, 42 => 1, 214 => 1],
  sparse![215; 4 => 2, 42 => 2],
]
```

### Level 216

dim S₂ = **25**; eta rank = **25**; full eta basis = **YES**; Sturm bound B = **72**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![216; 0 => -6, 1 => 13, 2 => 5, 3 => -5, 5 => -6, 8 => -1, 11 => 3, 17 => 1],
  sparse![216; 0 => -6, 1 => 15, 2 => 2, 3 => -6, 5 => -5, 11 => 3, 35 => 1],
  sparse![216; 0 => -6, 1 => 15, 2 => 2, 3 => -6, 5 => -4, 11 => 2, 17 => 1],
  sparse![216; 0 => -4, 1 => 6, 2 => 7, 3 => -2, 5 => -5, 8 => -1, 11 => 2, 17 => 1],
  sparse![216; 0 => -4, 1 => 8, 2 => 4, 3 => -3, 5 => -4, 11 => 2, 35 => 1],
  sparse![216; 0 => -4, 1 => 8, 2 => 4, 3 => -3, 5 => -3, 11 => 1, 17 => 1],
  sparse![216; 0 => -4, 1 => 9, 2 => 1, 3 => -2, 5 => -3, 8 => 1, 11 => 2],
  sparse![216; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 8 => 1, 11 => 1, 35 => 1],
  sparse![216; 0 => -3, 1 => 1, 2 => 10, 3 => 1, 5 => -5, 8 => -3, 11 => 1, 17 => 2],
  sparse![216; 0 => -3, 1 => 3, 2 => 7, 5 => -4, 8 => -2, 11 => 1, 17 => 1, 35 => 1],
  sparse![216; 0 => -3, 1 => 3, 2 => 7, 5 => -3, 8 => -2, 17 => 2],
  sparse![216; 0 => -3, 1 => 5, 2 => 1, 3 => 3, 7 => -2, 11 => -2, 17 => -1, 23 => 1, 35 => 3, 71 => -1],
  sparse![216; 0 => -3, 1 => 5, 2 => 4, 3 => -1, 5 => -2, 8 => -1, 17 => 1, 35 => 1],
  sparse![216; 0 => -3, 1 => 6, 2 => 2, 3 => -1, 5 => -1, 7 => -1, 8 => 1, 11 => -1, 17 => -1, 23 => 2, 35 => 2, 71 => -1],
  sparse![216; 0 => -3, 1 => 6, 2 => 3, 3 => -1, 5 => -4, 7 => -1, 8 => -2, 11 => 1, 17 => 4, 23 => 2, 71 => -1],
  sparse![216; 0 => -3, 1 => 7, 2 => -1, 3 => -2, 5 => 1, 8 => 4, 17 => -3, 26 => -2, 35 => 1, 53 => 3, 107 => -1],
  sparse![216; 0 => -2, 1 => 1, 2 => 4, 3 => 4, 5 => -1, 7 => -2, 8 => -2, 11 => -2, 17 => 2, 23 => 1, 35 => 2, 71 => -1],
  sparse![216; 0 => -2, 1 => 1, 2 => 5, 3 => 2, 5 => -4, 7 => -1, 8 => -1, 11 => 4, 17 => 1, 23 => -1],
  sparse![216; 0 => -2, 1 => 1, 2 => 5, 3 => 2, 5 => -2, 7 => -1, 8 => -1, 11 => -1, 23 => 1, 35 => 2, 53 => 1, 71 => -1, 107 => -1, 215 => 1],
  sparse![216; 0 => -2, 1 => 1, 2 => 6, 5 => -2, 17 => 1],
  sparse![216; 0 => -2, 1 => 3, 2 => 2, 3 => -1, 8 => 2, 26 => -2, 53 => 3, 107 => -1],
  sparse![216; 0 => -2, 1 => 3, 2 => 2, 3 => 1, 5 => -3, 7 => -1, 11 => 4, 23 => -1, 35 => 1],
  sparse![216; 0 => -2, 1 => 5, 2 => -2, 3 => -2, 5 => 2, 8 => 6, 17 => -4, 26 => -2, 35 => 1, 53 => 3, 107 => -1],
  sparse![216; 0 => -1, 2 => 1, 3 => 1, 5 => 2, 8 => 4, 11 => -1, 17 => -3, 26 => -2, 35 => 1, 53 => 3, 107 => -1],
  sparse![216; 0 => -1, 1 => 1, 3 => 1, 5 => 2, 7 => -1, 8 => 3, 11 => -2, 17 => -2, 23 => 2, 26 => -2, 35 => 2, 53 => 3, 71 => -1, 107 => -1],
]
```

### Level 217

dim S₂ = **19**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **42**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 218

dim S₂ = **26**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **55**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 219

dim S₂ = **23**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **49**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 220

dim S₂ = **31**; eta rank = **31**; full eta basis = **YES**; Sturm bound B = **72**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![220; 0 => 2, 10 => 2],
  sparse![220; 1 => 2, 21 => 2],
  sparse![220; 3 => 2, 43 => 2],
  sparse![220; 4 => 2, 54 => 2],
  sparse![220; 9 => 2, 109 => 2],
  sparse![220; 19 => 2, 219 => 2],
  sparse![220; 1 => 2, 9 => 2],
  sparse![220; 21 => 2, 109 => 2],
  sparse![220; 0 => 1, 4 => 1, 10 => 1, 54 => 1],
  sparse![220; 1 => 1, 9 => 1, 21 => 1, 109 => 1],
  sparse![220; 3 => 1, 19 => 1, 43 => 1, 219 => 1],
  sparse![220; 0 => 2, 1 => -1, 4 => -1, 9 => 2, 10 => -1, 21 => 2, 54 => 2, 109 => -1],
  sparse![220; 0 => -1, 1 => 2, 9 => 1, 10 => 1, 54 => 2, 109 => -1],
  sparse![220; 1 => 1, 4 => -1, 9 => 2, 10 => 2, 21 => -1, 54 => 1],
  sparse![220; 0 => -1, 1 => 2, 4 => 1, 10 => -1, 21 => 2, 54 => 1],
  sparse![220; 0 => 1, 4 => -1, 9 => 2, 10 => 1, 54 => -1, 109 => 2],
  sparse![220; 0 => 1, 1 => 1, 54 => 1, 109 => 1],
  sparse![220; 4 => 1, 9 => 1, 10 => 1, 21 => 1],
  sparse![220; 0 => 1, 1 => -1, 4 => -1, 9 => 3, 10 => -1, 21 => 3, 54 => 1, 109 => -1],
  sparse![220; 0 => 3, 1 => -1, 4 => -1, 9 => 1, 10 => -1, 21 => 1, 54 => 3, 109 => -1],
  sparse![220; 1 => 2, 3 => -1, 9 => -1, 19 => 2, 21 => -1, 43 => 2, 109 => 2, 219 => -1],
  sparse![220; 1 => -1, 3 => 2, 19 => 1, 21 => 1, 109 => 2, 219 => -1],
  sparse![220; 3 => 1, 9 => -1, 19 => 2, 21 => 2, 43 => -1, 109 => 1],
  sparse![220; 1 => -1, 3 => 2, 9 => 1, 21 => -1, 43 => 2, 109 => 1],
  sparse![220; 1 => 1, 9 => -1, 19 => 2, 21 => 1, 109 => -1, 219 => 2],
  sparse![220; 1 => 1, 3 => 1, 109 => 1, 219 => 1],
  sparse![220; 9 => 1, 19 => 1, 21 => 1, 43 => 1],
  sparse![220; 0 => 1, 1 => 1, 3 => -1, 9 => -1, 19 => 2, 21 => 1, 54 => 1, 109 => -1, 219 => 1],
  sparse![220; 0 => 1, 19 => 1, 43 => 1, 54 => 1],
  sparse![220; 0 => -2, 1 => 4, 3 => -1, 4 => 2, 9 => -2, 10 => 2, 19 => 1, 21 => -2, 43 => 1, 54 => -2, 109 => 4, 219 => -1],
  sparse![220; 0 => -2, 1 => 5, 3 => -2, 9 => -1, 10 => 1, 19 => 2, 54 => 1],
]
```

### Level 221

dim S₂ = **19**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **42**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 222

dim S₂ = **35**; eta rank = **14**; full eta basis = **NO**; Sturm bound B = **76**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![222; 0 => 1, 2 => 2, 5 => -1, 73 => 1, 110 => -1, 221 => 2],
  sparse![222; 0 => 2, 1 => -1, 2 => 1, 36 => -1, 73 => 2, 221 => 1],
  sparse![222; 1 => 2, 2 => 1, 5 => -1, 36 => 1, 73 => -1, 221 => 2],
  sparse![222; 0 => 1, 1 => 1, 110 => 1, 221 => 1],
  sparse![222; 0 => 2, 2 => -1, 5 => 1, 36 => -1, 73 => 1, 110 => 2],
  sparse![222; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 36 => 3, 73 => -2, 110 => -2, 221 => 3],
  sparse![222; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 36 => 2, 73 => -1, 110 => -1, 221 => 2],
  sparse![222; 1 => 1, 2 => 1, 36 => 1, 221 => 1],
  sparse![222; 0 => 1, 5 => 1, 73 => 1, 110 => 1],
  sparse![222; 0 => 2, 1 => -1, 2 => -1, 5 => 2, 36 => -1, 73 => 2, 110 => 2, 221 => -1],
  sparse![222; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 36 => -2, 73 => 3, 110 => 3, 221 => -2],
  sparse![222; 0 => -1, 1 => 1, 2 => 2, 36 => 2, 110 => -1, 221 => 1],
  sparse![222; 2 => 1, 5 => 1, 36 => 1, 73 => 1],
  sparse![222; 0 => 1, 1 => -1, 5 => 2, 73 => 2, 110 => 1, 221 => -1],
]
```

### Level 223

dim S₂ = **18**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **37**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 224

dim S₂ = **25**; eta rank = **25**; full eta basis = **YES**; Sturm bound B = **64**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![224; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![224; 1 => 1, 3 => 1, 13 => 1, 27 => 1],
  sparse![224; 3 => 1, 7 => 1, 27 => 1, 55 => 1],
  sparse![224; 7 => 1, 15 => 1, 55 => 1, 111 => 1],
  sparse![224; 15 => 1, 31 => 1, 111 => 1, 223 => 1],
  sparse![224; 3 => 2, 7 => 2],
  sparse![224; 27 => 2, 55 => 2],
  sparse![224; 0 => 1, 6 => 1, 7 => 1, 55 => 1],
  sparse![224; 1 => -1, 3 => 3, 13 => 3, 27 => -1],
  sparse![224; 1 => 1, 13 => 1, 15 => 1, 111 => 1],
  sparse![224; 3 => -1, 7 => 3, 27 => 3, 55 => -1],
  sparse![224; 3 => 1, 27 => 1, 31 => 1, 223 => 1],
  sparse![224; 7 => -1, 15 => 3, 55 => 3, 111 => -1],
  sparse![224; 0 => -3, 1 => 7, 3 => -2, 6 => 1, 13 => 1],
  sparse![224; 0 => -2, 1 => 4, 6 => 2, 13 => -2, 27 => 2],
  sparse![224; 0 => -2, 1 => 5, 3 => -2, 7 => 2, 15 => -1, 55 => 1, 111 => 1],
  sparse![224; 1 => -3, 3 => 7, 7 => -2, 13 => 1, 27 => 1],
  sparse![224; 1 => -2, 3 => 4, 13 => 2, 27 => -2, 55 => 2],
  sparse![224; 1 => -2, 3 => 5, 7 => -2, 15 => 2, 31 => -1, 111 => 1, 223 => 1],
  sparse![224; 0 => -1, 3 => 5, 6 => 1, 7 => -2, 13 => -1, 27 => 1, 55 => -1, 111 => 2],
  sparse![224; 0 => 1, 1 => -1, 3 => 1, 6 => -1, 7 => -1, 15 => 2, 27 => 5, 55 => -2],
  sparse![224; 3 => -2, 7 => 5, 13 => 2, 27 => -1, 31 => -1, 55 => 1, 111 => -1, 223 => 1],
  sparse![224; 0 => 1, 6 => 1, 31 => 1, 223 => 1],
  sparse![224; 3 => 2, 55 => 2],
  sparse![224; 0 => -3, 1 => 7, 3 => -2, 6 => 1, 13 => -3, 27 => 6, 55 => -2],
]
```

### Level 225

dim S₂ = **19**; eta rank = **12**; full eta basis = **NO**; Sturm bound B = **60**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![225; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![225; 2 => 1, 8 => 1, 14 => 1, 44 => 1],
  sparse![225; 4 => 1, 14 => 1, 24 => 1, 74 => 1],
  sparse![225; 14 => 1, 44 => 1, 74 => 1, 224 => 1],
  sparse![225; 0 => 1, 4 => 1, 14 => 1, 74 => 1],
  sparse![225; 2 => 1, 4 => 1, 14 => 1, 24 => 1],
  sparse![225; 2 => 1, 14 => 1, 44 => 1, 224 => 1],
  sparse![225; 8 => 1, 14 => 1, 44 => 1, 74 => 1],
  sparse![225; 0 => -1, 2 => 1, 4 => 4, 24 => -1, 74 => 1],
  sparse![225; 2 => 1, 8 => -1, 44 => 4, 74 => 1, 224 => -1],
  sparse![225; 0 => 1, 2 => -1, 4 => -1, 8 => 1, 14 => 4, 24 => 1, 44 => -1, 74 => -1, 224 => 1],
  sparse![225; 0 => -1, 2 => 3, 4 => 1, 8 => -1, 24 => -1, 44 => 1, 74 => 3, 224 => -1],
]
```

### Level 226

dim S₂ = **27**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **57**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 227

dim S₂ = **19**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **38**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![227; 0 => 2, 226 => 2],
]
```

### Level 228

dim S₂ = **35**; eta rank = **35**; full eta basis = **YES**; Sturm bound B = **80**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![228; 0 => 3, 1 => -1, 18 => -1, 37 => 3],
  sparse![228; 0 => -1, 1 => 3, 18 => 3, 37 => -1],
  sparse![228; 1 => 3, 3 => -1, 37 => -1, 75 => 3],
  sparse![228; 1 => -1, 3 => 3, 37 => 3, 75 => -1],
  sparse![228; 2 => 3, 5 => -1, 56 => -1, 113 => 3],
  sparse![228; 2 => -1, 5 => 3, 56 => 3, 113 => -1],
  sparse![228; 5 => 3, 11 => -1, 113 => -1, 227 => 3],
  sparse![228; 5 => -1, 11 => 3, 113 => 3, 227 => -1],
  sparse![228; 0 => 1, 3 => 1, 18 => -3, 37 => 8, 75 => -3],
  sparse![228; 2 => 1, 11 => 1, 56 => -3, 113 => 8, 227 => -3],
  sparse![228; 1 => 1, 2 => 2, 5 => -1, 18 => 1, 56 => -1, 113 => 2],
  sparse![228; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 18 => 1, 113 => 1],
  sparse![228; 0 => 2, 1 => -1, 5 => 1, 18 => -1, 37 => 2, 56 => 1],
  sparse![228; 0 => -1, 1 => 2, 2 => 1, 18 => 2, 37 => -1, 113 => 1],
  sparse![228; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 37 => 1, 56 => 1],
  sparse![228; 0 => -1, 1 => 1, 2 => 2, 18 => 1, 37 => -1, 113 => 2],
  sparse![228; 1 => 1, 2 => 1, 18 => -2, 37 => 3, 56 => 3, 113 => -2],
  sparse![228; 1 => 2, 2 => 1, 5 => -1, 18 => 2, 56 => -1, 113 => 1],
  sparse![228; 0 => 1, 2 => -1, 5 => 2, 37 => 1, 56 => 2, 113 => -1],
  sparse![228; 3 => 1, 5 => 2, 11 => -1, 37 => 1, 113 => -1, 227 => 2],
  sparse![228; 1 => 3, 3 => -2, 5 => -2, 11 => 3, 37 => 1, 227 => 1],
  sparse![228; 1 => 2, 3 => -1, 11 => 1, 37 => -1, 75 => 2, 113 => 1],
  sparse![228; 1 => -1, 3 => 2, 5 => 1, 37 => 2, 75 => -1, 227 => 1],
  sparse![228; 1 => -2, 3 => 3, 5 => 3, 11 => -2, 75 => 1, 113 => 1],
  sparse![228; 1 => -1, 3 => 1, 5 => 2, 37 => 1, 75 => -1, 227 => 2],
  sparse![228; 3 => 1, 5 => 1, 37 => -2, 75 => 3, 113 => 3, 227 => -2],
  sparse![228; 3 => 2, 5 => 1, 11 => -1, 37 => 2, 113 => -1, 227 => 1],
  sparse![228; 0 => 3, 1 => -1, 2 => -1, 11 => 1, 37 => 3, 75 => -1],
  sparse![228; 1 => 3, 3 => -1, 18 => 3, 37 => -1, 56 => -1, 227 => 1],
  sparse![228; 0 => -1, 2 => 3, 3 => 1, 5 => -1, 113 => 3, 227 => -1],
  sparse![228; 5 => 3, 11 => -1, 18 => -1, 56 => 3, 75 => 1, 113 => -1],
  sparse![228; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 11 => 1, 56 => 1, 227 => 1],
  sparse![228; 0 => -3, 1 => 7, 2 => 2, 3 => -3, 5 => -3, 11 => 2, 18 => -1, 37 => 3, 75 => -1, 113 => 1],
  sparse![228; 0 => -2, 1 => 4, 2 => 1, 3 => -1, 56 => -1, 75 => 1, 113 => 4, 227 => -2],
  sparse![228; 0 => -2, 1 => 4, 2 => 2, 3 => -1, 5 => -1, 18 => 1, 56 => 1, 113 => -1, 227 => 1],
]
```

### Level 229

dim S₂ = **18**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **38**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 230

dim S₂ = **33**; eta rank = **31**; full eta basis = **NO**; Sturm bound B = **72**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![230; 0 => 2, 22 => 2],
  sparse![230; 1 => 2, 45 => 2],
  sparse![230; 4 => 2, 114 => 2],
  sparse![230; 9 => 2, 229 => 2],
  sparse![230; 0 => -1, 1 => 3, 22 => -1, 45 => 3],
  sparse![230; 0 => 1, 1 => 1, 22 => 1, 45 => 1],
  sparse![230; 0 => 3, 1 => -1, 22 => 3, 45 => -1],
  sparse![230; 4 => -1, 9 => 3, 114 => -1, 229 => 3],
  sparse![230; 4 => 1, 9 => 1, 114 => 1, 229 => 1],
  sparse![230; 4 => 3, 9 => -1, 114 => 3, 229 => -1],
  sparse![230; 0 => 1, 4 => 1, 22 => 1, 114 => 1],
  sparse![230; 1 => 1, 9 => 1, 45 => 1, 229 => 1],
  sparse![230; 0 => -2, 1 => 4, 4 => 1, 9 => -1, 22 => 3, 45 => -1],
  sparse![230; 0 => -1, 1 => 3, 22 => 4, 45 => -2, 114 => -1, 229 => 1],
  sparse![230; 0 => -1, 1 => 1, 4 => 3, 9 => -1, 22 => 3, 45 => -1, 114 => -1, 229 => 1],
  sparse![230; 4 => 3, 9 => -1, 22 => 4, 45 => -2, 114 => -1, 229 => 1],
  sparse![230; 0 => -2, 1 => 4, 4 => 1, 9 => -1, 114 => -1, 229 => 3],
  sparse![230; 0 => -1, 1 => 3, 4 => 1, 9 => -1, 22 => 1, 45 => -1, 114 => -1, 229 => 3],
  sparse![230; 0 => -1, 1 => 2, 9 => 1, 22 => -1, 45 => 2, 229 => 1],
  sparse![230; 0 => -1, 1 => 2, 4 => 1, 22 => -1, 45 => 2, 114 => 1],
  sparse![230; 0 => -1, 1 => 2, 4 => 2, 9 => -1, 22 => -1, 45 => 2, 114 => 2, 229 => -1],
  sparse![230; 1 => 1, 4 => -1, 9 => 2, 45 => 1, 114 => -1, 229 => 2],
  sparse![230; 1 => 1, 4 => 1, 45 => 1, 114 => 1],
  sparse![230; 1 => 1, 4 => 2, 9 => -1, 45 => 1, 114 => 2, 229 => -1],
  sparse![230; 0 => 1, 4 => -1, 9 => 2, 22 => 1, 114 => -1, 229 => 2],
  sparse![230; 0 => 1, 9 => 1, 22 => 1, 229 => 1],
  sparse![230; 0 => 1, 4 => 2, 9 => -1, 22 => 1, 114 => 2, 229 => -1],
  sparse![230; 0 => 2, 1 => -1, 4 => -1, 9 => 2, 22 => 2, 45 => -1, 114 => -1, 229 => 2],
  sparse![230; 0 => 2, 1 => -1, 9 => 1, 22 => 2, 45 => -1, 229 => 1],
  sparse![230; 0 => 2, 1 => -1, 4 => 1, 22 => 2, 45 => -1, 114 => 1],
  sparse![230; 0 => 1, 1 => -1, 4 => -1, 9 => 3, 22 => -1, 45 => 3, 114 => 1, 229 => -1],
]
```

### Level 231

dim S₂ = **29**; eta rank = **12**; full eta basis = **NO**; Sturm bound B = **64**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![231; 0 => 2, 10 => 2],
  sparse![231; 2 => 2, 32 => 2],
  sparse![231; 6 => 2, 76 => 2],
  sparse![231; 20 => 2, 230 => 2],
  sparse![231; 0 => 1, 2 => 1, 10 => 1, 32 => 1],
  sparse![231; 6 => 1, 20 => 1, 76 => 1, 230 => 1],
  sparse![231; 0 => 1, 6 => 1, 10 => 1, 76 => 1],
  sparse![231; 2 => 1, 20 => 1, 32 => 1, 230 => 1],
  sparse![231; 6 => 1, 10 => 1, 20 => 1, 32 => 1],
  sparse![231; 2 => 1, 6 => 1, 32 => 1, 76 => 1],
  sparse![231; 0 => 1, 10 => 1, 20 => 1, 230 => 1],
  sparse![231; 0 => 1, 2 => 1, 76 => 1, 230 => 1],
]
```

### Level 232

dim S₂ = **27**; eta rank = **10**; full eta basis = **NO**; Sturm bound B = **60**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![232; 1 => 2, 57 => 2],
  sparse![232; 3 => 2, 115 => 2],
  sparse![232; 1 => -1, 3 => 5, 7 => -2, 57 => 1, 115 => -1, 231 => 2],
  sparse![232; 0 => 1, 1 => -1, 3 => 3, 7 => -1, 28 => -1, 57 => 3, 115 => -1, 231 => 1],
  sparse![232; 0 => -1, 1 => 2, 3 => 2, 7 => -1, 28 => 1, 231 => 1],
  sparse![232; 0 => 2, 1 => -1, 3 => 1, 28 => -2, 57 => 5, 115 => -1],
  sparse![232; 0 => 1, 7 => 1, 28 => -1, 57 => 2, 115 => 2, 231 => -1],
  sparse![232; 1 => 1, 3 => -1, 7 => 2, 57 => -1, 115 => 5, 231 => -2],
  sparse![232; 0 => -1, 1 => 3, 3 => -1, 7 => 1, 28 => 1, 57 => -1, 115 => 3, 231 => -1],
  sparse![232; 0 => -2, 1 => 5, 3 => -1, 28 => 2, 57 => -1, 115 => 1],
]
```

### Level 233

dim S₂ = **19**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **39**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 234

dim S₂ = **35**; eta rank = **35**; full eta basis = **YES**; Sturm bound B = **84**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![234; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 12 => 3, 25 => -2, 38 => -2, 77 => 3],
  sparse![234; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 12 => -2, 25 => 3, 38 => 3, 77 => -2],
  sparse![234; 0 => 1, 1 => 1, 38 => 1, 77 => 1],
  sparse![234; 0 => 1, 5 => 1, 25 => 1, 38 => 1],
  sparse![234; 1 => 1, 2 => 1, 12 => 1, 77 => 1],
  sparse![234; 2 => 1, 5 => 1, 12 => 1, 25 => 1],
  sparse![234; 0 => -1, 1 => 1, 2 => 2, 12 => 2, 38 => -1, 77 => 1],
  sparse![234; 0 => -1, 1 => 2, 5 => 1, 12 => 2, 25 => -1, 38 => 1],
  sparse![234; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 12 => 2, 25 => -1, 38 => -1, 77 => 2],
  sparse![234; 1 => 1, 2 => -1, 5 => 2, 12 => 1, 38 => 2, 77 => -1],
  sparse![234; 0 => 1, 1 => -1, 5 => 2, 25 => 2, 38 => 1, 77 => -1],
  sparse![234; 2 => -2, 5 => 3, 8 => 3, 17 => -2, 38 => 3, 77 => -2, 116 => -2, 233 => 3],
  sparse![234; 2 => 3, 5 => -2, 8 => -2, 17 => 3, 38 => -2, 77 => 3, 116 => 3, 233 => -2],
  sparse![234; 2 => 1, 5 => 1, 116 => 1, 233 => 1],
  sparse![234; 2 => 1, 17 => 1, 77 => 1, 116 => 1],
  sparse![234; 5 => 1, 8 => 1, 38 => 1, 233 => 1],
  sparse![234; 8 => 1, 17 => 1, 38 => 1, 77 => 1],
  sparse![234; 2 => -1, 5 => 1, 8 => 2, 38 => 2, 116 => -1, 233 => 1],
  sparse![234; 2 => -1, 5 => 2, 17 => 1, 38 => 2, 77 => -1, 116 => 1],
  sparse![234; 2 => 1, 5 => -1, 17 => 2, 77 => 2, 116 => 1, 233 => -1],
  sparse![234; 0 => -1, 1 => 3, 12 => -1, 25 => 1, 38 => 2],
  sparse![234; 0 => 3, 1 => -1, 12 => 1, 25 => -1, 77 => 2],
  sparse![234; 0 => -1, 1 => 1, 2 => 2, 12 => -1, 25 => 3],
  sparse![234; 2 => 2, 5 => -1, 8 => 1, 12 => 2, 25 => -1, 38 => -2, 77 => 3, 116 => 1, 233 => -1],
  sparse![234; 2 => -1, 5 => 2, 12 => -1, 17 => 1, 25 => 2, 38 => 3, 77 => -2, 116 => -1, 233 => 1],
  sparse![234; 0 => 1, 2 => 2, 5 => -1, 12 => 1, 25 => -1, 38 => -2, 77 => 3, 116 => 2, 233 => -1],
  sparse![234; 0 => -2, 1 => 1, 2 => 7, 5 => -3, 8 => -2, 17 => 1, 38 => 1, 77 => 1],
  sparse![234; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 25 => 1, 38 => -1, 77 => 2],
  sparse![234; 0 => -1, 1 => 1, 2 => 1, 5 => 1, 8 => 1, 17 => -1, 25 => 1, 116 => 1],
  sparse![234; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 12 => 1, 17 => 1, 25 => -1, 38 => -1, 77 => 2, 116 => 1],
  sparse![234; 0 => -1, 1 => 2, 2 => -1, 5 => 2, 8 => 1, 12 => -1, 17 => -1, 25 => 2, 38 => 3, 77 => -2, 116 => -1, 233 => 1],
  sparse![234; 0 => -1, 1 => 2, 17 => 1, 38 => 2, 116 => -1, 233 => 1],
  sparse![234; 0 => -1, 1 => 2, 5 => 1, 12 => -1, 25 => 2, 38 => 2, 77 => -1],
  sparse![234; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 8 => 1, 77 => 2, 116 => 1, 233 => -1],
  sparse![234; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 12 => -1, 25 => 2, 77 => 1],
]
```

### Level 235

dim S₂ = **23**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **48**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![235; 0 => 2, 46 => 2],
  sparse![235; 4 => 2, 234 => 2],
  sparse![235; 0 => 1, 4 => 1, 46 => 1, 234 => 1],
]
```

### Level 236

dim S₂ = **28**; eta rank = **4**; full eta basis = **NO**; Sturm bound B = **60**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![236; 0 => 2, 58 => 2],
  sparse![236; 1 => 2, 117 => 2],
  sparse![236; 3 => 2, 235 => 2],
  sparse![236; 0 => -2, 1 => 6, 3 => -2, 58 => -2, 117 => 6, 235 => -2],
]
```

### Level 237

dim S₂ = **25**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **53**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 238

dim S₂ = **33**; eta rank = **27**; full eta basis = **NO**; Sturm bound B = **72**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![238; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![238; 16 => 1, 33 => 1, 118 => 1, 237 => 1],
  sparse![238; 0 => 2, 118 => 2],
  sparse![238; 0 => 1, 6 => 1, 16 => 1, 118 => 1],
  sparse![238; 6 => 2, 16 => 2],
  sparse![238; 1 => 2, 237 => 2],
  sparse![238; 1 => 1, 13 => 1, 33 => 1, 237 => 1],
  sparse![238; 13 => 2, 33 => 2],
  sparse![238; 0 => 2, 1 => -1, 6 => 2, 13 => -1, 16 => -1, 33 => 2, 118 => -1, 237 => 2],
  sparse![238; 0 => -2, 1 => 4, 6 => 1, 13 => -1, 16 => 1, 33 => -1, 118 => -2, 237 => 4],
  sparse![238; 0 => -1, 1 => 3, 118 => -1, 237 => 3],
  sparse![238; 0 => 1, 1 => 1, 118 => 1, 237 => 1],
  sparse![238; 0 => 3, 1 => -1, 118 => 3, 237 => -1],
  sparse![238; 0 => 4, 1 => -2, 6 => -1, 13 => 1, 16 => -1, 33 => 1, 118 => 4, 237 => -2],
  sparse![238; 0 => -1, 1 => 2, 6 => 2, 13 => -1, 16 => 2, 33 => -1, 118 => -1, 237 => 2],
  sparse![238; 1 => 1, 6 => 2, 13 => -1, 16 => 2, 33 => -1, 237 => 1],
  sparse![238; 0 => 1, 6 => 2, 13 => -1, 16 => 2, 33 => -1, 118 => 1],
  sparse![238; 0 => -1, 1 => 2, 6 => 1, 16 => 1, 118 => -1, 237 => 2],
  sparse![238; 1 => 1, 6 => 1, 16 => 1, 237 => 1],
  sparse![238; 0 => 2, 1 => -1, 6 => 1, 16 => 1, 118 => 2, 237 => -1],
  sparse![238; 0 => -1, 1 => 2, 13 => 1, 33 => 1, 118 => -1, 237 => 2],
  sparse![238; 0 => 1, 13 => 1, 33 => 1, 118 => 1],
  sparse![238; 0 => 2, 1 => -1, 13 => 1, 33 => 1, 118 => 2, 237 => -1],
  sparse![238; 0 => 1, 6 => -1, 13 => 2, 16 => -1, 33 => 2, 118 => 1],
  sparse![238; 0 => 2, 1 => -1, 6 => -1, 13 => 2, 16 => -1, 33 => 2, 118 => 2, 237 => -1],
  sparse![238; 0 => -1, 1 => 1, 6 => 4, 13 => -2, 16 => 4, 33 => -2, 118 => -1, 237 => 1],
  sparse![238; 6 => 1, 13 => 1, 16 => 1, 33 => 1],
]
```

### Level 239

dim S₂ = **20**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **40**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![239; 0 => 2, 238 => 2],
]
```

### Level 240

dim S₂ = **37**; eta rank = **37**; full eta basis = **YES**; Sturm bound B = **96**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![240; 0 => -7, 1 => 14, 2 => 7, 3 => -5, 4 => 1, 5 => -7, 9 => -2, 11 => 2, 14 => -1, 19 => 1, 29 => 1],
  sparse![240; 0 => -6, 1 => 12, 2 => 6, 3 => -5, 4 => 1, 5 => -6, 7 => 2, 9 => -2, 11 => 2, 14 => -1, 15 => -1, 19 => 1, 23 => -1, 29 => 1, 47 => 1],
  sparse![240; 0 => -5, 1 => 9, 2 => 5, 3 => -1, 4 => 1, 5 => -6, 7 => -1, 9 => -2, 11 => 4, 14 => -1, 19 => 1, 23 => -1, 29 => 1],
  sparse![240; 0 => -5, 1 => 11, 2 => 1, 3 => -4, 4 => 5, 5 => -2, 9 => -4, 11 => 1, 14 => -1, 19 => 1, 29 => 1],
  sparse![240; 0 => -5, 1 => 13, 2 => 1, 3 => -5, 4 => -1, 5 => -4, 9 => -1, 11 => 2, 14 => 5, 19 => 1, 29 => -2],
  sparse![240; 0 => -4, 1 => 8, 2 => 1, 3 => -1, 4 => 4, 5 => -2, 7 => -1, 9 => -3, 11 => 1, 14 => -1, 29 => 1, 39 => 1],
  sparse![240; 0 => -4, 1 => 8, 2 => 2, 3 => -2, 4 => 2, 5 => -3, 9 => -1, 11 => 1, 19 => 1],
  sparse![240; 0 => -4, 1 => 8, 2 => 2, 3 => -2, 4 => 3, 5 => -3, 9 => -3, 11 => 1, 14 => -1, 19 => 1, 29 => 1, 39 => 2, 79 => -1, 119 => -1, 239 => 1],
  sparse![240; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 4 => -2, 5 => -2, 9 => 4, 11 => 1, 14 => 1, 29 => -2, 59 => 1],
  sparse![240; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 4 => 1, 5 => -3, 9 => -5, 11 => 2, 19 => 9, 29 => 2, 39 => -3, 59 => -3, 119 => 1],
  sparse![240; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 4 => 1, 5 => -3, 9 => -3, 11 => 2, 19 => 2, 29 => 4, 59 => -2],
  sparse![240; 0 => -4, 1 => 10, 2 => 2, 3 => -4, 4 => 1, 5 => -4, 9 => -3, 11 => 2, 14 => -1, 19 => 2, 29 => 3],
  sparse![240; 0 => -3, 1 => 5, 2 => 1, 3 => 2, 4 => 3, 5 => -2, 7 => -2, 9 => -2, 11 => 1, 14 => -1, 19 => -1, 29 => 1, 39 => 2],
  sparse![240; 0 => -3, 1 => 5, 2 => 2, 3 => -1, 4 => 2, 5 => -1, 9 => -1, 14 => 1, 29 => -1, 59 => 1],
  sparse![240; 0 => -3, 1 => 5, 2 => 3, 4 => 1, 5 => -3, 7 => -1, 14 => -1, 19 => -1, 23 => 1, 29 => 2, 39 => 1, 59 => 1, 119 => -1],
  sparse![240; 0 => -3, 1 => 5, 2 => 3, 4 => 2, 5 => -3, 7 => -1, 9 => -2, 14 => -2, 19 => -1, 23 => 1, 29 => 3, 39 => 3, 59 => 1, 79 => -1, 119 => -2, 239 => 1],
  sparse![240; 0 => -3, 1 => 6, 2 => 1, 3 => -2, 4 => 1, 14 => 1],
  sparse![240; 0 => -3, 1 => 6, 2 => 1, 3 => -2, 4 => 3, 5 => -2, 7 => 2, 9 => -3, 11 => 1, 14 => -1, 15 => -1, 19 => 1, 23 => -1, 29 => 1, 39 => 2, 47 => 1, 79 => -1, 119 => -1, 239 => 1],
  sparse![240; 0 => -3, 1 => 6, 2 => 1, 4 => 1, 5 => -2, 7 => -1, 9 => -2, 11 => 1, 14 => 1, 19 => 1, 59 => 2, 119 => -1],
  sparse![240; 0 => -3, 1 => 6, 2 => 1, 4 => 3, 5 => -2, 7 => -1, 9 => -3, 14 => -1, 19 => 3, 23 => 1, 29 => 1, 39 => -1, 59 => -1, 119 => 1],
  sparse![240; 0 => -3, 1 => 6, 2 => 2, 3 => -2, 4 => 1, 5 => -2, 23 => 2, 47 => -1, 239 => 1],
  sparse![240; 0 => -3, 1 => 6, 2 => 2, 3 => -2, 4 => 2, 5 => -3, 9 => -2, 11 => 3, 14 => -1, 23 => -1, 29 => 2, 39 => 2, 59 => -1, 79 => -1, 239 => 1],
  sparse![240; 0 => -3, 1 => 6, 2 => 2, 4 => 1, 5 => -3, 7 => -1, 9 => -2, 14 => -2, 19 => -1, 23 => 1, 29 => 4, 39 => 3, 59 => 1, 79 => -1, 119 => -2, 239 => 1],
  sparse![240; 0 => -3, 1 => 7, 2 => 1, 3 => -3, 4 => 1, 5 => -2, 7 => 2, 9 => -2, 11 => 2, 14 => -1, 15 => -1, 19 => 2, 23 => -2, 29 => 2, 39 => -2, 47 => 1, 59 => -3, 79 => 1, 119 => 7, 239 => -3],
  sparse![240; 0 => -2, 1 => 1, 2 => 1, 3 => 6, 4 => 2, 7 => -3, 9 => -2, 11 => -2, 14 => -1, 19 => 2, 23 => 1, 29 => 1],
  sparse![240; 0 => -2, 1 => 1, 2 => 4, 3 => 1, 4 => 2, 5 => -2, 9 => -1, 19 => 1],
  sparse![240; 0 => -2, 1 => 2, 2 => 1, 3 => 4, 4 => 2, 5 => -1, 7 => -2, 9 => -1, 11 => -1, 14 => -1, 19 => -1, 23 => 1, 59 => 2, 119 => 1],
  sparse![240; 0 => -2, 1 => 2, 2 => 2, 3 => 2, 4 => 1, 5 => -1, 7 => -1, 14 => 1, 19 => -1, 29 => -1, 39 => 1, 59 => 1],
  sparse![240; 0 => -2, 1 => 2, 2 => 3, 4 => 3, 5 => -2, 7 => 1, 9 => -2, 14 => -2, 15 => -1, 29 => 2, 47 => 1, 79 => 1, 119 => 1, 239 => -1],
  sparse![240; 0 => -2, 1 => 2, 2 => 3, 3 => 1, 4 => 1, 5 => -2, 7 => -1, 9 => 1, 19 => -1, 23 => 1, 29 => -1, 39 => 1, 59 => 2, 119 => -1],
  sparse![240; 0 => -2, 1 => 2, 2 => 3, 3 => 1, 4 => 2, 5 => -2, 7 => -1, 9 => -1, 14 => -1, 19 => -1, 23 => 1, 39 => 3, 59 => 2, 79 => -1, 119 => -2, 239 => 1],
  sparse![240; 0 => -2, 1 => 2, 2 => 4, 4 => 1, 5 => -2, 14 => -1, 19 => 1, 59 => 1],
  sparse![240; 0 => -2, 1 => 3, 2 => 1, 3 => -1, 4 => 2, 7 => 2, 9 => -1, 14 => 1, 15 => -1, 23 => -1, 29 => -1, 47 => 1, 59 => 1],
  sparse![240; 0 => -2, 1 => 3, 2 => 1, 3 => 1, 4 => 1, 5 => -1, 7 => 1, 11 => -1, 15 => -1, 19 => -1, 23 => 1, 29 => -1, 59 => 3, 119 => -1, 239 => 1],
  sparse![240; 0 => -1, 1 => -2, 2 => 2, 3 => 6, 4 => 2, 7 => -2, 9 => -1, 11 => -1, 14 => -1, 29 => 1, 59 => -1, 119 => 2],
  sparse![240; 0 => -1, 1 => -2, 2 => 2, 3 => 6, 4 => 2, 5 => 1, 7 => -2, 9 => 1, 11 => -3, 14 => -1, 19 => -3, 23 => 1, 29 => -2, 39 => 1, 59 => 6, 119 => -2],
  sparse![240; 0 => -1, 1 => -1, 2 => 2, 3 => 3, 4 => 1, 7 => 1, 11 => -1, 15 => -1, 239 => 1],
]
```

### Level 241

dim S₂ = **19**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **40**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 242

dim S₂ = **22**; eta rank = **10**; full eta basis = **NO**; Sturm bound B = **66**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![242; 0 => 2, 10 => 2],
  sparse![242; 1 => 2, 21 => 2],
  sparse![242; 10 => 2, 120 => 2],
  sparse![242; 21 => 2, 241 => 2],
  sparse![242; 0 => 1, 10 => 2, 120 => 1],
  sparse![242; 1 => 1, 21 => 2, 241 => 1],
  sparse![242; 0 => 2, 1 => -1, 10 => 2, 241 => 1],
  sparse![242; 1 => 1, 10 => 2, 120 => 2, 241 => -1],
  sparse![242; 0 => 1, 21 => 2, 120 => -1, 241 => 2],
  sparse![242; 0 => -1, 1 => 2, 21 => 2, 120 => 1],
]
```

### Level 243

dim S₂ = **19**; eta rank = **16**; full eta basis = **NO**; Sturm bound B = **54**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![243; 2 => 2, 8 => 2],
  sparse![243; 8 => 2, 26 => 2],
  sparse![243; 26 => 2, 80 => 2],
  sparse![243; 2 => -1, 8 => 6, 26 => -1],
  sparse![243; 2 => 1, 8 => 2, 26 => 1],
  sparse![243; 8 => -1, 26 => 6, 80 => -1],
  sparse![243; 8 => 1, 26 => 2, 80 => 1],
  sparse![243; 2 => 2, 8 => -1, 26 => 4, 80 => -1],
  sparse![243; 2 => 1, 8 => -1, 26 => 5, 80 => -1],
  sparse![243; 2 => 2, 8 => 1, 80 => 1],
  sparse![243; 2 => 1, 8 => 1, 26 => 1, 80 => 1],
  sparse![243; 2 => 2, 80 => 2],
  sparse![243; 2 => 1, 26 => 1, 80 => 2],
  sparse![243; 2 => -1, 8 => 3, 26 => 3, 80 => -1],
  sparse![243; 2 => -1, 8 => 5, 26 => -1, 80 => 1],
  sparse![243; 2 => -1, 8 => 4, 26 => -1, 80 => 2],
]
```

### Level 244

dim S₂ = **29**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **62**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 245

dim S₂ = **21**; eta rank = **10**; full eta basis = **NO**; Sturm bound B = **56**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![245; 0 => 2, 34 => 2],
  sparse![245; 0 => 1, 4 => 1, 6 => 1, 34 => 1],
  sparse![245; 4 => 2, 6 => 2],
  sparse![245; 6 => 2, 244 => 2],
  sparse![245; 6 => 1, 34 => 1, 48 => 1, 244 => 1],
  sparse![245; 34 => 2, 48 => 2],
  sparse![245; 0 => 1, 6 => 1, 34 => 1, 244 => 1],
  sparse![245; 4 => 1, 6 => 2, 244 => 1],
  sparse![245; 0 => 1, 34 => 2, 48 => 1],
  sparse![245; 4 => 1, 6 => 1, 34 => 1, 48 => 1],
]
```

### Level 246

dim S₂ = **39**; eta rank = **14**; full eta basis = **NO**; Sturm bound B = **84**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![246; 0 => 1, 2 => 1, 40 => 1, 122 => 1],
  sparse![246; 1 => 1, 5 => 1, 81 => 1, 245 => 1],
  sparse![246; 0 => 3, 1 => -1, 2 => -1, 5 => 1, 40 => -1, 81 => 1, 122 => 3, 245 => -1],
  sparse![246; 1 => 2, 2 => 1, 5 => -1, 40 => -1, 81 => 1, 122 => 2],
  sparse![246; 0 => 2, 2 => -1, 5 => 1, 40 => 1, 81 => -1, 245 => 2],
  sparse![246; 0 => -1, 1 => 3, 2 => 1, 5 => -1, 40 => 1, 81 => -1, 122 => -1, 245 => 3],
  sparse![246; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 40 => 1, 245 => 1],
  sparse![246; 1 => 1, 2 => 1, 40 => 3, 81 => -2, 122 => -2, 245 => 3],
  sparse![246; 0 => 1, 5 => 1, 40 => -2, 81 => 3, 122 => 3, 245 => -2],
  sparse![246; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 81 => 1, 122 => 1],
  sparse![246; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 40 => 3, 81 => -1, 122 => -1, 245 => 1],
  sparse![246; 0 => -1, 1 => 1, 2 => 2, 81 => 2, 122 => 1, 245 => -1],
  sparse![246; 0 => 1, 1 => -1, 5 => 2, 40 => 2, 122 => -1, 245 => 1],
  sparse![246; 0 => 1, 1 => -1, 2 => -1, 5 => 3, 40 => -1, 81 => 3, 122 => 1, 245 => -1],
]
```

### Level 247

dim S₂ = **21**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **46**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 248

dim S₂ = **29**; eta rank = **11**; full eta basis = **NO**; Sturm bound B = **64**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![248; 0 => 1, 1 => 1, 30 => 1, 61 => 1],
  sparse![248; 1 => 1, 3 => 1, 61 => 1, 123 => 1],
  sparse![248; 3 => 1, 7 => 1, 123 => 1, 247 => 1],
  sparse![248; 0 => -1, 1 => 4, 3 => -1, 30 => -1, 61 => 4, 123 => -1],
  sparse![248; 1 => -1, 3 => 4, 7 => -1, 61 => -1, 123 => 4, 247 => -1],
  sparse![248; 1 => -1, 3 => 3, 61 => 3, 123 => -1],
  sparse![248; 0 => 1, 1 => -1, 3 => 3, 7 => -1, 30 => 1, 61 => -1, 123 => 3, 247 => -1],
  sparse![248; 0 => 1, 7 => 1, 30 => 1, 247 => 1],
  sparse![248; 0 => -1, 1 => 2, 3 => 2, 7 => -1, 30 => -1, 61 => 2, 123 => 2, 247 => -1],
  sparse![248; 0 => -1, 1 => 3, 3 => -1, 7 => 1, 30 => -1, 61 => 3, 123 => -1, 247 => 1],
  sparse![248; 1 => 3, 3 => -1, 61 => -1, 123 => 3],
]
```

### Level 249

dim S₂ = **27**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **56**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![249; 0 => 2, 82 => 2],
  sparse![249; 2 => 2, 248 => 2],
  sparse![249; 0 => 1, 2 => 1, 82 => 1, 248 => 1],
]
```

### Level 250

dim S₂ = **28**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **75**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 251

dim S₂ = **21**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **42**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![251; 0 => 2, 250 => 2],
]
```

### Level 252

dim S₂ = **37**; eta rank = **37**; full eta basis = **YES**; Sturm bound B = **96**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![252; 0 => -4, 1 => 8, 2 => 3, 3 => -3, 5 => -3, 6 => 2, 11 => 1, 13 => -1, 20 => 1],
  sparse![252; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 6 => -4, 11 => 1, 13 => 10, 20 => 1, 27 => -4, 41 => -2, 83 => 1],
  sparse![252; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 6 => -2, 11 => 1, 13 => 3, 20 => 3, 27 => -1, 41 => -1],
  sparse![252; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 6 => -2, 11 => 1, 13 => 5, 27 => -2, 62 => 1, 125 => -1, 251 => 1],
  sparse![252; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 6 => -1, 11 => 1, 20 => 3, 27 => 1, 62 => -1, 83 => -1, 251 => 1],
  sparse![252; 0 => -4, 1 => 10, 2 => 2, 3 => -4, 5 => -4, 11 => 2, 20 => -2, 41 => 6, 83 => -2],
  sparse![252; 0 => -3, 1 => 6, 2 => 1, 3 => -2, 6 => 3, 13 => -2, 20 => -1, 83 => 2],
  sparse![252; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 5 => -3, 6 => -1, 8 => -1, 11 => 1, 13 => 4, 17 => 1, 20 => -1, 27 => -2, 41 => 1, 62 => 1, 83 => 1, 125 => -1],
  sparse![252; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 5 => -3, 8 => -1, 11 => 1, 13 => -1, 17 => 2, 20 => 2, 27 => 1, 35 => -1, 62 => -1, 83 => -1, 251 => 2],
  sparse![252; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 5 => -3, 6 => 1, 8 => -1, 11 => 1, 13 => -1, 17 => 1, 20 => -2, 41 => 3, 62 => 2, 125 => -2, 251 => 1],
  sparse![252; 0 => -3, 1 => 7, 3 => -3, 6 => 1, 8 => 1, 11 => 1, 17 => -1, 20 => 2, 41 => -1, 62 => -1, 125 => 1],
  sparse![252; 0 => -3, 1 => 7, 2 => 1, 3 => -3, 5 => -3, 6 => 3, 11 => 3, 13 => -3, 20 => -1, 27 => 1, 41 => 3, 83 => -1],
  sparse![252; 0 => -3, 1 => 7, 2 => 1, 3 => -3, 17 => -1, 27 => 1, 35 => 1, 41 => -1, 83 => 2, 125 => 1, 251 => -1],
  sparse![252; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -2, 6 => -3, 11 => 1, 13 => 7, 20 => 1, 27 => -2, 41 => -2, 83 => 1],
  sparse![252; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -2, 6 => -2, 11 => 1, 13 => 5, 27 => -2, 41 => -1, 62 => 2, 83 => 1, 125 => -1],
  sparse![252; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -1, 83 => 2],
  sparse![252; 0 => -3, 1 => 7, 2 => 2, 3 => -3, 5 => -3, 6 => -1, 8 => -1, 11 => 2, 13 => 3, 17 => 2, 20 => -2, 27 => -1, 35 => -1, 41 => 5, 62 => 1, 83 => -2, 125 => -2, 251 => 1],
  sparse![252; 0 => -3, 1 => 7, 2 => 2, 3 => -3, 5 => -3, 6 => 1, 8 => -1, 11 => 2, 13 => -2, 17 => 2, 20 => -3, 27 => 1, 35 => -1, 41 => 7, 62 => 2, 83 => -3, 125 => -3, 251 => 2],
  sparse![252; 0 => -3, 1 => 7, 2 => 2, 3 => -2, 5 => -3, 6 => 1, 11 => 1, 13 => -3, 20 => -2, 27 => 2, 41 => 7, 83 => -3],
  sparse![252; 0 => -3, 1 => 8, 3 => -3, 6 => -1, 13 => 2, 20 => 2, 27 => -1, 41 => -2, 83 => 2],
  sparse![252; 0 => -2, 1 => 1, 2 => 5, 5 => -2, 6 => 2, 13 => -1, 20 => 1],
  sparse![252; 0 => -2, 1 => 1, 2 => 5, 6 => 2, 8 => -2, 11 => -1, 13 => -1, 17 => 1, 20 => -3, 41 => 4, 62 => 2, 83 => -1, 125 => -1],
  sparse![252; 0 => -2, 1 => 1, 2 => 6, 5 => -3, 6 => 2, 8 => -2, 11 => 1, 13 => -1, 17 => 1, 20 => -2, 41 => 1, 62 => 2, 83 => 1, 125 => -1],
  sparse![252; 0 => -2, 1 => 1, 2 => 6, 5 => -2, 8 => -2, 17 => 1, 20 => 2],
  sparse![252; 0 => -2, 1 => 1, 2 => 6, 5 => -2, 8 => -2, 13 => 2, 17 => 1, 20 => -1, 27 => -1, 41 => 1, 62 => 1, 125 => -1, 251 => 1],
  sparse![252; 0 => -2, 1 => 1, 2 => 7, 5 => -3, 6 => -2, 8 => -2, 13 => 1, 17 => 1, 20 => 7, 41 => -3, 62 => -2, 125 => 1],
  sparse![252; 0 => -2, 1 => 1, 2 => 7, 5 => -3, 6 => -2, 8 => -2, 13 => 3, 17 => 1, 20 => 4, 27 => -1, 41 => -2, 62 => -1, 251 => 1],
  sparse![252; 0 => -2, 1 => 1, 2 => 7, 5 => -3, 6 => -2, 8 => -2, 13 => 4, 17 => 1, 20 => 1, 41 => -1],
  sparse![252; 0 => -2, 1 => 2, 2 => 4, 5 => -2, 6 => 1, 8 => -1, 17 => 1, 125 => 1],
  sparse![252; 0 => -2, 1 => 2, 2 => 5, 3 => -1, 5 => -3, 6 => 2, 8 => -2, 11 => 2, 13 => -2, 17 => 2, 20 => -3, 27 => 1, 35 => -1, 41 => 5, 62 => 2, 83 => -2, 125 => -2, 251 => 1],
  sparse![252; 0 => -2, 1 => 2, 2 => 5, 5 => -3, 8 => -2, 13 => -1, 17 => 2, 20 => 1, 41 => 3, 125 => -1],
  sparse![252; 0 => -2, 1 => 2, 2 => 5, 5 => -3, 8 => -2, 13 => 1, 17 => 2, 20 => -2, 27 => -1, 41 => 4, 62 => 1, 125 => -2, 251 => 1],
  sparse![252; 0 => -2, 1 => 3, 2 => 1, 3 => -1, 5 => 4, 6 => 2, 11 => -2, 13 => -3, 17 => -2, 20 => -3, 27 => 1, 35 => 1, 41 => 6, 83 => -2, 125 => 2, 251 => -1],
  sparse![252; 0 => -2, 1 => 3, 2 => 1, 5 => 1, 6 => 1, 11 => -1, 13 => 1, 27 => -1, 41 => -1, 83 => 2],
  sparse![252; 0 => -2, 1 => 3, 2 => 2, 3 => -1, 5 => -1, 6 => 2, 8 => 1, 13 => -1, 17 => -1, 20 => 1, 35 => 1],
  sparse![252; 0 => -2, 1 => 3, 2 => 2, 5 => -2, 6 => 2, 11 => 1, 13 => -2, 20 => -2, 27 => 1, 41 => 5, 83 => -2],
  sparse![252; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -3, 6 => 2, 11 => 1, 13 => -3, 17 => 2, 20 => -1, 27 => 1, 35 => -1, 41 => 7, 83 => -3, 125 => -2, 251 => 1],
]
```

### Level 253

dim S₂ = **23**; eta rank = **5**; full eta basis = **NO**; Sturm bound B = **48**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![253; 0 => 2, 10 => 2],
  sparse![253; 22 => 2, 252 => 2],
  sparse![253; 0 => 2, 22 => 2],
  sparse![253; 10 => 2, 252 => 2],
  sparse![253; 0 => 1, 10 => 1, 22 => 1, 252 => 1],
]
```

### Level 254

dim S₂ = **31**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **64**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![254; 0 => 1, 1 => 1, 126 => 1, 253 => 1],
]
```

### Level 255

dim S₂ = **33**; eta rank = **10**; full eta basis = **NO**; Sturm bound B = **72**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![255; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![255; 16 => 1, 50 => 1, 84 => 1, 254 => 1],
  sparse![255; 0 => 1, 2 => 1, 16 => 1, 50 => 1],
  sparse![255; 4 => 1, 14 => 1, 84 => 1, 254 => 1],
  sparse![255; 0 => -1, 2 => 2, 4 => 2, 14 => -1, 16 => 2, 50 => -1, 84 => -1, 254 => 2],
  sparse![255; 2 => 1, 4 => 1, 50 => 1, 84 => 1],
  sparse![255; 2 => 1, 14 => 1, 16 => 1, 84 => 1],
  sparse![255; 0 => 1, 4 => 1, 50 => 1, 254 => 1],
  sparse![255; 0 => 1, 14 => 1, 16 => 1, 254 => 1],
  sparse![255; 0 => 2, 2 => -1, 4 => -1, 14 => 2, 16 => -1, 50 => 2, 84 => 2, 254 => -1],
]
```

### Level 256

dim S₂ = **21**; eta rank = **21**; full eta basis = **YES**; Sturm bound B = **64**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![256; 3 => 2, 7 => 2],
  sparse![256; 7 => 2, 15 => 2],
  sparse![256; 15 => 2, 31 => 2],
  sparse![256; 31 => 2, 63 => 2],
  sparse![256; 0 => -2, 1 => 5, 3 => -2, 7 => 3],
  sparse![256; 1 => -2, 3 => 5, 7 => -2, 15 => 3],
  sparse![256; 3 => -2, 7 => 5, 15 => -2, 31 => 3],
  sparse![256; 1 => -2, 3 => 5, 7 => -1, 15 => 1, 31 => -1, 63 => 2],
  sparse![256; 1 => 2, 3 => 1, 15 => 1],
  sparse![256; 3 => 2, 31 => 2],
  sparse![256; 7 => 1, 31 => 1, 63 => 2],
  sparse![256; 3 => -2, 7 => 5, 15 => -1, 31 => 1, 63 => -1, 127 => 2],
  sparse![256; 3 => 2, 7 => 1, 31 => 1],
  sparse![256; 7 => 2, 63 => 2],
  sparse![256; 15 => 1, 63 => 1, 127 => 2],
  sparse![256; 0 => -2, 1 => 5, 3 => -2, 7 => 2, 31 => 1],
  sparse![256; 0 => -4, 1 => 10, 3 => -4, 7 => -1, 15 => 4, 31 => -1],
  sparse![256; 0 => -2, 1 => 3, 3 => 3, 7 => -2, 15 => 1, 31 => 1],
  sparse![256; 0 => -2, 1 => 5, 3 => -4, 7 => 4, 15 => 2, 31 => -1],
  sparse![256; 0 => -2, 1 => 5, 3 => -2, 7 => -1, 15 => 2, 31 => 4, 63 => -2],
  sparse![256; 1 => -2, 3 => 5, 7 => -3, 15 => 4, 31 => -3, 63 => 5, 127 => -2],
]
```

### Level 257

dim S₂ = **21**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **43**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 258

dim S₂ = **41**; eta rank = **16**; full eta basis = **NO**; Sturm bound B = **88**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![258; 0 => 3, 1 => -1, 42 => -1, 85 => 3],
  sparse![258; 0 => -1, 1 => 3, 42 => 3, 85 => -1],
  sparse![258; 2 => 3, 5 => -1, 128 => -1, 257 => 3],
  sparse![258; 2 => -1, 5 => 3, 128 => 3, 257 => -1],
  sparse![258; 1 => 1, 2 => 1, 42 => -2, 85 => 3, 128 => 3, 257 => -2],
  sparse![258; 0 => 1, 1 => -1, 5 => 2, 42 => -1, 85 => 1, 128 => 2],
  sparse![258; 0 => 1, 2 => -1, 5 => 2, 85 => 1, 128 => 2, 257 => -1],
  sparse![258; 0 => 2, 1 => -1, 5 => 1, 42 => -1, 85 => 2, 128 => 1],
  sparse![258; 0 => 2, 2 => -1, 5 => 1, 85 => 2, 128 => 1, 257 => -1],
  sparse![258; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 42 => 1, 257 => 1],
  sparse![258; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 85 => 1, 128 => 1],
  sparse![258; 0 => -1, 1 => 1, 2 => 2, 42 => 1, 85 => -1, 257 => 2],
  sparse![258; 0 => -1, 1 => 2, 2 => 1, 42 => 2, 85 => -1, 257 => 1],
  sparse![258; 1 => 1, 2 => 2, 5 => -1, 42 => 1, 128 => -1, 257 => 2],
  sparse![258; 1 => 2, 2 => 1, 5 => -1, 42 => 2, 128 => -1, 257 => 1],
  sparse![258; 0 => 1, 5 => 1, 42 => 3, 85 => -2, 128 => -2, 257 => 3],
]
```

### Level 259

dim S₂ = **23**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **50**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 260

dim S₂ = **37**; eta rank = **37**; full eta basis = **YES**; Sturm bound B = **84**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![260; 1 => 2, 9 => 2],
  sparse![260; 25 => 2, 129 => 2],
  sparse![260; 0 => 2, 1 => -1, 19 => 1, 51 => 1, 64 => -2, 129 => 5, 259 => -2],
  sparse![260; 1 => -1, 3 => 2, 4 => 1, 12 => 1, 64 => -2, 129 => 5, 259 => -2],
  sparse![260; 1 => 1, 4 => 1, 12 => 2, 25 => -1, 64 => 1],
  sparse![260; 1 => 1, 19 => 1, 25 => -1, 51 => 2, 259 => 1],
  sparse![260; 0 => 1, 9 => 1, 12 => 1, 64 => 2, 129 => -1],
  sparse![260; 0 => 3, 1 => -1, 12 => -1, 25 => 1, 64 => 2],
  sparse![260; 0 => 2, 1 => -1, 4 => 1, 25 => 1, 64 => 1],
  sparse![260; 4 => 3, 9 => -1, 12 => 2, 64 => -1, 129 => 1],
  sparse![260; 3 => 1, 9 => 1, 51 => 1, 129 => -1, 259 => 2],
  sparse![260; 1 => 2, 129 => 2],
  sparse![260; 1 => 1, 9 => 1, 25 => 1, 129 => 1],
  sparse![260; 9 => 2, 25 => 2],
  sparse![260; 0 => -3, 1 => 8, 3 => -3, 12 => 1, 25 => -2, 51 => 1, 64 => -2, 129 => 6, 259 => -2],
  sparse![260; 0 => -2, 1 => 4, 3 => -1, 4 => 2, 9 => -2, 12 => 2, 19 => 1, 25 => -2, 51 => 1, 64 => -2, 129 => 4, 259 => -1],
  sparse![260; 0 => -2, 1 => 4, 3 => -1, 4 => 2, 9 => -1, 25 => 1, 259 => 1],
  sparse![260; 0 => -2, 1 => 5, 3 => -2, 4 => -1, 9 => 3, 19 => -1, 25 => 1, 64 => -1, 129 => 3, 259 => -1],
  sparse![260; 0 => -2, 1 => 5, 3 => -2, 19 => 1, 51 => 1, 64 => 2, 129 => -1],
  sparse![260; 0 => -2, 1 => 5, 3 => -2, 4 => 1, 9 => -2, 12 => 1, 19 => 2, 129 => 1],
  sparse![260; 0 => -2, 1 => 5, 3 => -2, 4 => 1, 12 => 1, 129 => -1, 259 => 2],
  sparse![260; 0 => -2, 1 => 5, 3 => -2, 4 => 2, 9 => -2, 19 => 1, 51 => 1, 129 => 1],
  sparse![260; 0 => -2, 1 => 5, 3 => -1, 64 => 2, 129 => -1, 259 => 1],
  sparse![260; 0 => -2, 1 => 6, 3 => -2, 4 => 1, 9 => -2, 19 => 1, 64 => -3, 129 => 8, 259 => -3],
  sparse![260; 0 => -1, 1 => 1, 4 => 2, 12 => 3, 25 => -1],
  sparse![260; 0 => -1, 1 => 1, 3 => 1, 4 => 1, 9 => 1, 12 => 1, 19 => -1, 25 => 1, 51 => -1, 64 => -1, 129 => 1, 259 => 1],
  sparse![260; 0 => -1, 1 => 1, 3 => 1, 4 => 2, 9 => -1, 25 => 1, 64 => -1, 129 => 3, 259 => -1],
  sparse![260; 0 => -1, 1 => 2, 3 => -1, 4 => 1, 12 => 1, 19 => 1, 51 => 1, 64 => -1, 129 => 2, 259 => -1],
  sparse![260; 0 => -1, 1 => 2, 4 => -1, 9 => 2, 12 => 1, 64 => 1],
  sparse![260; 0 => -1, 1 => 2, 9 => 2, 19 => -1, 51 => 1, 64 => 1],
  sparse![260; 0 => -1, 1 => 2, 4 => 1, 9 => -1, 12 => -1, 19 => 1, 25 => 3, 51 => -1, 64 => 1],
  sparse![260; 0 => -1, 1 => 2, 4 => 1, 12 => 1, 64 => -1, 129 => 2],
  sparse![260; 0 => -1, 1 => 2, 3 => 1, 64 => 1, 129 => 2, 259 => -1],
  sparse![260; 0 => -1, 1 => 3, 3 => -1, 4 => -2, 9 => 5, 12 => -1, 19 => -2, 25 => 3, 51 => -1, 129 => 1],
  sparse![260; 0 => -1, 1 => 3, 3 => -1, 4 => -1, 9 => 3, 12 => 1, 19 => -1, 25 => -1, 51 => 1, 64 => 1, 129 => -1, 259 => 1],
  sparse![260; 0 => -1, 1 => 3, 3 => -1, 9 => -1, 12 => 2, 19 => 2, 25 => -1, 64 => -1, 129 => 3, 259 => -1],
  sparse![260; 0 => -1, 1 => 3, 3 => -1, 19 => 1, 25 => 2, 51 => -1, 64 => 1, 129 => -1, 259 => 1],
]
```

### Level 261

dim S₂ = **27**; eta rank = **2**; full eta basis = **NO**; Sturm bound B = **60**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![261; 0 => 1, 2 => 1, 28 => 1, 86 => 1],
  sparse![261; 2 => 1, 8 => 1, 86 => 1, 260 => 1],
]
```

### Level 262

dim S₂ = **32**; eta rank = **2**; full eta basis = **NO**; Sturm bound B = **66**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![262; 0 => 2, 130 => 2],
  sparse![262; 1 => 2, 261 => 2],
]
```

### Level 263

dim S₂ = **22**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **44**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![263; 0 => 2, 262 => 2],
]
```

### Level 264

dim S₂ = **41**; eta rank = **41**; full eta basis = **YES**; Sturm bound B = **96**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![264; 0 => -4, 1 => 9, 2 => 2, 3 => -3, 5 => -3, 10 => 2, 11 => 1],
  sparse![264; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 10 => 1, 11 => 1, 21 => -3, 32 => -2, 43 => 2, 65 => 5, 131 => -1],
  sparse![264; 0 => -4, 1 => 10, 2 => 2, 3 => -4, 5 => -4, 11 => 2, 32 => -2, 65 => 6, 131 => -2],
  sparse![264; 0 => -3, 1 => 6, 2 => 1, 3 => -1, 5 => -1, 10 => 3, 21 => -3, 32 => -1, 43 => 2, 65 => 2, 131 => -1],
  sparse![264; 0 => -3, 1 => 6, 2 => 1, 5 => -2, 7 => -1, 10 => 3, 21 => -3, 23 => 1, 32 => -1, 43 => 3, 65 => 1, 87 => -1, 131 => -1, 263 => 1],
  sparse![264; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 5 => -3, 10 => -3, 11 => 1, 21 => 6, 32 => 3, 43 => -2, 65 => -3, 131 => 1],
  sparse![264; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 5 => -3, 10 => -1, 11 => 1, 21 => 1, 32 => 1, 43 => 2, 65 => -2, 87 => -1, 131 => 3, 263 => -1],
  sparse![264; 0 => -3, 1 => 7, 2 => 1, 3 => -3, 5 => -3, 7 => 1, 10 => 3, 11 => 3, 21 => -2, 23 => -1, 32 => -1, 87 => 1, 131 => 2, 263 => -1],
  sparse![264; 0 => -3, 1 => 7, 2 => 1, 3 => -3, 5 => -2, 10 => 3, 11 => 2, 21 => -2, 32 => -1, 65 => 1, 131 => 1],
  sparse![264; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -2, 7 => -1, 10 => 3, 11 => -1, 21 => -1, 23 => 3, 32 => -1, 43 => -2, 65 => -2, 87 => 1, 131 => 7, 263 => -3],
  sparse![264; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -2, 10 => -3, 11 => 1, 21 => 7, 32 => 1, 43 => -2, 65 => -2, 131 => 1],
  sparse![264; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -2, 10 => -1, 11 => 1, 32 => 3, 43 => 1, 65 => -1],
  sparse![264; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -1, 131 => 2],
  sparse![264; 0 => -3, 1 => 7, 2 => 1, 3 => -1, 5 => -2, 7 => -1, 10 => -3, 21 => 7, 23 => 1, 32 => 1, 43 => -1, 65 => -2, 87 => -1, 263 => 1],
  sparse![264; 0 => -3, 1 => 7, 2 => 1, 3 => -1, 5 => -2, 7 => -1, 10 => -1, 23 => 1, 32 => 3, 43 => 2, 65 => -1, 87 => -1, 131 => -1, 263 => 1],
  sparse![264; 0 => -3, 1 => 8, 2 => 1, 3 => -4, 5 => -3, 7 => 1, 10 => -3, 11 => 3, 21 => 8, 23 => -1, 32 => 1, 43 => -4, 65 => -3, 87 => 1, 131 => 3, 263 => -1],
  sparse![264; 0 => -3, 1 => 8, 2 => 1, 3 => -3, 5 => -3, 10 => -3, 11 => 2, 21 => 8, 32 => 1, 43 => -3, 65 => -3, 131 => 2],
  sparse![264; 0 => -3, 1 => 8, 2 => 1, 3 => -3, 5 => -2, 10 => -3, 11 => 1, 21 => 8, 32 => 1, 43 => -3, 65 => -2, 131 => 1],
  sparse![264; 0 => -3, 1 => 8, 2 => 1, 3 => -3, 5 => -2, 10 => -1, 11 => 1, 21 => 1, 32 => 3, 65 => -1],
  sparse![264; 0 => -3, 1 => 9, 2 => 1, 3 => -4, 5 => -3, 11 => 2, 43 => 2],
  sparse![264; 0 => -2, 1 => 2, 2 => 4, 5 => -2, 10 => 2],
  sparse![264; 0 => -2, 1 => 3, 3 => 3, 5 => 1, 7 => -2, 11 => -2, 23 => 1, 32 => 2, 65 => -2, 131 => 3, 263 => -1],
  sparse![264; 0 => -2, 1 => 3, 2 => 1, 3 => 2, 5 => -1, 7 => -1, 10 => 1, 11 => -1, 21 => -2, 23 => 1, 43 => 5, 87 => -2],
  sparse![264; 0 => -2, 1 => 3, 2 => 1, 3 => 3, 5 => -2, 7 => -2, 11 => 1, 32 => -1, 65 => 3, 131 => -2, 263 => 2],
  sparse![264; 0 => -2, 1 => 3, 2 => 2, 5 => -1, 10 => 2, 21 => -3, 32 => -2, 43 => 2, 65 => 5, 131 => -2],
  sparse![264; 0 => -2, 1 => 3, 2 => 2, 3 => 1, 5 => -3, 7 => -1, 10 => 2, 11 => 3, 21 => -2, 23 => -1, 32 => -2, 65 => 4, 87 => 1, 131 => -2, 263 => 1],
  sparse![264; 0 => -2, 1 => 3, 2 => 2, 3 => 1, 5 => -2, 7 => -1, 11 => 1, 43 => 2, 65 => 1, 87 => -1],
  sparse![264; 0 => -2, 1 => 3, 2 => 2, 3 => 1, 5 => -2, 7 => -1, 10 => 2, 21 => -3, 23 => 1, 32 => -2, 43 => 3, 65 => 4, 87 => -1, 131 => -2, 263 => 1],
  sparse![264; 0 => -2, 1 => 3, 2 => 2, 3 => 1, 5 => -1, 7 => -1, 11 => -1, 21 => -2, 23 => 1, 43 => 5, 87 => -2, 131 => 1],
  sparse![264; 0 => -2, 1 => 3, 2 => 4, 3 => -1, 5 => -3, 11 => 1, 32 => -2, 65 => 6, 131 => -2],
  sparse![264; 0 => -2, 1 => 4, 3 => -1, 5 => 2, 11 => -1, 21 => 1, 32 => 2, 65 => -1],
  sparse![264; 0 => -2, 1 => 4, 3 => 1, 7 => -1, 10 => -1, 21 => 4, 32 => 1, 43 => -3, 65 => -2, 87 => 2, 131 => 2, 263 => -1],
  sparse![264; 0 => -2, 1 => 4, 2 => 1, 3 => -1, 5 => -2, 7 => 1, 10 => 1, 11 => 2, 23 => -1, 43 => -1, 87 => 2],
  sparse![264; 0 => -1, 1 => -2, 2 => 3, 3 => 7, 5 => -1, 7 => -3, 10 => 1, 11 => -2, 21 => -2, 23 => 1, 32 => -3, 43 => -1, 65 => 7, 87 => 3, 131 => -2, 263 => -1],
  sparse![264; 0 => -1, 1 => -1, 2 => 1, 3 => 6, 7 => -2, 10 => 1, 11 => -2, 21 => 2, 23 => 1, 32 => -1, 43 => -2, 65 => 1, 87 => 1],
  sparse![264; 0 => -1, 1 => -1, 2 => 1, 3 => 7, 7 => -3, 10 => -1, 11 => -2, 21 => -1, 23 => 1, 32 => 1, 43 => 7, 87 => -3, 131 => -2, 263 => 1],
  sparse![264; 0 => -1, 1 => -1, 2 => 2, 3 => 5, 5 => -1, 7 => -2, 10 => 1, 131 => -1, 263 => 2],
  sparse![264; 0 => -1, 1 => -1, 2 => 2, 3 => 5, 7 => -2, 11 => -2, 21 => 2, 23 => 1, 32 => -1, 43 => -2, 65 => 1, 87 => 1, 131 => 1],
  sparse![264; 0 => -1, 2 => 1, 3 => 3, 5 => 1, 7 => -1, 10 => 1, 11 => -2, 21 => 1, 23 => 1, 32 => -1, 43 => -2, 87 => 1, 131 => 3, 263 => -1],
  sparse![264; 0 => -1, 2 => 2, 3 => 1, 5 => -1, 10 => 4, 11 => 1, 21 => -2, 32 => -1, 65 => 1],
  sparse![264; 0 => -1, 2 => 2, 3 => 2, 5 => -1, 10 => 1, 65 => -1, 131 => 2],
]
```

### Level 265

dim S₂ = **25**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **54**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 266

dim S₂ = **37**; eta rank = **18**; full eta basis = **NO**; Sturm bound B = **80**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![266; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![266; 18 => 1, 37 => 1, 132 => 1, 265 => 1],
  sparse![266; 0 => 3, 1 => -1, 18 => -1, 37 => 3],
  sparse![266; 0 => -1, 1 => 3, 18 => 3, 37 => -1],
  sparse![266; 6 => 3, 13 => -1, 132 => -1, 265 => 3],
  sparse![266; 6 => -1, 13 => 3, 132 => 3, 265 => -1],
  sparse![266; 0 => -1, 1 => 2, 6 => -1, 13 => 2, 18 => 2, 37 => -1, 132 => 2, 265 => -1],
  sparse![266; 0 => -1, 1 => 2, 6 => 2, 13 => -1, 18 => 1, 265 => 1],
  sparse![266; 1 => 1, 6 => 1, 18 => 2, 37 => -1, 132 => -1, 265 => 2],
  sparse![266; 0 => -1, 1 => 2, 6 => 1, 37 => 1, 132 => 2, 265 => -1],
  sparse![266; 1 => 1, 13 => 1, 18 => 1, 132 => 1],
  sparse![266; 0 => 1, 6 => -1, 13 => 2, 18 => 2, 37 => -1, 265 => 1],
  sparse![266; 1 => 1, 6 => 2, 13 => -1, 18 => -1, 37 => 2, 132 => 1],
  sparse![266; 0 => 1, 6 => 1, 37 => 1, 265 => 1],
  sparse![266; 0 => 2, 1 => -1, 13 => 1, 18 => 1, 132 => -1, 265 => 2],
  sparse![266; 0 => 1, 13 => 1, 18 => -1, 37 => 2, 132 => 2, 265 => -1],
  sparse![266; 0 => 2, 1 => -1, 6 => -1, 13 => 2, 37 => 1, 132 => 1],
  sparse![266; 0 => 2, 1 => -1, 6 => 2, 13 => -1, 18 => -1, 37 => 2, 132 => -1, 265 => 2],
]
```

### Level 267

dim S₂ = **29**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **60**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![267; 0 => 1, 2 => 1, 88 => 1, 266 => 1],
]
```

### Level 268

dim S₂ = **32**; eta rank = **6**; full eta basis = **NO**; Sturm bound B = **68**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![268; 0 => 3, 1 => -1, 66 => -1, 133 => 3],
  sparse![268; 0 => -1, 1 => 3, 66 => 3, 133 => -1],
  sparse![268; 1 => 3, 3 => -1, 133 => -1, 267 => 3],
  sparse![268; 1 => -1, 3 => 3, 133 => 3, 267 => -1],
  sparse![268; 0 => 1, 3 => 1, 66 => -3, 133 => 8, 267 => -3],
  sparse![268; 0 => -3, 1 => 8, 3 => -3, 66 => 1, 267 => 1],
]
```

### Level 269

dim S₂ = **22**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **45**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 270

dim S₂ = **43**; eta rank = **43**; full eta basis = **YES**; Sturm bound B = **108**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![270; 0 => -3, 1 => 3, 2 => 5, 4 => 4, 5 => -3, 8 => -1, 9 => -2, 14 => -1, 17 => 1, 29 => 1],
  sparse![270; 0 => -3, 1 => 3, 2 => 6, 4 => 2, 5 => -3, 8 => -2, 9 => -1, 14 => -2, 17 => 1, 29 => 1, 44 => 3, 89 => -1],
  sparse![270; 0 => -3, 1 => 4, 2 => 4, 4 => 1, 5 => -2, 8 => 1, 9 => -1, 14 => -1, 29 => 1],
  sparse![270; 0 => -3, 1 => 4, 2 => 4, 4 => 3, 5 => -3, 8 => -1, 9 => -2, 14 => -1, 17 => 1, 29 => 2],
  sparse![270; 0 => -2, 1 => 1, 2 => 3, 4 => 4, 5 => -1, 8 => 2, 9 => -2, 17 => -1, 44 => -1, 89 => 1],
  sparse![270; 0 => -2, 1 => 1, 2 => 3, 4 => 4, 8 => 1, 9 => -2, 14 => -1, 17 => -1, 44 => -1, 89 => 2],
  sparse![270; 0 => -2, 1 => 1, 2 => 4, 4 => 4, 5 => -2, 8 => 1, 9 => -2, 14 => -1, 29 => 1],
  sparse![270; 0 => -2, 1 => 1, 2 => 4, 4 => 4, 5 => -1, 8 => -2, 9 => -2, 14 => -2, 17 => 2, 29 => 1, 44 => 2, 89 => -1],
  sparse![270; 0 => -2, 1 => 1, 2 => 4, 4 => 4, 5 => -1, 9 => -2, 14 => -2, 29 => 1, 89 => 1],
  sparse![270; 0 => -2, 1 => 1, 2 => 5, 4 => 1, 5 => -2, 9 => 1, 14 => -1, 44 => 1],
  sparse![270; 0 => -2, 1 => 1, 2 => 6, 4 => 1, 5 => -3, 8 => -1, 9 => 1, 14 => -2, 17 => 1, 29 => 1, 44 => 2, 89 => -1],
  sparse![270; 0 => -2, 1 => 1, 2 => 6, 4 => 2, 5 => -3, 8 => -3, 9 => -1, 14 => -3, 17 => 2, 26 => 2, 29 => 2, 44 => 6, 53 => -1, 89 => -3, 134 => -2, 269 => 1],
  sparse![270; 0 => -2, 1 => 1, 2 => 7, 5 => -3, 8 => -2, 14 => -2, 17 => 1, 29 => 1, 44 => 7, 89 => -3, 134 => -2, 269 => 1],
  sparse![270; 0 => -2, 1 => 1, 2 => 7, 5 => -3, 8 => -2, 14 => -2, 17 => 1, 29 => 4, 44 => 1, 89 => -1],
  sparse![270; 0 => -2, 1 => 1, 2 => 7, 5 => -3, 8 => -2, 14 => -1, 17 => 1, 29 => 2, 134 => 2, 269 => -1],
  sparse![270; 0 => -2, 1 => 2, 2 => 2, 4 => 3, 5 => -1, 8 => 2, 9 => -2, 17 => -1, 29 => 1, 44 => -1, 89 => 1],
  sparse![270; 0 => -2, 1 => 2, 2 => 2, 4 => 3, 8 => 1, 9 => -2, 14 => -1, 17 => -1, 29 => 1, 44 => -1, 89 => 2],
  sparse![270; 0 => -2, 1 => 2, 2 => 3, 4 => 3, 5 => -2, 8 => 1, 9 => -2, 14 => -1, 29 => 2],
  sparse![270; 0 => -2, 1 => 2, 2 => 3, 4 => 3, 5 => -1, 9 => -2, 14 => -2, 29 => 2, 89 => 1],
  sparse![270; 0 => -2, 1 => 2, 2 => 4, 5 => -2, 8 => -1, 9 => 1, 14 => 1, 17 => 1, 29 => -1, 89 => 1],
  sparse![270; 0 => -2, 1 => 2, 2 => 4, 5 => -2, 9 => 1, 14 => -1, 29 => 1, 44 => 1],
  sparse![270; 0 => -2, 1 => 2, 2 => 5, 5 => -3, 8 => -2, 9 => 1, 17 => 2, 44 => 1],
  sparse![270; 0 => -2, 1 => 2, 2 => 5, 5 => -3, 8 => -1, 9 => 1, 14 => -2, 17 => 1, 29 => 2, 44 => 2, 89 => -1],
  sparse![270; 0 => -2, 1 => 2, 2 => 5, 4 => 1, 5 => -3, 8 => -3, 9 => -1, 14 => -3, 17 => 2, 26 => 2, 29 => 3, 44 => 6, 53 => -1, 89 => -3, 134 => -2, 269 => 1],
  sparse![270; 0 => -2, 1 => 3, 2 => 1, 4 => 2, 5 => -1, 8 => 2, 9 => -2, 17 => -1, 29 => 2, 44 => -1, 89 => 1],
  sparse![270; 0 => -2, 1 => 3, 2 => 1, 4 => 2, 8 => 1, 9 => -2, 14 => -1, 17 => -1, 29 => 2, 44 => -1, 89 => 2],
  sparse![270; 0 => -2, 1 => 3, 2 => 2, 4 => 1, 5 => -1, 14 => -2, 29 => 3, 44 => 1, 89 => -1],
  sparse![270; 0 => -2, 1 => 3, 2 => 2, 4 => 1, 5 => -1, 14 => -1, 29 => 1, 134 => 2, 269 => -1],
  sparse![270; 0 => -2, 1 => 3, 2 => 2, 4 => 2, 5 => -2, 8 => 1, 9 => -2, 14 => -1, 29 => 3],
  sparse![270; 0 => -2, 1 => 4, 4 => 1, 5 => -1, 8 => 2, 9 => -2, 17 => -1, 29 => 3, 44 => -1, 89 => 1],
  sparse![270; 0 => -2, 1 => 4, 4 => 1, 8 => 1, 9 => -2, 14 => -1, 17 => -1, 29 => 3, 44 => -1, 89 => 2],
  sparse![270; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 14 => -2, 29 => 1, 44 => 7, 89 => -3, 134 => -2, 269 => 1],
  sparse![270; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 14 => -2, 29 => 4, 44 => 1, 89 => -1],
  sparse![270; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 14 => -1, 29 => 2, 134 => 2, 269 => -1],
  sparse![270; 0 => -2, 1 => 4, 2 => 1, 4 => 1, 5 => -2, 8 => -1, 9 => -2, 14 => -1, 17 => 2, 29 => 4, 44 => 2, 89 => -2],
  sparse![270; 0 => -2, 1 => 4, 2 => 1, 4 => 1, 5 => -2, 8 => 1, 9 => -2, 14 => -1, 29 => 4],
  sparse![270; 0 => -1, 1 => 1, 4 => 3, 9 => -1, 26 => 3, 53 => -1, 134 => -1, 269 => 1],
  sparse![270; 0 => -1, 1 => 1, 2 => 1, 9 => 2, 26 => 2, 53 => -1],
  sparse![270; 0 => -1, 1 => 1, 2 => 1, 4 => 1, 14 => -1, 26 => 2, 29 => 1, 44 => 2, 53 => -1, 89 => -1],
  sparse![270; 0 => -1, 1 => 1, 2 => 1, 4 => 1, 14 => -1, 17 => 1, 26 => 1, 29 => 1, 44 => 1, 53 => -1, 89 => -1, 269 => 1],
  sparse![270; 0 => -1, 1 => 1, 2 => 2, 4 => -1, 5 => -1, 8 => 2, 9 => 1, 14 => 2, 17 => -1, 26 => -1, 29 => -1, 44 => 2, 53 => 1, 89 => -1, 134 => -1, 269 => 1],
  sparse![270; 0 => -1, 1 => 1, 2 => 3, 4 => 2, 5 => -3, 8 => -3, 9 => -2, 14 => -3, 17 => 5, 26 => 2, 29 => 5, 44 => 3, 53 => -2, 89 => -3, 134 => -1, 269 => 1],
  sparse![270; 0 => -1, 1 => 2, 2 => -1, 5 => 1, 8 => 2, 14 => 2, 17 => -1, 26 => -1, 29 => -1, 53 => 1, 134 => 1],
]
```

### Level 271

dim S₂ = **22**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **45**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 272

dim S₂ = **31**; eta rank = **30**; full eta basis = **NO**; Sturm bound B = **72**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![272; 0 => 2, 1 => -1, 3 => 1, 16 => -2, 33 => 5, 67 => -1],
  sparse![272; 0 => 1, 1 => -1, 3 => 2, 16 => -1, 33 => 5, 67 => -2],
  sparse![272; 0 => 1, 1 => 2, 3 => -1, 16 => -1, 33 => 2, 67 => 1],
  sparse![272; 1 => 2, 33 => 2],
  sparse![272; 0 => -1, 1 => 2, 3 => 1, 16 => 1, 33 => 2, 67 => -1],
  sparse![272; 0 => -1, 1 => 5, 3 => -2, 16 => 1, 33 => -1, 67 => 2],
  sparse![272; 0 => -2, 1 => 5, 3 => -1, 16 => 2, 33 => -1, 67 => 1],
  sparse![272; 1 => 2, 3 => -1, 7 => 1, 33 => -2, 67 => 5, 135 => -1],
  sparse![272; 1 => 1, 3 => -1, 7 => 2, 33 => -1, 67 => 5, 135 => -2],
  sparse![272; 3 => 2, 67 => 2],
  sparse![272; 1 => -1, 3 => 2, 7 => 1, 33 => 1, 67 => 2, 135 => -1],
  sparse![272; 3 => 2, 7 => -1, 15 => 1, 67 => -2, 135 => 5, 271 => -1],
  sparse![272; 3 => 1, 7 => -1, 15 => 2, 67 => -1, 135 => 5, 271 => -2],
  sparse![272; 7 => 2, 135 => 2],
  sparse![272; 3 => -1, 7 => 2, 15 => 1, 67 => 1, 135 => 2, 271 => -1],
  sparse![272; 0 => -1, 1 => 1, 3 => 3, 7 => -1, 16 => 1, 33 => -1, 67 => 1, 135 => 1],
  sparse![272; 0 => -1, 1 => 3, 3 => 1, 7 => -1, 16 => 1, 33 => 1, 67 => -1, 135 => 1],
  sparse![272; 1 => -1, 3 => 1, 7 => 3, 15 => -1, 33 => 1, 67 => -1, 135 => 1, 271 => 1],
  sparse![272; 1 => -1, 3 => 3, 7 => 1, 15 => -1, 33 => 1, 67 => 1, 135 => -1, 271 => 1],
  sparse![272; 0 => 1, 1 => -1, 3 => 2, 16 => 1, 67 => -2, 135 => 5, 271 => -2],
  sparse![272; 3 => 2, 7 => -1, 15 => 1, 16 => -2, 33 => 5, 67 => -2, 271 => 1],
  sparse![272; 0 => -1, 1 => 3, 7 => -1, 15 => 1, 16 => -1, 33 => 2, 271 => 1],
  sparse![272; 0 => 1, 1 => -1, 7 => 3, 15 => -1, 16 => 1, 135 => 2, 271 => -1],
  sparse![272; 0 => -3, 1 => 8, 3 => -3, 16 => -1, 33 => 2, 67 => 1],
  sparse![272; 0 => -2, 1 => 5, 3 => -3, 7 => 3, 15 => -1, 67 => 1, 135 => 2, 271 => -1],
  sparse![272; 0 => -2, 1 => 5, 3 => -2, 15 => 1, 67 => 2, 135 => -1, 271 => 1],
  sparse![272; 0 => -2, 1 => 5, 3 => -1, 16 => -2, 33 => 5, 67 => -1],
  sparse![272; 0 => -1, 1 => 2, 3 => -1, 7 => 3, 15 => -1, 16 => -1, 33 => 3, 67 => -1, 135 => 2, 271 => -1],
  sparse![272; 0 => -1, 1 => 2, 15 => 1, 16 => -1, 33 => 3, 135 => -1, 271 => 1],
  sparse![272; 0 => -1, 1 => 2, 3 => 1, 16 => -3, 33 => 8, 67 => -3],
]
```

### Level 273

dim S₂ = **33**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **74**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 274

dim S₂ = **33**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **69**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 275

dim S₂ = **25**; eta rank = **13**; full eta basis = **NO**; Sturm bound B = **60**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![275; 0 => 2, 10 => 2],
  sparse![275; 4 => 2, 54 => 2],
  sparse![275; 24 => 2, 274 => 2],
  sparse![275; 0 => 1, 4 => 1, 10 => 1, 54 => 1],
  sparse![275; 4 => 1, 24 => 1, 54 => 1, 274 => 1],
  sparse![275; 0 => 1, 4 => 1, 54 => 1, 274 => 1],
  sparse![275; 4 => 1, 10 => 1, 24 => 1, 54 => 1],
  sparse![275; 0 => 1, 24 => 1, 274 => 2],
  sparse![275; 0 => 2, 274 => 2],
  sparse![275; 10 => 1, 24 => 2, 274 => 1],
  sparse![275; 0 => 1, 10 => 1, 24 => 1, 274 => 1],
  sparse![275; 0 => 2, 10 => 1, 274 => 1],
  sparse![275; 0 => 1, 10 => 2, 24 => 1],
]
```

### Level 276

dim S₂ = **43**; eta rank = **43**; full eta basis = **YES**; Sturm bound B = **96**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![276; 0 => 2, 22 => 2],
  sparse![276; 1 => 2, 45 => 2],
  sparse![276; 2 => 2, 68 => 2],
  sparse![276; 3 => 2, 91 => 2],
  sparse![276; 5 => 2, 137 => 2],
  sparse![276; 11 => 2, 275 => 2],
  sparse![276; 0 => -1, 1 => 3, 22 => -1, 45 => 3],
  sparse![276; 0 => 1, 1 => 1, 22 => 1, 45 => 1],
  sparse![276; 0 => 3, 1 => -1, 22 => 3, 45 => -1],
  sparse![276; 1 => -1, 3 => 3, 45 => -1, 91 => 3],
  sparse![276; 1 => 1, 3 => 1, 45 => 1, 91 => 1],
  sparse![276; 2 => -1, 5 => 3, 68 => -1, 137 => 3],
  sparse![276; 2 => 1, 5 => 1, 68 => 1, 137 => 1],
  sparse![276; 2 => 3, 5 => -1, 68 => 3, 137 => -1],
  sparse![276; 5 => -1, 11 => 3, 137 => -1, 275 => 3],
  sparse![276; 5 => 1, 11 => 1, 137 => 1, 275 => 1],
  sparse![276; 0 => 1, 2 => 1, 22 => 1, 68 => 1],
  sparse![276; 1 => 1, 5 => 1, 45 => 1, 137 => 1],
  sparse![276; 3 => 1, 11 => 1, 91 => 1, 275 => 1],
  sparse![276; 0 => 1, 1 => -1, 3 => 2, 22 => 1, 45 => -1, 91 => 2],
  sparse![276; 2 => 1, 5 => -1, 11 => 2, 68 => 1, 137 => -1, 275 => 2],
  sparse![276; 0 => 1, 1 => -1, 2 => -2, 5 => 4, 22 => 1, 45 => -1, 68 => -2, 137 => 4],
  sparse![276; 0 => 1, 1 => -1, 2 => -1, 5 => 3, 22 => 1, 45 => -1, 68 => -1, 137 => 3],
  sparse![276; 0 => -1, 1 => 1, 2 => 2, 22 => -1, 45 => 1, 68 => 2],
  sparse![276; 0 => 1, 1 => -1, 5 => 2, 22 => 1, 45 => -1, 137 => 2],
  sparse![276; 1 => 1, 3 => -1, 5 => -2, 11 => 4, 45 => 1, 91 => -1, 137 => -2, 275 => 4],
  sparse![276; 1 => 1, 3 => -1, 5 => -1, 11 => 3, 45 => 1, 91 => -1, 137 => -1, 275 => 3],
  sparse![276; 1 => -1, 3 => 1, 5 => 2, 45 => -1, 91 => 1, 137 => 2],
  sparse![276; 2 => 1, 3 => 1, 5 => 1, 11 => -1, 68 => 1, 91 => 1, 137 => 1, 275 => -1],
  sparse![276; 0 => -1, 2 => 3, 3 => 1, 11 => -1, 275 => 2],
  sparse![276; 0 => 3, 2 => -1, 3 => -1, 11 => 1, 91 => 2],
  sparse![276; 0 => 1, 2 => -1, 3 => -1, 11 => 3, 68 => 2],
  sparse![276; 0 => -1, 2 => 1, 3 => 3, 11 => -1, 22 => 2],
  sparse![276; 2 => 3, 5 => -1, 22 => 1, 91 => -1, 137 => -1, 275 => 3],
  sparse![276; 5 => -1, 11 => 3, 22 => -1, 68 => 3, 91 => 1, 137 => -1],
  sparse![276; 0 => 1, 11 => 1, 22 => 1, 275 => 1],
  sparse![276; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 11 => 1, 22 => -2, 45 => 3, 68 => 3, 91 => -1, 137 => -1],
  sparse![276; 0 => -4, 1 => 10, 2 => 2, 3 => -4, 5 => -4, 11 => 2, 68 => -2, 137 => 6, 275 => -2],
  sparse![276; 0 => -3, 1 => 7, 2 => 2, 3 => -2, 5 => -3, 11 => 1, 22 => 1, 45 => -3, 68 => -2, 91 => 2, 137 => 7, 275 => -3],
  sparse![276; 0 => -3, 1 => 8, 3 => -3, 22 => -1, 45 => 1, 68 => 2, 137 => 1, 275 => -1],
  sparse![276; 0 => -3, 1 => 8, 2 => 1, 3 => -3, 5 => -3, 11 => 2, 22 => -1, 45 => 1, 68 => 3, 137 => -2, 275 => 1],
  sparse![276; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -2, 11 => 1, 22 => 2, 45 => 1, 68 => -1, 91 => -1, 275 => 1],
  sparse![276; 0 => -2, 1 => 7, 2 => 1, 3 => -3, 5 => -3, 11 => 2, 22 => 2, 45 => -3, 68 => -3, 91 => 1, 137 => 7, 275 => -2],
]
```

### Level 277

dim S₂ = **22**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **46**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 278

dim S₂ = **34**; eta rank = **2**; full eta basis = **NO**; Sturm bound B = **70**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![278; 0 => 3, 1 => -1, 138 => -1, 277 => 3],
  sparse![278; 0 => -1, 1 => 3, 138 => 3, 277 => -1],
]
```

### Level 279

dim S₂ = **29**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **64**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![279; 0 => 1, 8 => 1, 30 => -1, 92 => 4, 278 => -1],
  sparse![279; 2 => 2, 92 => 2],
  sparse![279; 0 => -1, 2 => 4, 8 => -1, 30 => 1, 278 => 1],
]
```

### Level 280

dim S₂ = **41**; eta rank = **41**; full eta basis = **YES**; Sturm bound B = **96**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![280; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![280; 1 => 1, 3 => 1, 13 => 1, 27 => 1],
  sparse![280; 3 => 1, 7 => 1, 27 => 1, 55 => 1],
  sparse![280; 4 => 1, 9 => 1, 34 => 1, 69 => 1],
  sparse![280; 9 => 1, 19 => 1, 69 => 1, 139 => 1],
  sparse![280; 19 => 1, 39 => 1, 139 => 1, 279 => 1],
  sparse![280; 1 => 2, 9 => 2],
  sparse![280; 3 => 2, 19 => 2],
  sparse![280; 13 => 2, 69 => 2],
  sparse![280; 27 => 2, 139 => 2],
  sparse![280; 0 => 2, 34 => 2],
  sparse![280; 0 => 1, 4 => 1, 6 => 1, 34 => 1],
  sparse![280; 4 => 2, 6 => 2],
  sparse![280; 1 => 2, 69 => 2],
  sparse![280; 1 => 1, 9 => 1, 13 => 1, 69 => 1],
  sparse![280; 9 => 2, 13 => 2],
  sparse![280; 3 => 2, 139 => 2],
  sparse![280; 3 => 1, 19 => 1, 27 => 1, 139 => 1],
  sparse![280; 19 => 2, 27 => 2],
  sparse![280; 7 => 2, 279 => 2],
  sparse![280; 7 => 1, 39 => 1, 55 => 1, 279 => 1],
  sparse![280; 39 => 2, 55 => 2],
  sparse![280; 0 => -2, 1 => 5, 3 => -1, 4 => 2, 9 => -1, 19 => 1],
  sparse![280; 6 => -2, 13 => 5, 27 => -1, 34 => 2, 69 => -1, 139 => 1],
  sparse![280; 0 => 1, 6 => 1, 7 => 1, 55 => 1],
  sparse![280; 1 => -1, 3 => 3, 13 => 3, 27 => -1],
  sparse![280; 4 => 1, 34 => 1, 39 => 1, 279 => 1],
  sparse![280; 9 => -1, 19 => 3, 69 => 3, 139 => -1],
  sparse![280; 0 => 1, 4 => 2, 9 => -1, 13 => 1, 34 => -1, 69 => 2],
  sparse![280; 1 => 1, 9 => 2, 19 => -1, 27 => 1, 69 => -1, 139 => 2],
  sparse![280; 3 => 1, 19 => 2, 39 => -1, 55 => 1, 139 => -1, 279 => 2],
  sparse![280; 0 => 1, 6 => 1, 19 => 1, 139 => 1],
  sparse![280; 0 => -2, 1 => 4, 3 => -1, 4 => 2, 9 => -1, 13 => 2, 27 => -1, 69 => 1],
  sparse![280; 1 => 1, 13 => 1, 39 => 1, 279 => 1],
  sparse![280; 1 => -2, 3 => 4, 7 => -1, 9 => 2, 19 => -1, 27 => 2, 55 => -1, 139 => 1],
  sparse![280; 0 => 2, 1 => -1, 3 => 1, 34 => 2, 69 => -1, 139 => 1],
  sparse![280; 4 => 2, 6 => 2, 9 => -1, 13 => -1, 19 => 1, 27 => 1],
  sparse![280; 1 => 1, 3 => -1, 7 => 2, 69 => 1, 139 => -1, 279 => 2],
  sparse![280; 9 => 1, 13 => 1, 19 => -1, 27 => -1, 39 => 2, 55 => 2],
  sparse![280; 1 => 1, 3 => 1, 69 => 1, 139 => 1],
  sparse![280; 1 => 1, 19 => 1, 27 => 1, 69 => 1],
]
```

### Level 281

dim S₂ = **23**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **47**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 282

dim S₂ = **45**; eta rank = **28**; full eta basis = **NO**; Sturm bound B = **96**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![282; 0 => 2, 46 => 2],
  sparse![282; 1 => 2, 93 => 2],
  sparse![282; 2 => 2, 140 => 2],
  sparse![282; 5 => 2, 281 => 2],
  sparse![282; 0 => -1, 1 => 3, 46 => -1, 93 => 3],
  sparse![282; 0 => 1, 1 => 1, 46 => 1, 93 => 1],
  sparse![282; 0 => 3, 1 => -1, 46 => 3, 93 => -1],
  sparse![282; 2 => -1, 5 => 3, 140 => -1, 281 => 3],
  sparse![282; 2 => 1, 5 => 1, 140 => 1, 281 => 1],
  sparse![282; 2 => 3, 5 => -1, 140 => 3, 281 => -1],
  sparse![282; 0 => 1, 2 => 1, 46 => 1, 140 => 1],
  sparse![282; 1 => 1, 5 => 1, 93 => 1, 281 => 1],
  sparse![282; 0 => 1, 1 => -1, 2 => -2, 5 => 4, 46 => 1, 93 => -1, 140 => -2, 281 => 4],
  sparse![282; 0 => 1, 1 => -1, 2 => -1, 5 => 3, 46 => 1, 93 => -1, 140 => -1, 281 => 3],
  sparse![282; 0 => -1, 1 => 1, 2 => 2, 46 => -1, 93 => 1, 140 => 2],
  sparse![282; 0 => 1, 1 => -1, 5 => 2, 46 => 1, 93 => -1, 281 => 2],
  sparse![282; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 46 => -1, 93 => 1, 140 => 3, 281 => -1],
  sparse![282; 0 => -1, 1 => 1, 2 => 4, 5 => -2, 46 => -1, 93 => 1, 140 => 4, 281 => -2],
  sparse![282; 0 => -1, 1 => 2, 5 => 1, 46 => -1, 93 => 2, 281 => 1],
  sparse![282; 1 => 1, 2 => -1, 5 => 2, 93 => 1, 140 => -1, 281 => 2],
  sparse![282; 0 => -1, 1 => 2, 2 => 1, 46 => -1, 93 => 2, 140 => 1],
  sparse![282; 0 => 1, 2 => -1, 5 => 2, 46 => 1, 140 => -1, 281 => 2],
  sparse![282; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 46 => -2, 93 => 3, 140 => 3, 281 => -2],
  sparse![282; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 46 => -1, 93 => 2, 140 => 2, 281 => -1],
  sparse![282; 1 => 1, 2 => 1, 93 => 1, 140 => 1],
  sparse![282; 0 => 1, 5 => 1, 46 => 1, 281 => 1],
  sparse![282; 0 => 2, 1 => -1, 2 => -1, 5 => 2, 46 => 2, 93 => -1, 140 => -1, 281 => 2],
  sparse![282; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 46 => 3, 93 => -2, 140 => -2, 281 => 3],
]
```

### Level 283

dim S₂ = **23**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **47**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 284

dim S₂ = **34**; eta rank = **18**; full eta basis = **NO**; Sturm bound B = **72**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![284; 0 => 2, 70 => 2],
  sparse![284; 1 => 2, 141 => 2],
  sparse![284; 3 => 2, 283 => 2],
  sparse![284; 0 => -1, 1 => 3, 70 => -1, 141 => 3],
  sparse![284; 0 => 1, 1 => 1, 70 => 1, 141 => 1],
  sparse![284; 0 => 3, 1 => -1, 70 => 3, 141 => -1],
  sparse![284; 1 => -1, 3 => 3, 141 => -1, 283 => 3],
  sparse![284; 1 => 1, 3 => 1, 141 => 1, 283 => 1],
  sparse![284; 1 => 3, 3 => -1, 141 => 3, 283 => -1],
  sparse![284; 0 => 1, 1 => -1, 3 => 2, 70 => 1, 141 => -1, 283 => 2],
  sparse![284; 0 => -1, 1 => 2, 3 => 1, 70 => -1, 141 => 2, 283 => 1],
  sparse![284; 0 => 1, 3 => 1, 70 => 1, 283 => 1],
  sparse![284; 0 => 2, 1 => -1, 3 => 1, 70 => 2, 141 => -1, 283 => 1],
  sparse![284; 0 => -2, 1 => 5, 3 => -1, 70 => -2, 141 => 5, 283 => -1],
  sparse![284; 0 => -1, 1 => 4, 3 => -1, 70 => -1, 141 => 4, 283 => -1],
  sparse![284; 0 => 1, 1 => 2, 3 => -1, 70 => 1, 141 => 2, 283 => -1],
  sparse![284; 0 => -2, 1 => 6, 3 => -2, 70 => -2, 141 => 6, 283 => -2],
  sparse![284; 0 => -1, 1 => 5, 3 => -2, 70 => -1, 141 => 5, 283 => -2],
]
```

### Level 285

dim S₂ = **37**; eta rank = **14**; full eta basis = **NO**; Sturm bound B = **80**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![285; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![285; 18 => 1, 56 => 1, 94 => 1, 284 => 1],
  sparse![285; 0 => 2, 94 => 2],
  sparse![285; 0 => 1, 4 => 1, 18 => 1, 94 => 1],
  sparse![285; 4 => 2, 18 => 2],
  sparse![285; 2 => 2, 284 => 2],
  sparse![285; 2 => 1, 14 => 1, 56 => 1, 284 => 1],
  sparse![285; 14 => 2, 56 => 2],
  sparse![285; 0 => 1, 2 => 1, 94 => 1, 284 => 1],
  sparse![285; 0 => -1, 2 => 2, 4 => 2, 14 => -1, 18 => 2, 56 => -1, 94 => -1, 284 => 2],
  sparse![285; 2 => 1, 4 => 1, 18 => 1, 284 => 1],
  sparse![285; 0 => 1, 14 => 1, 56 => 1, 94 => 1],
  sparse![285; 0 => 2, 2 => -1, 4 => -1, 14 => 2, 18 => -1, 56 => 2, 94 => 2, 284 => -1],
  sparse![285; 4 => 1, 14 => 1, 18 => 1, 56 => 1],
]
```

### Level 286

dim S₂ = **39**; eta rank = **33**; full eta basis = **NO**; Sturm bound B = **84**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![286; 0 => 2, 10 => 2],
  sparse![286; 1 => 2, 21 => 2],
  sparse![286; 12 => 2, 142 => 2],
  sparse![286; 25 => 2, 285 => 2],
  sparse![286; 0 => 2, 142 => 2],
  sparse![286; 0 => 1, 10 => 1, 12 => 1, 142 => 1],
  sparse![286; 10 => 2, 12 => 2],
  sparse![286; 1 => 2, 285 => 2],
  sparse![286; 1 => 1, 21 => 1, 25 => 1, 285 => 1],
  sparse![286; 21 => 2, 25 => 2],
  sparse![286; 0 => -1, 1 => 3, 142 => -1, 285 => 3],
  sparse![286; 0 => 1, 1 => 1, 142 => 1, 285 => 1],
  sparse![286; 0 => 3, 1 => -1, 142 => 3, 285 => -1],
  sparse![286; 0 => 1, 10 => 2, 21 => -1, 25 => 1, 142 => -1, 285 => 2],
  sparse![286; 0 => 2, 1 => -1, 10 => 2, 21 => -1, 25 => 1, 285 => 1],
  sparse![286; 0 => 1, 10 => 1, 12 => -1, 25 => 2, 142 => -1, 285 => 2],
  sparse![286; 0 => 2, 1 => -1, 10 => 1, 12 => -1, 25 => 2, 285 => 1],
  sparse![286; 0 => -1, 1 => 2, 10 => 2, 12 => 2, 21 => -1, 25 => -1, 142 => -1, 285 => 2],
  sparse![286; 1 => 1, 10 => 2, 12 => 2, 21 => -1, 25 => -1, 285 => 1],
  sparse![286; 0 => 1, 10 => 2, 12 => 2, 21 => -1, 25 => -1, 142 => 1],
  sparse![286; 0 => -1, 1 => 2, 10 => 1, 12 => 1, 142 => -1, 285 => 2],
  sparse![286; 1 => 1, 10 => 1, 12 => 1, 285 => 1],
  sparse![286; 0 => 2, 1 => -1, 10 => 1, 12 => 1, 142 => 2, 285 => -1],
  sparse![286; 0 => -1, 1 => 2, 21 => 1, 25 => 1, 142 => -1, 285 => 2],
  sparse![286; 0 => 1, 21 => 1, 25 => 1, 142 => 1],
  sparse![286; 0 => 2, 1 => -1, 21 => 1, 25 => 1, 142 => 2, 285 => -1],
  sparse![286; 1 => 1, 10 => -1, 12 => -1, 21 => 2, 25 => 2, 285 => 1],
  sparse![286; 0 => 1, 10 => -1, 12 => -1, 21 => 2, 25 => 2, 142 => 1],
  sparse![286; 0 => 2, 1 => -1, 10 => -1, 12 => -1, 21 => 2, 25 => 2, 142 => 2, 285 => -1],
  sparse![286; 0 => -1, 1 => 2, 12 => 2, 21 => 1, 25 => -1, 142 => 1],
  sparse![286; 1 => 1, 12 => 2, 21 => 1, 25 => -1, 142 => 2, 285 => -1],
  sparse![286; 0 => -1, 1 => 2, 10 => -1, 12 => 1, 21 => 2, 142 => 1],
  sparse![286; 10 => 3, 12 => 3, 21 => -1, 25 => -1],
]
```

### Level 287

dim S₂ = **27**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **56**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![287; 0 => 2, 286 => 2],
  sparse![287; 0 => 1, 6 => 1, 40 => 1, 286 => 1],
  sparse![287; 6 => 2, 40 => 2],
]
```

### Level 288

dim S₂ = **33**; eta rank = **33**; full eta basis = **YES**; Sturm bound B = **96**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![288; 0 => -6, 1 => 15, 2 => 2, 3 => -7, 5 => -5, 7 => 2, 11 => 3],
  sparse![288; 0 => -6, 1 => 15, 2 => 2, 3 => -6, 5 => -5, 11 => 2, 23 => 1, 35 => 2, 71 => -1],
  sparse![288; 0 => -5, 1 => 12, 2 => 3, 3 => -6, 5 => -6, 7 => 1, 11 => 6, 23 => -1],
  sparse![288; 0 => -4, 1 => 8, 2 => 4, 3 => -4, 5 => -4, 7 => 2, 11 => 2],
  sparse![288; 0 => -4, 1 => 8, 2 => 4, 3 => -3, 5 => -4, 11 => 1, 23 => 1, 35 => 2, 71 => -1],
  sparse![288; 0 => -4, 1 => 9, 2 => 3, 3 => -4, 5 => -4, 7 => 1, 8 => -1, 11 => 1, 17 => 1, 23 => 2, 35 => 1, 71 => -1],
  sparse![288; 0 => -4, 1 => 10, 3 => -4, 11 => 2],
  sparse![288; 0 => -4, 1 => 10, 2 => 2, 3 => -6, 5 => -5, 7 => 3, 11 => 6, 15 => -1, 23 => -2, 47 => 1],
  sparse![288; 0 => -3, 1 => 3, 2 => 7, 3 => -1, 5 => -4, 7 => 2, 8 => -2, 11 => 1, 17 => 1],
  sparse![288; 0 => -3, 1 => 3, 2 => 7, 5 => -4, 8 => -2, 17 => 1, 23 => 1, 35 => 2, 71 => -1],
  sparse![288; 0 => -3, 1 => 5, 2 => 4, 3 => -2, 5 => -3, 7 => 2, 8 => -1, 11 => 1, 35 => 1],
  sparse![288; 0 => -3, 1 => 5, 2 => 4, 3 => -1, 5 => -3, 8 => -1, 23 => 1, 35 => 3, 71 => -1],
  sparse![288; 0 => -3, 1 => 6, 2 => 1, 3 => -1, 7 => -1, 15 => 2, 23 => 1, 31 => -1, 47 => -1, 95 => 1],
  sparse![288; 0 => -3, 1 => 6, 2 => 1, 3 => 1, 5 => -2, 7 => -2, 11 => 1, 23 => 2],
  sparse![288; 0 => -3, 1 => 6, 2 => 3, 3 => -4, 5 => -3, 7 => 4, 11 => 2, 15 => -1, 23 => -1, 47 => 1],
  sparse![288; 0 => -3, 1 => 6, 2 => 3, 3 => -3, 5 => -3, 7 => 2, 11 => 1, 15 => -1, 35 => 2, 47 => 1, 71 => -1],
  sparse![288; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -1, 23 => 2],
  sparse![288; 0 => -2, 1 => 1, 2 => 2, 3 => 6, 5 => -1, 7 => -3, 23 => 1],
  sparse![288; 0 => -2, 1 => 1, 2 => 5, 5 => -1, 8 => -1, 11 => 3, 23 => -1, 35 => -1, 71 => 1],
  sparse![288; 0 => -2, 1 => 1, 2 => 5, 5 => -1, 7 => 2, 8 => -1, 15 => -1, 143 => 1],
  sparse![288; 0 => -2, 1 => 1, 2 => 6, 3 => -1, 5 => -3, 7 => 2, 11 => 1],
  sparse![288; 0 => -2, 1 => 1, 2 => 6, 5 => -3, 7 => 2, 8 => -2, 15 => -1, 17 => 1, 35 => 2, 47 => 1, 71 => -1],
  sparse![288; 0 => -2, 1 => 1, 2 => 8, 5 => -4, 8 => -2, 11 => 2, 17 => 1],
  sparse![288; 0 => -2, 1 => 2, 2 => 2, 3 => 3, 7 => -1, 11 => -1, 23 => 1],
  sparse![288; 0 => -2, 1 => 2, 2 => 4, 5 => -1, 7 => -1, 8 => -2, 15 => 2, 17 => 3, 23 => 1, 31 => -1, 35 => -1, 47 => -1, 95 => 1],
  sparse![288; 0 => -2, 1 => 2, 2 => 5, 5 => -2, 7 => -1, 8 => -1, 15 => 2, 23 => 1, 31 => -1, 35 => 1, 47 => -1, 95 => 1],
  sparse![288; 0 => -2, 1 => 3, 2 => 2, 3 => 1, 5 => -2, 7 => -1, 11 => 1, 17 => -1, 35 => 3, 47 => 2, 71 => -1, 95 => -1, 143 => -1, 287 => 1],
  sparse![288; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -2, 7 => 2, 8 => -1, 15 => -1, 35 => 3, 47 => 1, 71 => -1],
  sparse![288; 0 => -2, 1 => 4, 3 => -1, 5 => 1, 7 => -1, 8 => 2, 15 => 2, 17 => -1, 23 => 1, 31 => -1, 47 => -1, 95 => 1],
  sparse![288; 0 => -2, 1 => 4, 3 => -1, 5 => 1, 7 => 1, 15 => 1, 31 => -1, 95 => 1],
  sparse![288; 0 => -1, 1 => -1, 2 => 1, 3 => 6, 7 => -1, 15 => -1, 47 => 1],
  sparse![288; 0 => -1, 1 => -1, 2 => 3, 3 => 2, 5 => 1, 7 => -1, 11 => -1, 15 => 2, 23 => 1, 31 => -1, 47 => -1, 95 => 1],
  sparse![288; 0 => -1, 2 => 2, 3 => 1, 5 => 1, 8 => -1, 11 => 1, 17 => 1, 23 => -1, 35 => -1, 47 => 2, 71 => 1, 95 => -1, 143 => -1, 287 => 1],
]
```

### Level 289

dim S₂ = **17**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **51**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 290

dim S₂ = **41**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **90**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 291

dim S₂ = **31**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **65**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 292

dim S₂ = **35**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **74**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 293

dim S₂ = **24**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **49**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 294

dim S₂ = **41**; eta rank = **41**; full eta basis = **YES**; Sturm bound B = **112**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![294; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![294; 2 => 1, 5 => 1, 20 => 1, 41 => 1],
  sparse![294; 6 => 1, 13 => 1, 48 => 1, 97 => 1],
  sparse![294; 20 => 1, 41 => 1, 146 => 1, 293 => 1],
  sparse![294; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 6 => 4, 13 => -2, 20 => -1, 41 => 1],
  sparse![294; 0 => -1, 1 => 1, 2 => 4, 5 => -2, 6 => 1, 13 => -1, 20 => -2, 41 => 4],
  sparse![294; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 6 => -1, 13 => 2, 20 => 2, 41 => -1],
  sparse![294; 6 => -2, 13 => 4, 20 => 1, 41 => -1, 48 => 4, 97 => -2, 146 => -1, 293 => 1],
  sparse![294; 6 => -1, 13 => 1, 20 => 4, 41 => -2, 48 => 1, 97 => -1, 146 => -2, 293 => 4],
  sparse![294; 6 => -1, 13 => 2, 20 => 2, 41 => -1, 48 => -1, 97 => 2, 146 => 2, 293 => -1],
  sparse![294; 0 => 2, 1 => -1, 6 => 1, 13 => 1, 48 => -1, 97 => 2],
  sparse![294; 0 => 1, 6 => 1, 13 => 1, 97 => 1],
  sparse![294; 1 => 1, 6 => 1, 13 => 1, 48 => 1],
  sparse![294; 0 => -1, 1 => 2, 6 => 1, 13 => 1, 48 => 2, 97 => -1],
  sparse![294; 2 => 2, 5 => -1, 20 => 1, 41 => 1, 146 => -1, 293 => 2],
  sparse![294; 2 => 1, 20 => 1, 41 => 1, 293 => 1],
  sparse![294; 5 => 1, 20 => 1, 41 => 1, 146 => 1],
  sparse![294; 2 => -1, 5 => 2, 20 => 1, 41 => 1, 146 => 2, 293 => -1],
  sparse![294; 0 => 1, 1 => -1, 2 => -1, 5 => 2, 6 => -1, 13 => 1, 20 => 4, 41 => -2, 146 => -1, 293 => 2],
  sparse![294; 0 => 2, 1 => -1, 6 => -2, 13 => 4, 20 => 1, 41 => -1, 48 => 2, 97 => -1, 146 => -1, 293 => 1],
  sparse![294; 0 => -1, 1 => 2, 6 => 4, 13 => -2, 20 => -1, 41 => 1, 48 => -1, 97 => 2, 146 => 1, 293 => -1],
  sparse![294; 2 => 2, 5 => -1, 6 => 1, 13 => -1, 20 => -2, 41 => 4, 48 => -1, 97 => 1, 146 => 2, 293 => -1],
  sparse![294; 0 => 1, 6 => -1, 13 => 2, 20 => 1, 48 => 1, 97 => -1, 293 => 1],
  sparse![294; 1 => 1, 6 => 2, 13 => -1, 41 => 1, 48 => -1, 97 => 1, 146 => 1],
  sparse![294; 2 => 1, 6 => 1, 20 => -1, 41 => 2, 97 => 1, 146 => 1, 293 => -1],
  sparse![294; 5 => 1, 13 => 1, 20 => 2, 41 => -1, 48 => 1, 146 => -1, 293 => 1],
  sparse![294; 0 => 1, 1 => -1, 5 => 1, 6 => -1, 13 => 2, 20 => 1, 48 => 1],
  sparse![294; 0 => -1, 1 => 1, 2 => 1, 6 => 2, 13 => -1, 41 => 1, 97 => 1],
  sparse![294; 1 => 1, 2 => 1, 5 => -1, 6 => 1, 20 => -1, 41 => 2, 146 => 1],
  sparse![294; 0 => 1, 2 => -1, 5 => 1, 13 => 1, 20 => 2, 41 => -1, 293 => 1],
  sparse![294; 0 => 2, 1 => -1, 2 => -1, 5 => 1, 6 => -2, 13 => 4, 20 => 1, 41 => -1, 48 => 2, 97 => -1],
  sparse![294; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 6 => 4, 13 => -2, 20 => -1, 41 => 1, 48 => -1, 97 => 2],
  sparse![294; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 6 => 1, 13 => -1, 20 => -2, 41 => 4, 146 => 2, 293 => -1],
  sparse![294; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 6 => -1, 13 => 2, 20 => 2, 41 => -1, 97 => 1],
  sparse![294; 0 => -1, 1 => 2, 6 => -1, 13 => 2, 20 => 2, 41 => -1, 146 => 2, 293 => -1],
  sparse![294; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 6 => -1, 13 => 2, 20 => 2, 41 => -1, 146 => 1],
  sparse![294; 2 => -1, 5 => 2, 6 => 2, 13 => -1, 20 => -1, 41 => 2, 48 => 2, 97 => -1],
  sparse![294; 5 => 1, 6 => 2, 13 => -1, 20 => -1, 41 => 2, 48 => 2, 97 => -1, 146 => -1, 293 => 1],
  sparse![294; 2 => 1, 6 => -1, 13 => 2, 20 => 2, 41 => -1, 48 => -1, 97 => 2, 146 => 1, 293 => -1],
  sparse![294; 2 => 2, 5 => -1, 6 => -1, 13 => 2, 20 => 2, 41 => -1, 48 => -1, 97 => 2],
  sparse![294; 1 => 1, 6 => -1, 13 => 2, 20 => 2, 41 => -1, 48 => -1, 97 => 1, 146 => 2, 293 => -1],
]
```

### Level 295

dim S₂ = **29**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **60**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![295; 0 => 2, 58 => 2],
  sparse![295; 4 => 2, 294 => 2],
  sparse![295; 0 => 1, 4 => 1, 58 => 1, 294 => 1],
]
```

### Level 296

dim S₂ = **35**; eta rank = **12**; full eta basis = **NO**; Sturm bound B = **76**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![296; 0 => -1, 1 => 3, 3 => 1, 7 => -1, 36 => 1, 73 => -1, 147 => 1, 295 => 1],
  sparse![296; 0 => -1, 1 => 2, 3 => 2, 7 => -1, 36 => 1, 295 => 1],
  sparse![296; 0 => -1, 1 => 1, 3 => 3, 7 => -1, 36 => 1, 73 => 1, 147 => -1, 295 => 1],
  sparse![296; 0 => -1, 1 => 4, 3 => -2, 7 => 1, 36 => 1, 73 => -2, 147 => 4, 295 => -1],
  sparse![296; 0 => -1, 1 => 3, 3 => -1, 7 => 1, 36 => 1, 73 => -1, 147 => 3, 295 => -1],
  sparse![296; 0 => -1, 1 => 2, 7 => 1, 36 => 1, 147 => 2, 295 => -1],
  sparse![296; 0 => 1, 3 => 2, 7 => -1, 36 => -1, 73 => 2, 295 => 1],
  sparse![296; 0 => 1, 1 => -1, 3 => 3, 7 => -1, 36 => -1, 73 => 3, 147 => -1, 295 => 1],
  sparse![296; 0 => 1, 1 => -2, 3 => 4, 7 => -1, 36 => -1, 73 => 4, 147 => -2, 295 => 1],
  sparse![296; 0 => 1, 1 => 1, 3 => -1, 7 => 1, 36 => -1, 73 => 1, 147 => 3, 295 => -1],
  sparse![296; 0 => 1, 7 => 1, 36 => -1, 73 => 2, 147 => 2, 295 => -1],
  sparse![296; 0 => 1, 1 => -1, 3 => 1, 7 => 1, 36 => -1, 73 => 3, 147 => 1, 295 => -1],
]
```

### Level 297

dim S₂ = **31**; eta rank = **22**; full eta basis = **NO**; Sturm bound B = **72**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![297; 0 => 2, 10 => 2],
  sparse![297; 2 => 2, 32 => 2],
  sparse![297; 8 => 2, 98 => 2],
  sparse![297; 26 => 2, 296 => 2],
  sparse![297; 2 => 2, 8 => 2],
  sparse![297; 32 => 2, 98 => 2],
  sparse![297; 0 => 1, 2 => 1, 10 => 1, 32 => 1],
  sparse![297; 2 => 1, 8 => 1, 32 => 1, 98 => 1],
  sparse![297; 8 => 1, 26 => 1, 98 => 1, 296 => 1],
  sparse![297; 0 => 1, 8 => 1, 10 => 1, 98 => 1],
  sparse![297; 2 => 1, 26 => 1, 32 => 1, 296 => 1],
  sparse![297; 2 => -1, 8 => 3, 32 => 3, 98 => -1],
  sparse![297; 2 => -1, 8 => 4, 26 => -1, 296 => 2],
  sparse![297; 8 => 3, 26 => -1, 32 => 1, 98 => -1, 296 => 2],
  sparse![297; 0 => 2, 2 => -1, 8 => 1, 10 => -1, 32 => 3],
  sparse![297; 0 => 2, 10 => -1, 32 => 4, 98 => -1],
  sparse![297; 0 => 1, 10 => 1, 26 => 1, 296 => 1],
  sparse![297; 0 => -1, 2 => 3, 10 => 2, 32 => -1, 98 => 1],
  sparse![297; 0 => -1, 2 => 4, 8 => -1, 10 => 2],
  sparse![297; 26 => 2, 32 => -1, 98 => 4, 296 => -1],
  sparse![297; 2 => 1, 8 => -1, 26 => 2, 98 => 3, 296 => -1],
  sparse![297; 2 => 3, 8 => -1, 32 => -1, 98 => 3],
]
```

### Level 298

dim S₂ = **36**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **75**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 299

dim S₂ = **27**; eta rank = **5**; full eta basis = **NO**; Sturm bound B = **56**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![299; 0 => 2, 22 => 2],
  sparse![299; 12 => 2, 298 => 2],
  sparse![299; 0 => 2, 298 => 2],
  sparse![299; 0 => 1, 12 => 1, 22 => 1, 298 => 1],
  sparse![299; 12 => 2, 22 => 2],
]
```

### Level 300

dim S₂ = **43**; eta rank = **43**; full eta basis = **YES**; Sturm bound B = **120**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![300; 0 => -3, 1 => 6, 2 => 1, 3 => -2, 4 => 3, 5 => -2, 9 => -1, 11 => 1, 14 => -1, 29 => 1, 49 => 2, 99 => -1],
  sparse![300; 0 => -3, 1 => 6, 2 => 2, 3 => -2, 4 => 3, 5 => -3, 9 => -3, 11 => 1, 14 => -3, 19 => 1, 29 => 6, 59 => -2, 74 => 1],
  sparse![300; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 4 => 3, 5 => -3, 9 => -3, 11 => 1, 14 => -3, 19 => 1, 29 => 6, 59 => -2],
  sparse![300; 0 => -3, 1 => 7, 2 => 1, 3 => -3, 4 => 3, 5 => -2, 9 => -4, 11 => 1, 14 => -1, 19 => 3, 24 => -3, 29 => 2, 49 => 7, 59 => -1, 74 => 1, 99 => -3, 149 => -2, 299 => 1],
  sparse![300; 0 => -3, 1 => 7, 2 => 2, 3 => -2, 4 => 2, 5 => -3, 9 => -3, 11 => 1, 14 => -3, 19 => 1, 29 => 7, 59 => -2],
  sparse![300; 0 => -3, 1 => 8, 2 => 1, 3 => -3, 4 => -3, 5 => -2, 9 => 8, 11 => 1, 14 => 1, 19 => -3, 29 => -2, 59 => 1],
  sparse![300; 0 => -3, 1 => 8, 2 => 1, 3 => -3, 4 => -1, 5 => -2, 9 => 1, 11 => 1, 14 => 3, 29 => -1],
  sparse![300; 0 => -2, 1 => 3, 2 => 2, 3 => -1, 4 => 1, 5 => -1, 9 => 2, 14 => -1, 19 => -1, 24 => 1, 29 => 1, 49 => -2, 74 => -1, 99 => 1, 149 => 3, 299 => -1],
  sparse![300; 0 => -2, 1 => 3, 2 => 2, 3 => -1, 4 => 2, 5 => -1, 9 => -1, 14 => -1, 24 => 1, 29 => 2, 49 => -1, 99 => 1],
  sparse![300; 0 => -2, 1 => 3, 2 => 2, 3 => -1, 4 => 3, 5 => -2, 9 => -2, 11 => 1, 14 => -2, 19 => 1, 29 => 3, 59 => -1, 74 => 1],
  sparse![300; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 4 => 3, 5 => -3, 9 => -3, 11 => 1, 14 => -3, 19 => 1, 24 => -1, 29 => 6, 49 => 3, 59 => -2, 99 => -1],
  sparse![300; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 4 => 3, 5 => -2, 9 => -2, 11 => 1, 14 => -2, 19 => 1, 29 => 3, 59 => -1],
  sparse![300; 0 => -2, 1 => 4, 2 => 1, 3 => -2, 4 => 3, 5 => -2, 9 => -2, 11 => 2, 14 => -1, 19 => 1, 24 => -1, 29 => 1, 49 => 2, 99 => -1, 149 => 1],
  sparse![300; 0 => -2, 1 => 4, 2 => 1, 3 => -1, 5 => -1, 9 => 2, 14 => -1, 19 => -1, 24 => 1, 29 => 2, 49 => -2, 74 => -1, 99 => 1, 149 => 3, 299 => -1],
  sparse![300; 0 => -2, 1 => 4, 2 => 1, 3 => -1, 4 => 1, 5 => -2, 11 => 1, 24 => -1, 29 => 2, 49 => 2, 59 => -1, 74 => 1, 99 => -1, 149 => -2, 299 => 2],
  sparse![300; 0 => -2, 1 => 4, 2 => 1, 3 => -1, 4 => 1, 5 => -1, 9 => -1, 14 => -1, 24 => 1, 29 => 3, 49 => -1, 99 => 1],
  sparse![300; 0 => -2, 1 => 4, 2 => 1, 3 => -1, 4 => 1, 5 => -1, 9 => -1, 19 => 1, 24 => -1, 49 => 1, 59 => 1, 74 => 1, 149 => 1, 299 => -1],
  sparse![300; 0 => -2, 1 => 4, 2 => 1, 3 => -1, 4 => 2, 5 => -2, 9 => -2, 11 => 1, 14 => -2, 19 => 1, 29 => 4, 59 => -1, 74 => 1],
  sparse![300; 0 => -2, 1 => 4, 2 => 2, 3 => -2, 4 => 1, 5 => -2, 9 => -2, 11 => 1, 19 => 3, 24 => -1, 29 => 1, 49 => 2, 59 => -1, 99 => -1, 149 => 1],
  sparse![300; 0 => -2, 1 => 4, 2 => 2, 3 => -1, 5 => -2, 9 => 1, 14 => -1, 19 => -1, 29 => 1, 49 => 1, 59 => 2, 74 => 1, 149 => -1],
  sparse![300; 0 => -2, 1 => 4, 2 => 2, 3 => -1, 4 => 2, 5 => -3, 9 => -3, 11 => 1, 14 => -3, 19 => 1, 24 => -1, 29 => 7, 49 => 3, 59 => -2, 99 => -1],
  sparse![300; 0 => -2, 1 => 4, 2 => 2, 3 => -1, 4 => 2, 5 => -2, 9 => -2, 11 => 1, 14 => -2, 19 => 1, 29 => 4, 59 => -1],
  sparse![300; 0 => -2, 1 => 5, 3 => -2, 4 => -1, 9 => 3, 14 => -1, 19 => -1, 24 => 1, 29 => 3, 49 => -2, 59 => -1, 74 => -1, 99 => 1, 149 => 3, 299 => -1],
  sparse![300; 0 => -2, 1 => 5, 3 => -2, 5 => -1, 11 => 1, 14 => 3, 29 => -1, 49 => -1, 74 => -1, 99 => 2, 149 => 2, 299 => -1],
  sparse![300; 0 => -2, 1 => 5, 3 => -2, 9 => -1, 14 => 1, 19 => 2, 74 => 1],
  sparse![300; 0 => -2, 1 => 5, 3 => -2, 14 => -1, 24 => 1, 29 => 4, 49 => -1, 59 => -1, 99 => 1],
  sparse![300; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 4 => -3, 5 => -2, 9 => 8, 11 => 1, 14 => 1, 19 => -3, 24 => -1, 29 => -2, 49 => 3, 59 => 1, 99 => -1],
  sparse![300; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 4 => -1, 5 => -2, 9 => 1, 11 => 1, 14 => 3, 24 => -1, 29 => -1, 49 => 3, 99 => -1],
  sparse![300; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 4 => -1, 5 => -2, 9 => 3, 11 => 1, 14 => -1, 19 => -1, 24 => 1, 29 => 3, 49 => -2, 59 => -1, 74 => -2, 99 => 1, 149 => 5, 299 => -2],
  sparse![300; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 5 => -2, 9 => -1, 11 => 1, 14 => 1, 19 => 2, 149 => 2, 299 => -1],
  sparse![300; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 5 => -1, 24 => 2, 29 => -1, 49 => -1, 59 => 3, 74 => -1, 149 => 2, 299 => -1],
  sparse![300; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 4 => 1, 5 => -3, 9 => -3, 11 => 2, 14 => -2, 19 => 2, 29 => 7, 49 => 2, 59 => -3, 99 => -1],
  sparse![300; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 4 => 1, 5 => -3, 9 => -3, 11 => 2, 14 => -2, 19 => 3, 29 => 6, 49 => 1, 59 => -3, 99 => -1, 299 => 1],
  sparse![300; 0 => -2, 1 => 5, 2 => 2, 3 => -2, 4 => 1, 5 => -3, 9 => -2, 11 => 1, 14 => -1, 19 => 1, 24 => 1, 29 => 5, 59 => -2, 74 => -1, 149 => 1],
  sparse![300; 0 => -2, 1 => 6, 2 => 1, 3 => -3, 5 => -2, 9 => -1, 11 => 1, 19 => 3, 24 => -1, 29 => 1, 49 => 2, 59 => -1],
  sparse![300; 0 => -1, 3 => 2, 4 => 3, 5 => 1, 9 => -1, 11 => -1, 14 => -1, 24 => 1, 29 => 1, 49 => -1, 99 => 1],
  sparse![300; 0 => -1, 2 => 1, 3 => 1, 4 => 2, 5 => 1, 9 => 1, 11 => -1, 14 => -1, 19 => -1, 59 => 1, 74 => 1],
  sparse![300; 0 => -1, 2 => 2, 3 => 1, 4 => 2, 5 => -1, 9 => -1, 14 => -1, 29 => 2, 49 => 2, 99 => -1],
  sparse![300; 0 => -1, 2 => 2, 3 => 1, 4 => 2, 5 => -1, 9 => -1, 14 => -1, 19 => 1, 29 => 1, 49 => 1, 99 => -1, 299 => 1],
  sparse![300; 0 => -1, 2 => 2, 3 => 1, 4 => 2, 11 => -1, 14 => -1, 19 => -1, 59 => 2, 99 => 1],
  sparse![300; 0 => -1, 2 => 2, 3 => 1, 4 => 2, 5 => 1, 9 => 1, 11 => -1, 14 => -1, 19 => -1, 59 => 1],
  sparse![300; 0 => -1, 1 => 1, 4 => 3, 9 => -1, 14 => 3, 29 => -1, 74 => -1, 149 => 1],
  sparse![300; 0 => -1, 1 => 1, 2 => 1, 9 => 2, 14 => 1, 19 => -1, 24 => 2, 29 => -1, 49 => -2, 59 => 1, 74 => -1, 99 => 1, 149 => 2, 299 => -1],
]
```

### Level 301

dim S₂ = **27**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **58**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 302

dim S₂ = **37**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **76**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![302; 0 => 1, 1 => 1, 150 => 1, 301 => 1],
]
```

### Level 303

dim S₂ = **33**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **68**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![303; 0 => 1, 2 => 1, 100 => 1, 302 => 1],
]
```

### Level 304

dim S₂ = **35**; eta rank = **34**; full eta basis = **NO**; Sturm bound B = **80**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![304; 0 => 3, 1 => -1, 18 => -1, 37 => 3],
  sparse![304; 0 => -1, 1 => 3, 18 => 3, 37 => -1],
  sparse![304; 1 => 3, 3 => -1, 37 => -1, 75 => 3],
  sparse![304; 1 => -1, 3 => 3, 37 => 3, 75 => -1],
  sparse![304; 3 => 3, 7 => -1, 75 => -1, 151 => 3],
  sparse![304; 3 => -1, 7 => 3, 75 => 3, 151 => -1],
  sparse![304; 7 => 3, 15 => -1, 151 => -1, 303 => 3],
  sparse![304; 7 => -1, 15 => 3, 151 => 3, 303 => -1],
  sparse![304; 0 => 1, 3 => 1, 18 => -3, 37 => 8, 75 => -3],
  sparse![304; 1 => 1, 7 => 1, 37 => -3, 75 => 8, 151 => -3],
  sparse![304; 3 => 1, 15 => 1, 75 => -3, 151 => 8, 303 => -3],
  sparse![304; 0 => -1, 1 => 1, 3 => 3, 7 => -1, 18 => -1, 37 => 3, 75 => 1, 151 => -1],
  sparse![304; 0 => -1, 1 => 3, 3 => 1, 7 => -1, 18 => -1, 37 => 1, 75 => 3, 151 => -1],
  sparse![304; 1 => 1, 3 => 1, 37 => 1, 75 => 1],
  sparse![304; 0 => -1, 1 => 2, 7 => 1, 18 => -1, 37 => 4, 75 => -2, 151 => 1],
  sparse![304; 0 => -1, 1 => 4, 3 => -2, 7 => 1, 18 => -1, 37 => 2, 151 => 1],
  sparse![304; 0 => 1, 1 => -2, 3 => 4, 7 => -1, 18 => 1, 75 => 2, 151 => -1],
  sparse![304; 1 => -1, 3 => 1, 7 => 3, 15 => -1, 37 => -1, 75 => 3, 151 => 1, 303 => -1],
  sparse![304; 1 => -1, 3 => 3, 7 => 1, 15 => -1, 37 => -1, 75 => 1, 151 => 3, 303 => -1],
  sparse![304; 3 => 1, 7 => 1, 75 => 1, 151 => 1],
  sparse![304; 1 => 1, 3 => -2, 7 => 4, 15 => -1, 37 => 1, 151 => 2, 303 => -1],
  sparse![304; 1 => 1, 7 => 2, 15 => -1, 37 => 1, 75 => -2, 151 => 4, 303 => -1],
  sparse![304; 0 => -1, 1 => 3, 18 => -1, 37 => 5, 75 => -2],
  sparse![304; 3 => -2, 7 => 5, 15 => -1, 151 => 3, 303 => -1],
  sparse![304; 0 => -1, 1 => 5, 3 => -2, 18 => -1, 37 => 3],
  sparse![304; 0 => 1, 1 => -2, 3 => 4, 7 => -2, 15 => 1, 18 => 1, 303 => 1],
  sparse![304; 7 => 3, 15 => -1, 75 => -2, 151 => 5, 303 => -1],
  sparse![304; 0 => -2, 1 => 4, 18 => 2, 37 => -2, 75 => 2],
  sparse![304; 0 => -2, 1 => 5, 3 => -3, 7 => 3, 15 => -1, 75 => 1, 303 => 1],
  sparse![304; 0 => -1, 1 => 1, 3 => 2, 7 => 1, 15 => -1, 18 => -1, 37 => 3, 75 => -2, 151 => 3, 303 => -1],
  sparse![304; 0 => -1, 1 => 1, 3 => 3, 7 => -2, 15 => 1, 18 => -1, 37 => 3, 75 => -1, 303 => 1],
  sparse![304; 0 => -1, 1 => 2, 7 => 2, 15 => -1, 18 => 1, 37 => -1, 75 => 2, 151 => -1, 303 => 1],
  sparse![304; 0 => -1, 1 => 3, 3 => -3, 7 => 5, 15 => -2, 18 => 1, 75 => 1],
  sparse![304; 1 => -1, 3 => 4, 7 => -1, 37 => -1, 75 => 4, 151 => -1],
]
```

### Level 305

dim S₂ = **29**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **62**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 306

dim S₂ = **47**; eta rank = **45**; full eta basis = **NO**; Sturm bound B = **108**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![306; 0 => 1, 2 => 1, 16 => 1, 50 => 1],
  sparse![306; 1 => 1, 5 => 1, 33 => 1, 101 => 1],
  sparse![306; 2 => 1, 8 => 1, 50 => 1, 152 => 1],
  sparse![306; 5 => 1, 17 => 1, 101 => 1, 305 => 1],
  sparse![306; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 16 => 1, 101 => 1],
  sparse![306; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 33 => 1, 50 => 1],
  sparse![306; 1 => 2, 2 => 1, 5 => -1, 16 => -1, 33 => 1, 50 => 2],
  sparse![306; 0 => 2, 2 => -1, 5 => 1, 16 => 1, 33 => -1, 101 => 2],
  sparse![306; 0 => 1, 1 => -1, 5 => 2, 16 => 2, 50 => -1, 101 => 1],
  sparse![306; 0 => -1, 1 => 1, 2 => 2, 33 => 2, 50 => 1, 101 => -1],
  sparse![306; 0 => -1, 1 => 3, 2 => 1, 5 => -1, 16 => 1, 33 => -1, 50 => -1, 101 => 3],
  sparse![306; 0 => 3, 1 => -1, 2 => -1, 5 => 1, 16 => -1, 33 => 1, 50 => 3, 101 => -1],
  sparse![306; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 16 => 3, 33 => -1, 50 => -1, 101 => 1],
  sparse![306; 1 => 1, 2 => 1, 16 => 3, 33 => -2, 50 => -2, 101 => 3],
  sparse![306; 0 => 1, 1 => -1, 2 => -1, 5 => 3, 16 => -1, 33 => 3, 50 => 1, 101 => -1],
  sparse![306; 2 => -2, 5 => 3, 8 => 3, 17 => -2, 50 => 1, 305 => 1],
  sparse![306; 2 => 3, 5 => -2, 8 => -2, 17 => 3, 101 => 1, 152 => 1],
  sparse![306; 5 => 2, 8 => 1, 17 => -1, 50 => -1, 101 => 1, 152 => 2],
  sparse![306; 2 => 2, 8 => -1, 17 => 1, 50 => 1, 101 => -1, 305 => 2],
  sparse![306; 2 => 1, 5 => -1, 17 => 2, 50 => 2, 152 => -1, 305 => 1],
  sparse![306; 2 => -1, 5 => 1, 8 => 2, 101 => 2, 152 => 1, 305 => -1],
  sparse![306; 2 => -1, 5 => 3, 8 => 1, 17 => -1, 50 => 1, 101 => -1, 152 => -1, 305 => 3],
  sparse![306; 2 => 3, 5 => -1, 8 => -1, 17 => 1, 50 => -1, 101 => 1, 152 => 3, 305 => -1],
  sparse![306; 2 => -1, 5 => 1, 8 => 3, 17 => -1, 50 => 3, 101 => -1, 152 => -1, 305 => 1],
  sparse![306; 2 => 1, 5 => -1, 8 => -1, 17 => 3, 50 => -1, 101 => 3, 152 => 1, 305 => -1],
  sparse![306; 0 => -1, 1 => 1, 2 => 2, 16 => 3, 33 => -1],
  sparse![306; 0 => 1, 1 => -1, 5 => 2, 16 => -1, 33 => 3],
  sparse![306; 2 => 2, 8 => -1, 17 => 1, 152 => 3, 305 => -1],
  sparse![306; 0 => 3, 1 => -1, 16 => -1, 33 => 1, 50 => 2],
  sparse![306; 5 => 2, 8 => 1, 17 => -1, 152 => -1, 305 => 3],
  sparse![306; 0 => -1, 1 => 3, 16 => 1, 33 => -1, 101 => 2],
  sparse![306; 2 => 3, 5 => -1, 8 => -1, 16 => 2, 17 => 1, 33 => -1, 50 => -1, 101 => 1, 152 => 1],
  sparse![306; 2 => -1, 5 => 3, 8 => 1, 16 => -1, 17 => -1, 33 => 2, 50 => 1, 101 => -1, 305 => 1],
  sparse![306; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 16 => 1, 50 => -1, 101 => 1, 152 => 2, 305 => -1],
  sparse![306; 0 => 2, 1 => -1, 2 => -1, 5 => 1, 8 => 1, 50 => 3, 101 => -1, 152 => -1, 305 => 1],
  sparse![306; 0 => 1, 1 => -1, 2 => -1, 5 => 3, 33 => 1, 50 => 1, 101 => -1, 152 => -1, 305 => 2],
  sparse![306; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 17 => 1, 50 => -1, 101 => 3, 152 => 1, 305 => -1],
  sparse![306; 0 => -2, 1 => 3, 2 => 2, 5 => -1, 16 => 1, 50 => 1],
  sparse![306; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 8 => 2, 16 => 1, 17 => -1, 101 => 1],
  sparse![306; 0 => -1, 1 => 2, 2 => -1, 5 => 2, 8 => 1, 17 => -1, 50 => 1, 305 => 1],
  sparse![306; 0 => -1, 1 => 2, 17 => 1, 101 => 2, 152 => 1, 305 => -1],
  sparse![306; 0 => -1, 1 => 2, 5 => 1, 8 => 1, 17 => -1, 101 => 1, 305 => 1],
  sparse![306; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 8 => 1, 50 => 2, 152 => -1, 305 => 1],
  sparse![306; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 8 => -1, 17 => 1, 50 => 1, 152 => 1],
  sparse![306; 0 => -1, 1 => 2, 2 => 3, 5 => -2, 8 => -1, 17 => 1, 101 => 1, 152 => 1],
]
```

### Level 307

dim S₂ = **25**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **51**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 308

dim S₂ = **43**; eta rank = **43**; full eta basis = **YES**; Sturm bound B = **96**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![308; 0 => 2, 10 => 2],
  sparse![308; 1 => 2, 21 => 2],
  sparse![308; 3 => 2, 43 => 2],
  sparse![308; 6 => 2, 76 => 2],
  sparse![308; 13 => 2, 153 => 2],
  sparse![308; 27 => 2, 307 => 2],
  sparse![308; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![308; 1 => 1, 3 => 1, 13 => 1, 27 => 1],
  sparse![308; 10 => 1, 21 => 1, 76 => 1, 153 => 1],
  sparse![308; 21 => 1, 43 => 1, 153 => 1, 307 => 1],
  sparse![308; 0 => 1, 6 => 1, 10 => 1, 76 => 1],
  sparse![308; 1 => 1, 13 => 1, 21 => 1, 153 => 1],
  sparse![308; 3 => 1, 27 => 1, 43 => 1, 307 => 1],
  sparse![308; 0 => -1, 1 => 2, 6 => -1, 10 => 2, 13 => 2, 21 => -1, 76 => 2, 153 => -1],
  sparse![308; 0 => -1, 1 => 2, 6 => 2, 10 => 1, 13 => -1, 153 => 1],
  sparse![308; 1 => 1, 6 => 1, 10 => 2, 21 => -1, 76 => -1, 153 => 2],
  sparse![308; 0 => -1, 1 => 2, 6 => 1, 10 => -1, 21 => 2, 76 => 1],
  sparse![308; 0 => 1, 6 => -1, 10 => 1, 13 => 2, 76 => -1, 153 => 2],
  sparse![308; 1 => 1, 6 => 2, 13 => -1, 21 => 1, 76 => 2, 153 => -1],
  sparse![308; 0 => 2, 1 => -1, 10 => 2, 13 => 1, 21 => -1, 153 => 1],
  sparse![308; 0 => 1, 10 => -1, 13 => 1, 21 => 2, 76 => 2, 153 => -1],
  sparse![308; 0 => 2, 1 => -1, 6 => -1, 13 => 2, 21 => 1, 76 => 1],
  sparse![308; 1 => -1, 3 => 2, 13 => -1, 21 => 2, 27 => 2, 43 => -1, 153 => 2, 307 => -1],
  sparse![308; 1 => -1, 3 => 2, 13 => 2, 21 => 1, 27 => -1, 307 => 1],
  sparse![308; 3 => 1, 13 => 1, 21 => 2, 43 => -1, 153 => -1, 307 => 2],
  sparse![308; 1 => -1, 3 => 2, 13 => 1, 21 => -1, 43 => 2, 153 => 1],
  sparse![308; 1 => 1, 13 => -1, 21 => 1, 27 => 2, 153 => -1, 307 => 2],
  sparse![308; 3 => 1, 13 => 2, 27 => -1, 43 => 1, 153 => 2, 307 => -1],
  sparse![308; 1 => 2, 3 => -1, 21 => 2, 27 => 1, 43 => -1, 307 => 1],
  sparse![308; 1 => 1, 21 => -1, 27 => 1, 43 => 2, 153 => 2, 307 => -1],
  sparse![308; 0 => 2, 1 => -2, 3 => 2, 6 => -1, 13 => 2, 27 => -1, 76 => 1, 307 => 1],
  sparse![308; 6 => 1, 10 => 2, 21 => -2, 27 => 1, 43 => 2, 76 => -1, 153 => 2, 307 => -1],
  sparse![308; 0 => -1, 1 => 3, 10 => 1, 21 => -1, 76 => -2, 153 => 4],
  sparse![308; 1 => 2, 3 => -1, 10 => 1, 13 => 2, 21 => -1, 27 => -1, 43 => 1, 76 => 1, 153 => -1, 307 => 1],
  sparse![308; 0 => -1, 1 => 1, 3 => 1, 6 => 2, 10 => 1, 13 => -1, 21 => 1, 43 => -1, 153 => -1, 307 => 2],
  sparse![308; 0 => 1, 1 => 1, 3 => -1, 10 => -1, 13 => -1, 21 => 1, 27 => 2, 43 => 1, 76 => 2, 153 => -1],
  sparse![308; 0 => 2, 1 => -1, 6 => -1, 13 => 1, 21 => -1, 27 => 1, 43 => 2, 76 => 1, 153 => 1, 307 => -1],
  sparse![308; 1 => 2, 153 => 2],
  sparse![308; 13 => 2, 21 => 2],
  sparse![308; 3 => 1, 10 => 1, 27 => 1, 76 => 1],
  sparse![308; 0 => -3, 1 => 8, 3 => -3, 6 => 1, 10 => 1, 13 => -2, 21 => -2, 27 => 1, 43 => 1, 76 => -3, 153 => 8, 307 => -3],
  sparse![308; 0 => -2, 1 => 4, 3 => -1, 6 => 2, 10 => 2, 13 => -1, 21 => -2, 43 => 1, 76 => -2, 153 => 5, 307 => -2],
  sparse![308; 0 => -2, 1 => 4, 6 => 1, 13 => -1, 76 => -1, 153 => 3],
]
```

### Level 309

dim S₂ = **33**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **69**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 310

dim S₂ = **45**; eta rank = **22**; full eta basis = **NO**; Sturm bound B = **96**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![310; 0 => 1, 1 => 1, 30 => 1, 61 => 1],
  sparse![310; 4 => 1, 9 => 1, 154 => 1, 309 => 1],
  sparse![310; 0 => 2, 154 => 2],
  sparse![310; 0 => 1, 4 => 1, 30 => 1, 154 => 1],
  sparse![310; 4 => 2, 30 => 2],
  sparse![310; 1 => 2, 309 => 2],
  sparse![310; 1 => 1, 9 => 1, 61 => 1, 309 => 1],
  sparse![310; 9 => 2, 61 => 2],
  sparse![310; 0 => 2, 1 => -1, 4 => -1, 9 => 2, 30 => 2, 61 => -1, 154 => -1, 309 => 2],
  sparse![310; 0 => 1, 4 => 2, 9 => -1, 61 => 1, 154 => -1, 309 => 2],
  sparse![310; 0 => 2, 1 => -1, 4 => 1, 30 => -1, 61 => 2, 309 => 1],
  sparse![310; 0 => -1, 1 => 2, 4 => 1, 30 => 1, 154 => -1, 309 => 2],
  sparse![310; 0 => 1, 4 => -1, 9 => 2, 30 => -1, 61 => 2, 154 => 1],
  sparse![310; 1 => 1, 4 => 2, 9 => -1, 30 => 2, 61 => -1, 309 => 1],
  sparse![310; 0 => 2, 1 => -1, 9 => 1, 61 => 1, 154 => 2, 309 => -1],
  sparse![310; 0 => -1, 1 => 2, 9 => 1, 30 => 2, 61 => -1, 154 => 1],
  sparse![310; 1 => 1, 4 => -1, 9 => 2, 30 => 1, 154 => 2, 309 => -1],
  sparse![310; 0 => -1, 1 => 2, 4 => 2, 9 => -1, 30 => -1, 61 => 2, 154 => 2, 309 => -1],
  sparse![310; 0 => 1, 1 => -1, 4 => -1, 9 => 3, 30 => -1, 61 => 3, 154 => 1, 309 => -1],
  sparse![310; 0 => -1, 1 => 3, 4 => 1, 9 => -1, 30 => 1, 61 => -1, 154 => -1, 309 => 3],
  sparse![310; 0 => -1, 1 => 1, 4 => 3, 9 => -1, 30 => 3, 61 => -1, 154 => -1, 309 => 1],
  sparse![310; 0 => 3, 1 => -1, 4 => -1, 9 => 1, 30 => -1, 61 => 1, 154 => 3, 309 => -1],
]
```

### Level 311

dim S₂ = **26**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **52**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![311; 0 => 2, 310 => 2],
]
```

### Level 312

dim S₂ = **49**; eta rank = **49**; full eta basis = **YES**; Sturm bound B = **112**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![312; 1 => 1, 3 => 1, 5 => 1, 11 => 1],
  sparse![312; 25 => 1, 51 => 1, 77 => 1, 155 => 1],
  sparse![312; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 12 => 3, 25 => -2, 38 => -2, 77 => 3],
  sparse![312; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 12 => -2, 25 => 3, 38 => 3, 77 => -2],
  sparse![312; 0 => 1, 1 => 1, 38 => 1, 77 => 1],
  sparse![312; 0 => 1, 5 => 1, 25 => 1, 38 => 1],
  sparse![312; 1 => 1, 2 => 1, 12 => 1, 77 => 1],
  sparse![312; 2 => 1, 5 => 1, 12 => 1, 25 => 1],
  sparse![312; 0 => -1, 1 => 1, 2 => 2, 12 => 2, 38 => -1, 77 => 1],
  sparse![312; 0 => -1, 1 => 2, 5 => 1, 12 => 2, 25 => -1, 38 => 1],
  sparse![312; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 12 => 2, 25 => -1, 38 => -1, 77 => 2],
  sparse![312; 1 => 1, 2 => -1, 5 => 2, 12 => 1, 38 => 2, 77 => -1],
  sparse![312; 0 => 1, 1 => -1, 5 => 2, 25 => 2, 38 => 1, 77 => -1],
  sparse![312; 1 => -2, 3 => 3, 5 => 3, 11 => -2, 25 => 3, 51 => -2, 77 => -2, 155 => 3],
  sparse![312; 1 => 3, 3 => -2, 5 => -2, 11 => 3, 25 => -2, 51 => 3, 77 => 3, 155 => -2],
  sparse![312; 1 => 1, 3 => 1, 77 => 1, 155 => 1],
  sparse![312; 1 => 1, 11 => 1, 51 => 1, 77 => 1],
  sparse![312; 3 => 1, 5 => 1, 25 => 1, 155 => 1],
  sparse![312; 5 => 1, 11 => 1, 25 => 1, 51 => 1],
  sparse![312; 1 => -1, 3 => 2, 11 => 1, 25 => 2, 51 => -1, 77 => 1],
  sparse![312; 3 => 1, 5 => -1, 11 => 2, 25 => 1, 77 => 2, 155 => -1],
  sparse![312; 3 => -2, 7 => 3, 11 => 3, 23 => -2, 51 => 3, 103 => -2, 155 => -2, 311 => 3],
  sparse![312; 3 => 3, 7 => -2, 11 => -2, 23 => 3, 51 => -2, 103 => 3, 155 => 3, 311 => -2],
  sparse![312; 3 => 1, 7 => 1, 155 => 1, 311 => 1],
  sparse![312; 3 => 1, 23 => 1, 103 => 1, 155 => 1],
  sparse![312; 7 => 1, 11 => 1, 51 => 1, 311 => 1],
  sparse![312; 11 => 1, 23 => 1, 51 => 1, 103 => 1],
  sparse![312; 3 => -1, 7 => 2, 23 => 1, 51 => 2, 103 => -1, 155 => 1],
  sparse![312; 7 => 1, 11 => -1, 23 => 2, 51 => 1, 155 => 2, 311 => -1],
  sparse![312; 0 => 1, 3 => 2, 7 => -1, 12 => -1, 25 => 2, 103 => 1],
  sparse![312; 0 => -1, 1 => 1, 3 => 3, 7 => -1, 12 => 1, 25 => 1, 51 => -1, 103 => 1],
  sparse![312; 0 => -1, 1 => 2, 7 => 1, 12 => 1, 51 => 2, 103 => -1],
  sparse![312; 0 => -1, 1 => 2, 3 => 2, 7 => -1, 12 => 1, 103 => 1],
  sparse![312; 0 => -1, 1 => 3, 3 => 1, 7 => -1, 12 => 1, 25 => -1, 51 => 1, 103 => 1],
  sparse![312; 2 => 1, 11 => 2, 23 => -1, 38 => -1, 77 => 2, 311 => 1],
  sparse![312; 2 => -1, 5 => 1, 11 => 3, 23 => -1, 38 => 1, 77 => 1, 155 => -1, 311 => 1],
  sparse![312; 2 => -1, 5 => 2, 23 => 1, 38 => 1, 155 => 2, 311 => -1],
  sparse![312; 2 => -1, 5 => 2, 11 => 2, 23 => -1, 38 => 1, 311 => 1],
  sparse![312; 2 => -1, 5 => 3, 11 => 1, 23 => -1, 38 => 1, 77 => -1, 155 => 1, 311 => 1],
  sparse![312; 0 => 2, 1 => 1, 2 => -1, 3 => -1, 11 => 1, 12 => -1, 38 => 2, 51 => 1, 77 => 1, 155 => -1],
  sparse![312; 1 => 2, 3 => 1, 5 => -1, 7 => -1, 23 => 1, 25 => -1, 77 => 2, 103 => 1, 155 => 1, 311 => -1],
  sparse![312; 1 => 1, 3 => -1, 11 => 1, 23 => 1, 25 => -1, 51 => 2, 103 => 1],
  sparse![312; 3 => 1, 5 => 1, 7 => 1, 11 => -1, 77 => -1, 155 => 2, 311 => 1],
  sparse![312; 1 => -1, 2 => 1, 3 => 1, 5 => 1, 12 => 1, 25 => 2, 51 => -1],
  sparse![312; 1 => -1, 3 => 2, 7 => 1, 25 => 1, 51 => -1, 155 => 1, 311 => 1],
  sparse![312; 0 => 1, 1 => 1, 5 => -1, 11 => 1, 38 => 1, 77 => 2, 155 => -1],
  sparse![312; 0 => 1, 23 => 1, 38 => 1, 103 => 1],
  sparse![312; 1 => 2, 25 => -1, 51 => 1, 77 => 1, 155 => 1],
  sparse![312; 1 => 1, 3 => 1, 5 => 1, 11 => -1, 155 => 2],
]
```

### Level 313

dim S₂ = **25**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **52**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 314

dim S₂ = **38**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **79**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 315

dim S₂ = **41**; eta rank = **30**; full eta basis = **NO**; Sturm bound B = **96**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![315; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![315; 2 => 1, 8 => 1, 14 => 1, 44 => 1],
  sparse![315; 6 => 1, 20 => 1, 34 => 1, 104 => 1],
  sparse![315; 20 => 1, 62 => 1, 104 => 1, 314 => 1],
  sparse![315; 0 => 2, 34 => 2],
  sparse![315; 0 => 1, 4 => 1, 6 => 1, 34 => 1],
  sparse![315; 4 => 2, 6 => 2],
  sparse![315; 2 => 2, 104 => 2],
  sparse![315; 2 => 1, 14 => 1, 20 => 1, 104 => 1],
  sparse![315; 14 => 2, 20 => 2],
  sparse![315; 8 => 2, 314 => 2],
  sparse![315; 8 => 1, 44 => 1, 62 => 1, 314 => 1],
  sparse![315; 44 => 2, 62 => 2],
  sparse![315; 2 => 2, 20 => 2],
  sparse![315; 0 => -1, 2 => 4, 6 => 1, 8 => -1, 62 => 1],
  sparse![315; 0 => 1, 6 => -1, 8 => 1, 20 => 4, 62 => -1],
  sparse![315; 14 => 2, 104 => 2],
  sparse![315; 4 => -1, 14 => 4, 34 => 1, 44 => -1, 314 => 1],
  sparse![315; 4 => 1, 34 => -1, 44 => 1, 104 => 4, 314 => -1],
  sparse![315; 0 => 1, 14 => 1, 20 => 1, 34 => 1],
  sparse![315; 2 => 1, 4 => 1, 6 => 1, 104 => 1],
  sparse![315; 0 => 1, 2 => 1, 34 => 1, 104 => 1],
  sparse![315; 2 => 1, 44 => 1, 62 => 1, 104 => 1],
  sparse![315; 2 => 1, 8 => 1, 104 => 1, 314 => 1],
  sparse![315; 0 => -1, 2 => 3, 6 => 1, 8 => -1, 14 => 1, 20 => -1, 62 => 1, 104 => 1],
  sparse![315; 0 => 1, 4 => 1, 62 => 1, 314 => 1],
  sparse![315; 6 => 1, 8 => 1, 34 => 1, 44 => 1],
  sparse![315; 0 => 1, 8 => 1, 34 => 1, 314 => 1],
  sparse![315; 0 => 1, 34 => 1, 44 => 1, 62 => 1],
  sparse![315; 2 => 1, 4 => -1, 14 => 3, 20 => 1, 34 => 1, 44 => -1, 104 => -1, 314 => 1],
]
```

### Level 316

dim S₂ = **38**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **80**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![316; 0 => 1, 1 => 1, 78 => 1, 157 => 1],
  sparse![316; 1 => 1, 3 => 1, 157 => 1, 315 => 1],
  sparse![316; 0 => -1, 1 => 4, 3 => -1, 78 => -1, 157 => 4, 315 => -1],
]
```

### Level 317

dim S₂ = **26**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **53**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 318

dim S₂ = **51**; eta rank = **10**; full eta basis = **NO**; Sturm bound B = **108**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![318; 0 => 1, 2 => 1, 52 => 1, 158 => 1],
  sparse![318; 1 => 1, 5 => 1, 105 => 1, 317 => 1],
  sparse![318; 0 => -1, 1 => 3, 2 => 1, 5 => -1, 52 => 1, 105 => -1, 158 => -1, 317 => 3],
  sparse![318; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 52 => 2, 105 => -1, 158 => -1, 317 => 2],
  sparse![318; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 52 => 3, 105 => -1, 158 => -1, 317 => 1],
  sparse![318; 0 => 1, 1 => 1, 158 => 1, 317 => 1],
  sparse![318; 2 => 1, 5 => 1, 52 => 1, 105 => 1],
  sparse![318; 0 => 1, 1 => -1, 2 => -1, 5 => 3, 52 => -1, 105 => 3, 158 => 1, 317 => -1],
  sparse![318; 0 => 2, 1 => -1, 2 => -1, 5 => 2, 52 => -1, 105 => 2, 158 => 2, 317 => -1],
  sparse![318; 0 => 3, 1 => -1, 2 => -1, 5 => 1, 52 => -1, 105 => 1, 158 => 3, 317 => -1],
]
```

### Level 319

dim S₂ = **29**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **60**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![319; 0 => 2, 10 => 2],
  sparse![319; 28 => 2, 318 => 2],
  sparse![319; 0 => 1, 10 => 1, 28 => 1, 318 => 1],
]
```

### Level 320

dim S₂ = **37**; eta rank = **37**; full eta basis = **YES**; Sturm bound B = **96**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![320; 1 => 2, 9 => 2],
  sparse![320; 3 => 2, 19 => 2],
  sparse![320; 7 => 2, 39 => 2],
  sparse![320; 15 => 2, 79 => 2],
  sparse![320; 31 => 2, 159 => 2],
  sparse![320; 3 => 2, 7 => 2],
  sparse![320; 7 => 2, 15 => 2],
  sparse![320; 19 => 2, 39 => 2],
  sparse![320; 39 => 2, 79 => 2],
  sparse![320; 0 => -2, 1 => 5, 3 => -1, 4 => 2, 9 => -1, 19 => 1],
  sparse![320; 1 => -2, 3 => 5, 7 => -1, 9 => 2, 19 => -1, 39 => 1],
  sparse![320; 3 => -2, 7 => 5, 15 => -1, 19 => 2, 39 => -1, 79 => 1],
  sparse![320; 7 => -2, 15 => 5, 31 => -1, 39 => 2, 79 => -1, 159 => 1],
  sparse![320; 0 => -2, 1 => 5, 3 => -2, 7 => 3],
  sparse![320; 4 => -2, 9 => 5, 19 => -2, 39 => 3],
  sparse![320; 0 => -2, 1 => 5, 3 => -1, 4 => -2, 9 => 5, 19 => -1],
  sparse![320; 0 => -1, 1 => 1, 3 => 2, 4 => 1, 9 => 1],
  sparse![320; 1 => -2, 3 => 5, 7 => -1, 9 => -2, 19 => 5, 39 => -1],
  sparse![320; 1 => -1, 3 => 1, 7 => 2, 9 => 1, 19 => 1],
  sparse![320; 3 => -2, 7 => 5, 15 => -1, 19 => -2, 39 => 5, 79 => -1],
  sparse![320; 3 => -1, 7 => 1, 15 => 2, 19 => 1, 39 => 1],
  sparse![320; 3 => 1, 7 => 1, 19 => 1, 39 => 1],
  sparse![320; 0 => -2, 1 => 3, 3 => 2, 4 => 2, 7 => -1, 9 => -3, 19 => 4, 39 => -1],
  sparse![320; 0 => -2, 1 => 4, 3 => -2, 4 => 2, 7 => 2],
  sparse![320; 0 => -2, 1 => 5, 3 => -3, 7 => 3, 15 => -1, 19 => 1, 39 => 2, 79 => -1],
  sparse![320; 7 => 1, 15 => 1, 39 => 1, 79 => 1],
  sparse![320; 1 => -2, 3 => 3, 7 => 2, 9 => 2, 15 => -1, 19 => -3, 39 => 4, 79 => -1],
  sparse![320; 1 => -2, 3 => 4, 7 => -2, 9 => 2, 15 => 2],
  sparse![320; 1 => -2, 3 => 5, 7 => -3, 15 => 3, 31 => -1, 39 => 1, 79 => 2, 159 => -1],
  sparse![320; 4 => -2, 7 => 1, 9 => 5, 15 => 1, 19 => -2, 39 => 2, 79 => -1],
  sparse![320; 1 => 1, 3 => -1, 7 => 1, 9 => 1, 31 => 1, 39 => 1, 79 => -1, 159 => 1],
  sparse![320; 0 => 1, 1 => 1, 4 => 1, 39 => 1],
  sparse![320; 0 => 1, 4 => 1, 7 => 1, 9 => 1],
  sparse![320; 3 => 2, 79 => 2],
  sparse![320; 3 => 1, 15 => 1, 19 => 1, 79 => 1],
  sparse![320; 7 => 1, 63 => 1, 159 => 1, 319 => 1],
  sparse![320; 31 => 1, 39 => 1, 63 => 1, 319 => 1],
]
```

### Level 321

dim S₂ = **35**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **72**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![321; 0 => 2, 106 => 2],
  sparse![321; 2 => 2, 320 => 2],
  sparse![321; 0 => 1, 2 => 1, 106 => 1, 320 => 1],
]
```

### Level 322

dim S₂ = **45**; eta rank = **28**; full eta basis = **NO**; Sturm bound B = **96**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![322; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![322; 22 => 1, 45 => 1, 160 => 1, 321 => 1],
  sparse![322; 0 => 2, 22 => 2],
  sparse![322; 1 => 2, 45 => 2],
  sparse![322; 6 => 2, 160 => 2],
  sparse![322; 13 => 2, 321 => 2],
  sparse![322; 0 => -1, 1 => 3, 22 => -1, 45 => 3],
  sparse![322; 0 => 1, 1 => 1, 22 => 1, 45 => 1],
  sparse![322; 0 => 3, 1 => -1, 22 => 3, 45 => -1],
  sparse![322; 6 => -1, 13 => 3, 160 => -1, 321 => 3],
  sparse![322; 6 => 1, 13 => 1, 160 => 1, 321 => 1],
  sparse![322; 6 => 3, 13 => -1, 160 => 3, 321 => -1],
  sparse![322; 0 => 1, 6 => 1, 22 => 1, 160 => 1],
  sparse![322; 1 => 1, 13 => 1, 45 => 1, 321 => 1],
  sparse![322; 0 => -1, 1 => 2, 6 => -1, 13 => 2, 22 => 2, 45 => -1, 160 => 2, 321 => -1],
  sparse![322; 0 => -1, 1 => 2, 13 => 1, 22 => -1, 45 => 2, 321 => 1],
  sparse![322; 0 => -1, 1 => 2, 6 => 1, 22 => -1, 45 => 2, 160 => 1],
  sparse![322; 0 => -1, 1 => 2, 6 => 2, 13 => -1, 22 => -1, 45 => 2, 160 => 2, 321 => -1],
  sparse![322; 1 => 1, 6 => -1, 13 => 2, 45 => 1, 160 => -1, 321 => 2],
  sparse![322; 1 => 1, 6 => 1, 45 => 1, 160 => 1],
  sparse![322; 1 => 1, 6 => 2, 13 => -1, 45 => 1, 160 => 2, 321 => -1],
  sparse![322; 0 => 1, 6 => -1, 13 => 2, 22 => 1, 160 => -1, 321 => 2],
  sparse![322; 0 => 1, 13 => 1, 22 => 1, 321 => 1],
  sparse![322; 0 => 1, 6 => 2, 13 => -1, 22 => 1, 160 => 2, 321 => -1],
  sparse![322; 0 => 2, 1 => -1, 6 => -1, 13 => 2, 22 => 2, 45 => -1, 160 => -1, 321 => 2],
  sparse![322; 0 => 2, 1 => -1, 13 => 1, 22 => 2, 45 => -1, 321 => 1],
  sparse![322; 0 => 2, 1 => -1, 6 => 1, 22 => 2, 45 => -1, 160 => 1],
  sparse![322; 0 => 2, 1 => -1, 6 => 2, 13 => -1, 22 => -1, 45 => 2, 160 => -1, 321 => 2],
]
```

### Level 323

dim S₂ = **29**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **60**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![323; 0 => 2, 322 => 2],
  sparse![323; 0 => 1, 16 => 1, 18 => 1, 322 => 1],
  sparse![323; 16 => 2, 18 => 2],
]
```

### Level 324

dim S₂ = **37**; eta rank = **37**; full eta basis = **YES**; Sturm bound B = **108**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![324; 2 => 2, 8 => 2],
  sparse![324; 5 => 2, 17 => 2],
  sparse![324; 8 => 2, 26 => 2],
  sparse![324; 11 => 2, 35 => 2],
  sparse![324; 17 => 2, 53 => 2],
  sparse![324; 35 => 2, 107 => 2],
  sparse![324; 5 => 4],
  sparse![324; 17 => 4],
  sparse![324; 53 => 4],
  sparse![324; 0 => -1, 1 => 2, 5 => 2, 8 => 1],
  sparse![324; 0 => -1, 1 => 2, 2 => 1, 17 => 1, 26 => 2, 53 => -1],
  sparse![324; 1 => -1, 3 => 2, 11 => 2, 17 => 1],
  sparse![324; 1 => -1, 3 => 2, 5 => 1, 35 => 1, 53 => 2, 107 => -1],
  sparse![324; 2 => -1, 5 => 2, 17 => 2, 26 => 1],
  sparse![324; 2 => -1, 5 => 2, 8 => 1, 53 => 1, 80 => 2, 161 => -1],
  sparse![324; 5 => -1, 11 => 2, 35 => 2, 53 => 1],
  sparse![324; 5 => -1, 11 => 2, 17 => 1, 107 => 1, 161 => 2, 323 => -1],
  sparse![324; 2 => -1, 8 => 6, 26 => -1],
  sparse![324; 2 => 1, 8 => 2, 26 => 1],
  sparse![324; 5 => -1, 17 => 6, 53 => -1],
  sparse![324; 5 => 1, 17 => 2, 53 => 1],
  sparse![324; 11 => -1, 35 => 6, 107 => -1],
  sparse![324; 11 => 1, 35 => 2, 107 => 1],
  sparse![324; 1 => 3, 17 => 1],
  sparse![324; 5 => 3, 53 => 1],
  sparse![324; 0 => -1, 1 => 2, 2 => -1, 5 => 2, 8 => 1, 26 => 1],
  sparse![324; 0 => -1, 1 => 2, 5 => -1, 8 => 1, 17 => 4, 53 => -1],
  sparse![324; 0 => -1, 1 => 2, 5 => -1, 8 => 2, 17 => 2, 26 => -1, 80 => 2, 161 => -1],
  sparse![324; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 17 => 1, 26 => 2],
  sparse![324; 1 => -1, 3 => 2, 5 => -1, 11 => 2, 17 => 1, 53 => 1],
  sparse![324; 1 => -1, 3 => 2, 11 => -1, 17 => 1, 35 => 4, 107 => -1],
  sparse![324; 1 => -1, 3 => 2, 11 => -1, 17 => 2, 35 => 2, 53 => -1, 161 => 2, 323 => -1],
  sparse![324; 1 => -1, 3 => 2, 5 => 1, 11 => -1, 35 => 1, 53 => 2],
  sparse![324; 5 => 2, 53 => 2],
  sparse![324; 0 => 1, 1 => 1, 2 => -1, 8 => 2, 53 => 1],
  sparse![324; 0 => 1, 1 => 1, 8 => 2, 26 => -1, 53 => 1],
  sparse![324; 0 => 2, 1 => -1, 17 => 1, 26 => -1, 53 => 1, 80 => 1, 161 => 1],
]
```

### Level 325

dim S₂ = **29**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **70**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 326

dim S₂ = **40**; eta rank = **2**; full eta basis = **NO**; Sturm bound B = **82**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![326; 0 => 3, 1 => -1, 162 => -1, 325 => 3],
  sparse![326; 0 => -1, 1 => 3, 162 => 3, 325 => -1],
]
```

### Level 327

dim S₂ = **35**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **73**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 328

dim S₂ = **39**; eta rank = **22**; full eta basis = **NO**; Sturm bound B = **84**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![328; 0 => 2, 1 => -1, 3 => 1, 40 => -2, 81 => 5, 163 => -1],
  sparse![328; 0 => 1, 1 => -1, 3 => 2, 40 => -1, 81 => 5, 163 => -2],
  sparse![328; 0 => 1, 1 => 2, 3 => -1, 40 => -1, 81 => 2, 163 => 1],
  sparse![328; 1 => 2, 81 => 2],
  sparse![328; 0 => -1, 1 => 2, 3 => 1, 40 => 1, 81 => 2, 163 => -1],
  sparse![328; 0 => -1, 1 => 5, 3 => -2, 40 => 1, 81 => -1, 163 => 2],
  sparse![328; 0 => -2, 1 => 5, 3 => -1, 40 => 2, 81 => -1, 163 => 1],
  sparse![328; 1 => 2, 3 => -1, 7 => 1, 81 => -2, 163 => 5, 327 => -1],
  sparse![328; 1 => 1, 3 => -1, 7 => 2, 81 => -1, 163 => 5, 327 => -2],
  sparse![328; 1 => 1, 3 => 2, 7 => -1, 81 => -1, 163 => 2, 327 => 1],
  sparse![328; 3 => 2, 163 => 2],
  sparse![328; 1 => -1, 3 => 2, 7 => 1, 81 => 1, 163 => 2, 327 => -1],
  sparse![328; 1 => -1, 3 => 5, 7 => -2, 81 => 1, 163 => -1, 327 => 2],
  sparse![328; 1 => -2, 3 => 5, 7 => -1, 81 => 2, 163 => -1, 327 => 1],
  sparse![328; 0 => -1, 1 => 2, 7 => 1, 40 => 1, 81 => -2, 163 => 4, 327 => -1],
  sparse![328; 0 => 1, 1 => -1, 3 => 1, 7 => 1, 40 => -1, 81 => 1, 163 => 3, 327 => -1],
  sparse![328; 0 => -1, 1 => 1, 3 => 3, 7 => -1, 40 => 1, 81 => -1, 163 => 1, 327 => 1],
  sparse![328; 0 => 1, 1 => -2, 3 => 4, 7 => -1, 40 => -1, 81 => 2, 327 => 1],
  sparse![328; 0 => -1, 1 => 4, 3 => -2, 7 => 1, 40 => 1, 163 => 2, 327 => -1],
  sparse![328; 0 => 1, 1 => 1, 3 => -1, 7 => 1, 40 => -1, 81 => 3, 163 => 1, 327 => -1],
  sparse![328; 0 => -1, 1 => 3, 3 => 1, 7 => -1, 40 => 1, 81 => 1, 163 => -1, 327 => 1],
  sparse![328; 0 => 1, 3 => 2, 7 => -1, 40 => -1, 81 => 4, 163 => -2, 327 => 1],
]
```

### Level 329

dim S₂ = **31**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **64**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![329; 0 => 2, 46 => 2],
  sparse![329; 6 => 2, 328 => 2],
  sparse![329; 0 => 1, 6 => 1, 46 => 1, 328 => 1],
]
```

### Level 330

dim S₂ = **65**; eta rank = **65**; full eta basis = **YES**; Sturm bound B = **144**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![330; 0 => -3, 1 => 5, 2 => 2, 4 => 2, 5 => -2, 9 => -2, 10 => 2, 14 => -1, 21 => -2, 29 => 1, 32 => -1, 54 => -3, 65 => 1, 109 => 5, 164 => 2, 329 => -2],
  sparse![330; 0 => -2, 1 => 1, 2 => 4, 4 => 4, 5 => -2, 9 => -2, 10 => 1, 14 => -2, 29 => 1, 32 => -1, 54 => -1, 65 => 1, 109 => 1, 164 => 1],
  sparse![330; 0 => -2, 1 => 2, 2 => 1, 4 => 5, 5 => -1, 9 => -3, 10 => 5, 14 => -2, 21 => -3, 29 => 2, 32 => -2, 54 => -2, 65 => 2, 109 => 2, 164 => 1, 329 => -1],
  sparse![330; 0 => -2, 1 => 2, 2 => 3, 4 => 3, 5 => -2, 9 => -2, 10 => 1, 14 => -2, 21 => -1, 29 => 2, 65 => 1, 109 => 1, 164 => 1, 329 => -1],
  sparse![330; 0 => -2, 1 => 2, 2 => 3, 4 => 3, 5 => -2, 9 => -2, 10 => 1, 14 => -2, 29 => 2, 32 => -1, 54 => -1, 65 => 1, 109 => 1, 164 => 1],
  sparse![330; 0 => -2, 1 => 2, 2 => 5, 4 => 1, 5 => -3, 9 => -1, 10 => 1, 14 => -2, 21 => -1, 29 => 2, 32 => -2, 54 => -2, 65 => 2, 109 => 2, 164 => 5, 329 => -3],
  sparse![330; 0 => -2, 1 => 3, 2 => 2, 4 => 1, 5 => -1, 9 => -1, 10 => 1, 21 => -1, 54 => -1, 109 => 2, 164 => -1, 329 => 2],
  sparse![330; 0 => -2, 1 => 3, 2 => 2, 4 => 2, 5 => -2, 9 => -2, 10 => 1, 14 => -2, 21 => -1, 29 => 3, 65 => 1, 109 => 1, 164 => 1, 329 => -1],
  sparse![330; 0 => -2, 1 => 3, 2 => 2, 4 => 2, 5 => -2, 9 => -2, 10 => 1, 14 => -2, 29 => 3, 32 => -1, 54 => -1, 65 => 1, 109 => 1, 164 => 1],
  sparse![330; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 54 => 4, 109 => -2, 164 => -1, 329 => 1],
  sparse![330; 0 => -2, 1 => 4, 2 => 1, 4 => 1, 5 => -2, 9 => -2, 10 => 1, 14 => -2, 21 => -1, 29 => 4, 65 => 1, 109 => 1, 164 => 1, 329 => -1],
  sparse![330; 0 => -1, 4 => 4, 5 => 1, 9 => -1, 10 => 4, 14 => -1, 21 => -1, 32 => -1, 54 => -1, 329 => 1],
  sparse![330; 0 => -1, 2 => 2, 4 => 2, 14 => -1, 21 => 1, 32 => 1, 54 => 1, 65 => -1, 109 => -1, 329 => 1],
  sparse![330; 0 => -1, 2 => 4, 5 => -1, 9 => 1, 14 => -1, 21 => 1, 32 => -1, 54 => -1, 164 => 4, 329 => -1],
  sparse![330; 0 => -1, 1 => 1, 4 => 2, 9 => -1, 10 => 3, 14 => 2, 21 => -2, 29 => -1, 32 => -1, 54 => -1, 65 => 2, 109 => 1],
  sparse![330; 0 => -1, 1 => 1, 4 => 2, 5 => 1, 9 => -1, 10 => 1, 32 => 1, 65 => -1, 164 => -1, 329 => 2],
  sparse![330; 0 => -1, 1 => 1, 4 => 3, 9 => -2, 10 => 2, 14 => -1, 21 => -1, 29 => 2, 32 => 2, 54 => -1, 65 => -1, 109 => 1],
  sparse![330; 0 => -1, 1 => 1, 4 => 3, 9 => -1, 10 => 3, 21 => -1, 54 => -1, 109 => 1],
  sparse![330; 0 => -1, 1 => 1, 2 => 1, 4 => 1, 14 => -1, 29 => 1, 32 => 2, 54 => 2, 65 => -1, 109 => -1],
  sparse![330; 0 => -1, 1 => 1, 2 => 1, 4 => 1, 54 => 2, 65 => 1, 109 => -1, 164 => -1, 329 => 1],
  sparse![330; 0 => -1, 1 => 1, 2 => 1, 4 => 2, 5 => -1, 9 => -1, 10 => 1, 14 => -1, 29 => 2, 65 => 1],
  sparse![330; 0 => -1, 1 => 1, 2 => 1, 4 => 2, 9 => -1, 10 => -1, 21 => 1, 32 => 1, 54 => 2, 109 => -1],
  sparse![330; 0 => -1, 1 => 1, 2 => 1, 4 => 2, 9 => -1, 10 => -1, 21 => 2, 54 => 1, 109 => -1, 329 => 1],
  sparse![330; 0 => -1, 1 => 1, 2 => 1, 4 => 2, 9 => -1, 14 => -1, 21 => 1, 29 => 1, 54 => -1, 109 => 1, 164 => 2, 329 => -1],
  sparse![330; 0 => -1, 1 => 1, 2 => 2, 4 => -1, 5 => -1, 9 => 2, 14 => 1, 29 => -1, 32 => 1, 109 => 1],
  sparse![330; 0 => -1, 1 => 1, 2 => 2, 4 => -1, 5 => -1, 9 => 2, 10 => 2, 21 => -1, 54 => 1, 109 => -1, 164 => -1, 329 => 2],
  sparse![330; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 10 => -1, 14 => 1, 21 => 1, 32 => 2, 65 => -1, 164 => 1],
  sparse![330; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 29 => 1, 32 => 1, 54 => 1, 109 => -1, 164 => -1, 329 => 2],
  sparse![330; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 10 => 1, 14 => 2, 21 => -1, 29 => -1, 32 => -1, 54 => -1, 65 => 2, 109 => 1, 164 => 2, 329 => -1],
  sparse![330; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 9 => 1, 32 => 1, 54 => 1, 164 => -1, 329 => 1],
  sparse![330; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 9 => 1, 21 => 1, 164 => -1, 329 => 2],
  sparse![330; 0 => -1, 1 => 1, 2 => 2, 4 => 1, 5 => -1, 9 => -1, 14 => -1, 29 => 2, 32 => 2, 54 => -1, 65 => -1, 109 => 1, 164 => 2, 329 => -1],
  sparse![330; 0 => -1, 1 => 1, 2 => 2, 4 => 1, 5 => -1, 9 => -1, 10 => 1, 14 => -1, 21 => -1, 29 => 2, 32 => -1, 65 => 2, 164 => -1, 329 => 2],
  sparse![330; 0 => -1, 1 => 1, 2 => 2, 4 => 1, 5 => -1, 10 => -1, 21 => 1, 32 => 2, 54 => 1, 65 => -1],
  sparse![330; 0 => -1, 1 => 1, 2 => 2, 4 => 1, 5 => -1, 10 => -1, 21 => 2, 32 => 1, 65 => -1, 329 => 1],
  sparse![330; 0 => -1, 1 => 1, 2 => 2, 4 => 1, 5 => -1, 10 => 2, 14 => -1, 21 => -1, 29 => 1, 32 => -1, 65 => 1, 329 => 1],
  sparse![330; 0 => -1, 1 => 1, 2 => 2, 4 => 2, 5 => -2, 9 => -2, 10 => 2, 14 => -3, 21 => -2, 29 => 5, 32 => -3, 54 => -1, 65 => 5, 109 => 1, 164 => 2, 329 => -2],
  sparse![330; 0 => -1, 1 => 1, 2 => 2, 4 => 2, 5 => -1, 9 => -1, 10 => -1, 14 => -1, 21 => 1, 29 => 1, 32 => 2, 54 => 2, 65 => -1, 109 => -1, 164 => -1, 329 => 1],
  sparse![330; 0 => -1, 1 => 1, 2 => 2, 4 => 2, 5 => -1, 9 => -1, 10 => -1, 14 => -1, 21 => 2, 29 => 1, 32 => 1, 54 => 1, 65 => -1, 109 => -1, 164 => -1, 329 => 2],
  sparse![330; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 10 => -1, 21 => 1, 32 => 3, 65 => -1],
  sparse![330; 0 => -1, 1 => 1, 2 => 3, 4 => 3, 5 => -1, 9 => -1, 14 => -1, 29 => 1],
  sparse![330; 0 => -1, 1 => 1, 2 => 4, 5 => -2, 54 => 1, 109 => -1, 164 => -2, 329 => 4],
  sparse![330; 0 => -1, 1 => 2, 2 => -1, 5 => 2, 14 => 1, 29 => -1, 32 => 1, 54 => 2, 65 => -1, 109 => -1, 164 => -2, 329 => 3],
  sparse![330; 0 => -1, 1 => 2, 2 => -1, 4 => 1, 5 => 2, 9 => -1, 10 => 1, 21 => -1, 54 => -2, 109 => 3, 164 => 2, 329 => -1],
  sparse![330; 0 => -1, 1 => 2, 4 => -1, 9 => 1, 10 => 1, 14 => 2, 21 => -1, 29 => -1, 32 => -1, 54 => 2, 65 => 2, 109 => -1],
  sparse![330; 0 => -1, 1 => 2, 4 => -1, 9 => 2, 10 => -1, 14 => 1, 21 => 2, 29 => -1, 32 => 1, 54 => 2, 65 => -1, 109 => -1, 164 => -1, 329 => 1],
  sparse![330; 0 => -1, 1 => 2, 10 => -1, 14 => 1, 21 => 2, 164 => 1],
  sparse![330; 0 => -1, 1 => 2, 14 => -1, 29 => 2, 32 => 2, 54 => 2, 65 => -1, 109 => -1],
  sparse![330; 0 => -1, 1 => 2, 29 => 1, 54 => 2, 65 => 1, 109 => -1, 164 => -1, 329 => 1],
  sparse![330; 0 => -1, 1 => 2, 14 => 2, 29 => -1, 32 => 2, 54 => -1, 65 => -1, 109 => 2],
  sparse![330; 0 => -1, 1 => 2, 9 => 1, 10 => 1, 54 => 2, 109 => -1],
  sparse![330; 0 => -1, 1 => 2, 4 => 1, 9 => -1, 10 => -1, 21 => 1, 29 => 1, 32 => 1, 54 => 2, 109 => -1],
  sparse![330; 0 => -1, 1 => 2, 4 => 1, 9 => -1, 10 => -1, 21 => 2, 29 => 1, 54 => 1, 109 => -1, 329 => 1],
  sparse![330; 0 => -1, 1 => 2, 4 => 1, 9 => -1, 14 => -1, 21 => 1, 29 => 2, 54 => -1, 109 => 1, 164 => 2, 329 => -1],
  sparse![330; 0 => -1, 1 => 2, 4 => 1, 9 => -1, 14 => 1, 32 => 2, 65 => -1, 109 => 1, 164 => -1, 329 => 1],
  sparse![330; 0 => -1, 1 => 2, 4 => 1, 10 => -1, 21 => 2, 54 => 1],
  sparse![330; 0 => -1, 1 => 2, 4 => 2, 9 => -1, 10 => 2, 21 => -1, 54 => -1, 109 => 2],
  sparse![330; 0 => -1, 1 => 2, 2 => 1, 4 => -1, 5 => -1, 9 => 1, 14 => 2, 21 => 1, 29 => -1, 164 => 1],
  sparse![330; 0 => -1, 1 => 2, 2 => 1, 4 => -1, 5 => -1, 9 => 2, 10 => 2, 21 => -1, 32 => -1, 54 => -1, 65 => 1, 109 => 2, 164 => 1, 329 => -1],
  sparse![330; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 10 => -1, 21 => 1, 29 => 1, 32 => 2, 54 => 1, 65 => -1],
  sparse![330; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 10 => -1, 21 => 2, 29 => 1, 32 => 1, 65 => -1, 329 => 1],
  sparse![330; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 14 => 1, 32 => 1, 54 => 2, 109 => -1],
  sparse![330; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 14 => 1, 21 => 1, 54 => 1, 109 => -1, 329 => 1],
  sparse![330; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 14 => 2, 29 => -1, 32 => -1, 54 => 2, 65 => 2, 109 => -1, 164 => -1, 329 => 1],
  sparse![330; 2 => -1, 4 => -1, 5 => 1, 9 => 2, 10 => 2, 14 => 3, 21 => -1, 29 => -2, 32 => 2, 65 => -1, 164 => -1, 329 => 1],
]
```

### Level 331

dim S₂ = **27**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **55**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 332

dim S₂ = **40**; eta rank = **4**; full eta basis = **NO**; Sturm bound B = **84**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![332; 0 => 2, 82 => 2],
  sparse![332; 1 => 2, 165 => 2],
  sparse![332; 3 => 2, 331 => 2],
  sparse![332; 0 => -2, 1 => 6, 3 => -2, 82 => -2, 165 => 6, 331 => -2],
]
```

### Level 333

dim S₂ = **35**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **76**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 334

dim S₂ = **41**; eta rank = **5**; full eta basis = **NO**; Sturm bound B = **84**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![334; 0 => 2, 166 => 2],
  sparse![334; 1 => 2, 333 => 2],
  sparse![334; 0 => -1, 1 => 3, 166 => -1, 333 => 3],
  sparse![334; 0 => 1, 1 => 1, 166 => 1, 333 => 1],
  sparse![334; 0 => 3, 1 => -1, 166 => 3, 333 => -1],
]
```

### Level 335

dim S₂ = **33**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **68**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![335; 0 => 2, 334 => 2],
  sparse![335; 0 => 1, 4 => 1, 66 => 1, 334 => 1],
  sparse![335; 4 => 2, 66 => 2],
]
```

### Level 336

dim S₂ = **53**; eta rank = **53**; full eta basis = **YES**; Sturm bound B = **128**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![336; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![336; 1 => 1, 3 => 1, 13 => 1, 27 => 1],
  sparse![336; 2 => 1, 5 => 1, 20 => 1, 41 => 1],
  sparse![336; 3 => 1, 7 => 1, 27 => 1, 55 => 1],
  sparse![336; 5 => 1, 11 => 1, 41 => 1, 83 => 1],
  sparse![336; 7 => 1, 15 => 1, 55 => 1, 111 => 1],
  sparse![336; 11 => 1, 23 => 1, 83 => 1, 167 => 1],
  sparse![336; 23 => 1, 47 => 1, 167 => 1, 335 => 1],
  sparse![336; 1 => 1, 3 => 1, 5 => 1, 11 => 1],
  sparse![336; 3 => 1, 7 => 1, 11 => 1, 23 => 1],
  sparse![336; 13 => 1, 27 => 1, 41 => 1, 83 => 1],
  sparse![336; 27 => 1, 55 => 1, 83 => 1, 167 => 1],
  sparse![336; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 6 => 4, 13 => -2, 20 => -1, 41 => 1],
  sparse![336; 0 => -1, 1 => 1, 2 => 4, 5 => -2, 6 => 1, 13 => -1, 20 => -2, 41 => 4],
  sparse![336; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 6 => -1, 13 => 2, 20 => 2, 41 => -1],
  sparse![336; 1 => -2, 3 => 4, 5 => 1, 11 => -1, 13 => 4, 27 => -2, 41 => -1, 83 => 1],
  sparse![336; 1 => -1, 3 => 1, 5 => 4, 11 => -2, 13 => 1, 27 => -1, 41 => -2, 83 => 4],
  sparse![336; 3 => -2, 7 => 4, 11 => 1, 23 => -1, 27 => 4, 55 => -2, 83 => -1, 167 => 1],
  sparse![336; 3 => -1, 7 => 1, 11 => 4, 23 => -2, 27 => 1, 55 => -1, 83 => -2, 167 => 4],
  sparse![336; 7 => -2, 15 => 4, 23 => 1, 47 => -1, 55 => 4, 111 => -2, 167 => -1, 335 => 1],
  sparse![336; 7 => -1, 15 => 1, 23 => 4, 47 => -2, 55 => 1, 111 => -1, 167 => -2, 335 => 4],
  sparse![336; 0 => -2, 1 => 4, 2 => 2, 5 => -2, 11 => 2],
  sparse![336; 6 => -2, 13 => 4, 20 => 2, 41 => -2, 83 => 2],
  sparse![336; 0 => 1, 6 => 1, 7 => 1, 55 => 1],
  sparse![336; 1 => -1, 3 => 3, 13 => 3, 27 => -1],
  sparse![336; 1 => 1, 13 => 1, 15 => 1, 111 => 1],
  sparse![336; 3 => -1, 7 => 3, 27 => 3, 55 => -1],
  sparse![336; 2 => 1, 20 => 1, 23 => 1, 167 => 1],
  sparse![336; 5 => -1, 11 => 3, 41 => 3, 83 => -1],
  sparse![336; 5 => 1, 41 => 1, 47 => 1, 335 => 1],
  sparse![336; 11 => -1, 23 => 3, 83 => 3, 167 => -1],
  sparse![336; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -2, 11 => 1, 13 => 4, 27 => -2, 41 => -1, 83 => 1],
  sparse![336; 0 => -3, 1 => 7, 2 => 2, 3 => -2, 5 => -3, 6 => 1, 11 => 1, 13 => -3, 20 => -2, 27 => 2, 41 => 7, 83 => -3],
  sparse![336; 1 => -3, 3 => 7, 5 => 1, 7 => -2, 11 => -2, 23 => 1, 27 => 4, 55 => -2, 83 => -1, 167 => 1],
  sparse![336; 1 => -3, 3 => 7, 5 => 2, 7 => -2, 11 => -3, 13 => 1, 23 => 1, 27 => -3, 41 => -2, 55 => 2, 83 => 7, 167 => -3],
  sparse![336; 3 => -3, 7 => 7, 11 => 1, 15 => -2, 23 => -2, 47 => 1, 55 => 4, 111 => -2, 167 => -1, 335 => 1],
  sparse![336; 3 => -3, 7 => 7, 11 => 2, 15 => -2, 23 => -3, 27 => 1, 47 => 1, 55 => -3, 83 => -2, 111 => 2, 167 => 7, 335 => -3],
  sparse![336; 0 => -3, 1 => 7, 3 => -2, 6 => 1, 13 => 1],
  sparse![336; 0 => -2, 1 => 4, 6 => 2, 13 => -2, 27 => 2],
  sparse![336; 0 => -2, 1 => 5, 3 => -2, 7 => 2, 15 => -1, 55 => 1, 111 => 1],
  sparse![336; 2 => -3, 5 => 7, 11 => -2, 20 => 1, 41 => 1],
  sparse![336; 2 => -2, 5 => 4, 20 => 2, 41 => -2, 83 => 2],
  sparse![336; 2 => -2, 5 => 5, 11 => -2, 23 => 2, 47 => -1, 167 => 1, 335 => 1],
  sparse![336; 1 => 2, 3 => -2, 5 => -1, 7 => 1, 11 => 3, 23 => -1, 41 => 1, 55 => 1, 83 => 1, 167 => -1],
  sparse![336; 1 => -1, 3 => 3, 5 => 2, 7 => -1, 11 => -2, 13 => 1, 23 => 1, 27 => 1, 55 => -1, 167 => 1],
  sparse![336; 3 => 2, 7 => -2, 11 => -1, 15 => 1, 23 => 3, 47 => -1, 83 => 1, 111 => 1, 167 => 1, 335 => -1],
  sparse![336; 3 => -1, 7 => 3, 11 => 2, 15 => -1, 23 => -2, 27 => 1, 47 => 1, 55 => 1, 111 => -1, 335 => 1],
  sparse![336; 1 => 2, 3 => 1, 5 => -1, 7 => -1, 11 => 1, 41 => 1, 167 => 1],
  sparse![336; 1 => -1, 3 => 1, 5 => 2, 11 => 1, 13 => 1, 23 => -1, 55 => 1],
  sparse![336; 5 => 1, 13 => 2, 23 => 1, 27 => 1, 41 => -1, 55 => -1, 83 => 1],
  sparse![336; 0 => 1, 1 => 1, 20 => -1, 41 => 1, 83 => 2],
  sparse![336; 0 => -1, 1 => 1, 3 => 2, 20 => 1, 41 => 1],
  sparse![336; 0 => 2, 1 => -1, 7 => 1, 55 => 1, 111 => -1, 167 => 1, 335 => 1],
]
```

### Level 337

dim S₂ = **27**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **56**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 338

dim S₂ = **32**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **91**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 339

dim S₂ = **37**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **76**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![339; 0 => 1, 2 => 1, 112 => 1, 338 => 1],
]
```

### Level 340

dim S₂ = **49**; eta rank = **49**; full eta basis = **YES**; Sturm bound B = **108**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![340; 1 => 2, 9 => 2],
  sparse![340; 33 => 2, 169 => 2],
  sparse![340; 0 => 2, 1 => -1, 3 => 1, 16 => -2, 33 => 5, 67 => -1],
  sparse![340; 0 => 1, 1 => -1, 3 => 2, 16 => -1, 33 => 5, 67 => -2],
  sparse![340; 0 => 1, 1 => 2, 3 => -1, 16 => -1, 33 => 2, 67 => 1],
  sparse![340; 1 => 2, 33 => 2],
  sparse![340; 0 => -1, 1 => 2, 3 => 1, 16 => 1, 33 => 2, 67 => -1],
  sparse![340; 0 => -1, 1 => 5, 3 => -2, 16 => 1, 33 => -1, 67 => 2],
  sparse![340; 0 => -2, 1 => 5, 3 => -1, 16 => 2, 33 => -1, 67 => 1],
  sparse![340; 4 => 2, 9 => -1, 19 => 1, 84 => -2, 169 => 5, 339 => -1],
  sparse![340; 4 => 1, 9 => -1, 19 => 2, 84 => -1, 169 => 5, 339 => -2],
  sparse![340; 4 => 1, 9 => 2, 19 => -1, 84 => -1, 169 => 2, 339 => 1],
  sparse![340; 9 => 2, 169 => 2],
  sparse![340; 4 => -1, 9 => 2, 19 => 1, 84 => 1, 169 => 2, 339 => -1],
  sparse![340; 4 => -1, 9 => 5, 19 => -2, 84 => 1, 169 => -1, 339 => 2],
  sparse![340; 4 => -2, 9 => 5, 19 => -1, 84 => 2, 169 => -1, 339 => 1],
  sparse![340; 1 => 2, 3 => -1, 4 => -1, 9 => 2, 67 => 1, 84 => 1],
  sparse![340; 0 => 1, 9 => -1, 16 => 1, 19 => 2, 84 => -2, 169 => 5, 339 => -2],
  sparse![340; 3 => 1, 4 => 2, 9 => -1, 67 => 1, 84 => -2, 169 => 5, 339 => -2],
  sparse![340; 1 => -1, 3 => 2, 4 => 1, 16 => -2, 33 => 5, 67 => -2, 84 => 1],
  sparse![340; 0 => 1, 4 => -2, 9 => 5, 16 => 1, 19 => -2, 169 => -1, 339 => 2],
  sparse![340; 0 => 2, 1 => -1, 16 => -2, 19 => 1, 33 => 5, 67 => -2, 339 => 1],
  sparse![340; 3 => 1, 4 => -2, 9 => 5, 19 => -2, 67 => 1, 84 => 2, 169 => -1],
  sparse![340; 0 => -2, 1 => 5, 3 => -2, 4 => 1, 33 => -1, 67 => 2, 84 => 1],
  sparse![340; 0 => -2, 1 => 5, 3 => -2, 16 => 2, 19 => 1, 33 => -1, 339 => 1],
  sparse![340; 3 => 1, 9 => 2, 19 => -1, 67 => 1, 169 => 2, 339 => -1],
  sparse![340; 0 => 1, 4 => -1, 9 => 2, 16 => 1, 84 => -1, 169 => 2],
  sparse![340; 1 => 2, 3 => -1, 19 => 1, 33 => 2, 67 => -1, 339 => 1],
  sparse![340; 0 => -1, 1 => 2, 4 => 1, 16 => -1, 33 => 2, 84 => 1],
  sparse![340; 1 => 1, 9 => 1, 33 => 1, 169 => 1],
  sparse![340; 3 => 1, 19 => 1, 33 => 2, 67 => -1, 169 => 2, 339 => -1],
  sparse![340; 0 => 1, 4 => 1, 16 => -1, 33 => 2, 84 => -1, 169 => 2],
  sparse![340; 1 => 2, 3 => -1, 9 => 2, 19 => -1, 67 => 1, 339 => 1],
  sparse![340; 0 => -1, 1 => 1, 3 => 1, 4 => 2, 9 => -1, 16 => -1, 33 => 3, 67 => -1, 169 => 1],
  sparse![340; 0 => 1, 1 => 1, 3 => -1, 9 => -1, 16 => -1, 19 => 2, 33 => 3, 67 => -1, 169 => 1],
  sparse![340; 0 => 2, 1 => -1, 4 => -1, 9 => 1, 19 => 1, 33 => 1, 84 => -1, 169 => 3, 339 => -1],
  sparse![340; 0 => -1, 1 => 3, 3 => -1, 9 => 1, 16 => -1, 33 => 1, 67 => 1, 84 => 2, 169 => -1],
  sparse![340; 1 => -1, 3 => 2, 4 => 1, 9 => 1, 19 => -1, 33 => 1, 84 => -1, 169 => 3, 339 => -1],
  sparse![340; 0 => -1, 1 => 3, 3 => -1, 9 => 1, 16 => 1, 33 => 1, 67 => -1, 169 => -1, 339 => 2],
  sparse![340; 0 => 1, 1 => 1, 3 => -1, 4 => -1, 9 => 1, 16 => -1, 19 => 1, 33 => 1, 67 => 1, 84 => 1, 169 => 1, 339 => -1],
  sparse![340; 0 => -4, 1 => 10, 3 => -4, 4 => 1, 9 => -2, 16 => 1, 19 => 1, 33 => -2, 67 => 1, 84 => -2, 169 => 6, 339 => -2],
  sparse![340; 0 => -2, 1 => 4, 3 => -1, 4 => 2, 9 => -2, 16 => 2, 19 => 1, 33 => -2, 67 => 1, 84 => -2, 169 => 4, 339 => -1],
  sparse![340; 0 => -2, 1 => 4, 3 => -1, 4 => 2, 9 => -1, 67 => 1, 169 => 1],
  sparse![340; 0 => -2, 1 => 5, 3 => -2, 4 => 1, 9 => -2, 19 => 2, 33 => 1, 84 => 1],
  sparse![340; 0 => -2, 1 => 5, 3 => -2, 4 => 2, 9 => -2, 19 => 1, 33 => 1, 339 => 1],
  sparse![340; 0 => -2, 1 => 6, 3 => -2, 4 => 1, 9 => -2, 16 => 1, 19 => 1, 33 => -2, 67 => 1, 84 => -4, 169 => 10, 339 => -4],
  sparse![340; 0 => -1, 1 => 1, 4 => 2, 16 => 4, 33 => -2, 84 => -1, 169 => 1],
  sparse![340; 0 => -1, 1 => 1, 4 => 4, 9 => -2, 16 => 2, 84 => -1, 169 => 1],
  sparse![340; 0 => -1, 1 => 1, 3 => 1, 4 => 1, 9 => 1, 16 => 1, 19 => -1, 33 => 1, 67 => -1, 84 => -1, 169 => 1, 339 => 1],
]
```

### Level 341

dim S₂ = **31**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **64**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![341; 0 => 2, 10 => 2],
  sparse![341; 30 => 2, 340 => 2],
  sparse![341; 0 => 1, 10 => 1, 30 => 1, 340 => 1],
]
```

### Level 342

dim S₂ = **53**; eta rank = **49**; full eta basis = **NO**; Sturm bound B = **120**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![342; 0 => 3, 1 => -1, 18 => -1, 37 => 3],
  sparse![342; 0 => -1, 1 => 3, 18 => 3, 37 => -1],
  sparse![342; 2 => 3, 5 => -1, 56 => -1, 113 => 3],
  sparse![342; 2 => -1, 5 => 3, 56 => 3, 113 => -1],
  sparse![342; 8 => 3, 17 => -1, 170 => -1, 341 => 3],
  sparse![342; 8 => -1, 17 => 3, 170 => 3, 341 => -1],
  sparse![342; 1 => 1, 2 => 2, 5 => -1, 18 => 1, 56 => -1, 113 => 2],
  sparse![342; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 18 => 1, 113 => 1],
  sparse![342; 0 => 2, 1 => -1, 5 => 1, 18 => -1, 37 => 2, 56 => 1],
  sparse![342; 0 => -1, 1 => 2, 2 => 1, 18 => 2, 37 => -1, 113 => 1],
  sparse![342; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 37 => 1, 56 => 1],
  sparse![342; 0 => -1, 1 => 1, 2 => 2, 18 => 1, 37 => -1, 113 => 2],
  sparse![342; 1 => 1, 2 => 1, 18 => -2, 37 => 3, 56 => 3, 113 => -2],
  sparse![342; 1 => 2, 2 => 1, 5 => -1, 18 => 2, 56 => -1, 113 => 1],
  sparse![342; 0 => 1, 2 => -1, 5 => 2, 37 => 1, 56 => 2, 113 => -1],
  sparse![342; 5 => 1, 8 => 2, 17 => -1, 56 => 1, 170 => -1, 341 => 2],
  sparse![342; 2 => 3, 5 => -2, 8 => -2, 17 => 3, 56 => 1, 341 => 1],
  sparse![342; 2 => 2, 5 => -1, 17 => 1, 56 => -1, 113 => 2, 170 => 1],
  sparse![342; 2 => -1, 5 => 2, 8 => 1, 56 => 2, 113 => -1, 341 => 1],
  sparse![342; 2 => -2, 5 => 3, 8 => 3, 17 => -2, 113 => 1, 170 => 1],
  sparse![342; 2 => -1, 5 => 1, 8 => 2, 56 => 1, 113 => -1, 341 => 2],
  sparse![342; 5 => 1, 8 => 1, 56 => -2, 113 => 3, 170 => 3, 341 => -2],
  sparse![342; 5 => 2, 8 => 1, 17 => -1, 56 => 2, 170 => -1, 341 => 1],
  sparse![342; 0 => 1, 8 => 1, 18 => -1, 56 => 4, 170 => -1],
  sparse![342; 2 => 2, 56 => 2],
  sparse![342; 0 => -1, 2 => 4, 8 => -1, 18 => 1, 170 => 1],
  sparse![342; 1 => 1, 17 => 1, 37 => -1, 113 => 4, 341 => -1],
  sparse![342; 5 => 2, 113 => 2],
  sparse![342; 0 => 1, 2 => 1, 5 => -1, 8 => -1, 17 => 2, 37 => 1, 56 => -1, 113 => 1, 170 => 2, 341 => -1],
  sparse![342; 2 => 1, 5 => -1, 17 => 2, 170 => -1, 341 => 3],
  sparse![342; 2 => -1, 5 => 1, 8 => 2, 170 => 3, 341 => -1],
  sparse![342; 0 => 1, 1 => -1, 2 => -1, 5 => 2, 17 => 1, 18 => -1, 37 => 1, 56 => 2, 113 => -1, 170 => 1],
  sparse![342; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 8 => 1, 18 => 1, 37 => -1, 56 => -1, 113 => 2, 341 => 1],
  sparse![342; 0 => -2, 1 => 1, 2 => 6, 5 => -2, 8 => -2, 17 => 1, 18 => 2, 37 => -1, 56 => -2, 113 => 2, 170 => 2, 341 => -1],
  sparse![342; 0 => -2, 1 => 2, 2 => 5, 5 => -3, 8 => -2, 17 => 2, 18 => -1, 37 => 1, 56 => 3, 113 => -1, 170 => -1, 341 => 1],
  sparse![342; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 8 => -1, 17 => 1, 37 => 1, 56 => -1, 113 => 2, 170 => 1, 341 => -1],
  sparse![342; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 8 => -1, 17 => 1, 18 => 1, 37 => -1, 56 => -2, 113 => 3, 170 => 3, 341 => -2],
  sparse![342; 0 => -1, 2 => 3, 5 => 1, 8 => -1, 37 => -1, 56 => 1, 113 => 3, 341 => -1],
  sparse![342; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 8 => 2, 17 => -1, 37 => 1, 56 => 1],
  sparse![342; 0 => -1, 1 => 1, 2 => 2, 8 => -1, 17 => 1, 18 => 1, 37 => -1, 56 => -2, 113 => 4, 170 => 1, 341 => -1],
  sparse![342; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 8 => -1, 17 => 1, 18 => -2, 37 => 2, 56 => 5, 113 => -3, 170 => -2, 341 => 2],
  sparse![342; 0 => -1, 1 => 2, 2 => -1, 5 => 2, 8 => 1, 17 => -1, 113 => 1, 170 => 1],
  sparse![342; 0 => -1, 1 => 2, 17 => 1, 18 => -1, 37 => 2, 56 => 1, 113 => -1, 170 => 1],
  sparse![342; 0 => -1, 1 => 2, 2 => 1, 18 => -1, 37 => 2, 56 => 1],
  sparse![342; 0 => -1, 1 => 2, 2 => 3, 5 => -2, 8 => -1, 17 => 1, 56 => 1, 341 => 1],
  sparse![342; 5 => 1, 8 => 1, 18 => -1, 37 => 2, 56 => -1, 113 => 2, 170 => 1, 341 => -1],
  sparse![342; 2 => 1, 17 => 1, 18 => -1, 37 => 2, 56 => 3, 113 => -2, 170 => -1, 341 => 1],
  sparse![342; 1 => 1, 2 => -1, 5 => 2, 18 => 1, 113 => 1],
  sparse![342; 1 => 1, 2 => -1, 5 => 2, 8 => 1, 17 => -1, 18 => -2, 37 => 3, 56 => 3, 113 => -2, 170 => -1, 341 => 1],
]
```

### Level 343

dim S₂ = **26**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **65**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 344

dim S₂ = **41**; eta rank = **18**; full eta basis = **NO**; Sturm bound B = **88**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![344; 0 => 3, 1 => -1, 42 => -1, 85 => 3],
  sparse![344; 0 => -1, 1 => 3, 42 => 3, 85 => -1],
  sparse![344; 1 => 3, 3 => -1, 85 => -1, 171 => 3],
  sparse![344; 1 => -1, 3 => 3, 85 => 3, 171 => -1],
  sparse![344; 3 => 3, 7 => -1, 171 => -1, 343 => 3],
  sparse![344; 3 => -1, 7 => 3, 171 => 3, 343 => -1],
  sparse![344; 0 => 1, 3 => 1, 42 => -3, 85 => 8, 171 => -3],
  sparse![344; 0 => -3, 1 => 8, 3 => -3, 42 => 1, 171 => 1],
  sparse![344; 1 => 1, 7 => 1, 85 => -3, 171 => 8, 343 => -3],
  sparse![344; 1 => -3, 3 => 8, 7 => -3, 85 => 1, 343 => 1],
  sparse![344; 0 => -1, 1 => 2, 7 => 1, 42 => -1, 85 => 4, 171 => -2, 343 => 1],
  sparse![344; 0 => -1, 1 => 4, 3 => -2, 7 => 1, 42 => -1, 85 => 2, 343 => 1],
  sparse![344; 0 => -1, 1 => 1, 3 => 3, 7 => -1, 42 => -1, 85 => 3, 171 => 1, 343 => -1],
  sparse![344; 0 => -1, 1 => 3, 3 => 1, 7 => -1, 42 => -1, 85 => 1, 171 => 3, 343 => -1],
  sparse![344; 1 => 1, 3 => 1, 85 => 1, 171 => 1],
  sparse![344; 0 => 1, 1 => -1, 3 => 1, 7 => 1, 42 => 1, 85 => 1, 171 => -1, 343 => 1],
  sparse![344; 0 => 1, 1 => 1, 3 => -1, 7 => 1, 42 => 1, 85 => -1, 171 => 1, 343 => 1],
  sparse![344; 0 => 1, 1 => -2, 3 => 4, 7 => -1, 42 => 1, 171 => 2, 343 => -1],
]
```

### Level 345

dim S₂ = **45**; eta rank = **14**; full eta basis = **NO**; Sturm bound B = **96**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![345; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![345; 22 => 1, 68 => 1, 114 => 1, 344 => 1],
  sparse![345; 0 => 2, 22 => 2],
  sparse![345; 2 => 2, 68 => 2],
  sparse![345; 4 => 2, 114 => 2],
  sparse![345; 14 => 2, 344 => 2],
  sparse![345; 0 => 1, 2 => 1, 22 => 1, 68 => 1],
  sparse![345; 4 => 1, 14 => 1, 114 => 1, 344 => 1],
  sparse![345; 0 => 1, 4 => 1, 22 => 1, 114 => 1],
  sparse![345; 2 => 1, 14 => 1, 68 => 1, 344 => 1],
  sparse![345; 0 => -1, 2 => 2, 4 => 2, 14 => -1, 22 => 2, 68 => -1, 114 => -1, 344 => 2],
  sparse![345; 2 => 1, 4 => 1, 68 => 1, 114 => 1],
  sparse![345; 0 => 1, 14 => 1, 22 => 1, 344 => 1],
  sparse![345; 0 => 2, 2 => -1, 4 => -1, 14 => 2, 22 => -1, 68 => 2, 114 => 2, 344 => -1],
]
```

### Level 346

dim S₂ = **42**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **87**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 347

dim S₂ = **29**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **58**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![347; 0 => 2, 346 => 2],
]
```

### Level 348

dim S₂ = **55**; eta rank = **44**; full eta basis = **NO**; Sturm bound B = **120**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![348; 0 => 1, 2 => 1, 28 => 1, 86 => 1],
  sparse![348; 1 => 1, 5 => 1, 57 => 1, 173 => 1],
  sparse![348; 3 => 1, 11 => 1, 115 => 1, 347 => 1],
  sparse![348; 1 => 2, 57 => 2],
  sparse![348; 5 => 2, 173 => 2],
  sparse![348; 0 => -1, 1 => 3, 2 => 1, 5 => -1, 28 => 1, 57 => -1, 86 => -1, 173 => 3],
  sparse![348; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 28 => 2, 57 => -1, 86 => -1, 173 => 2],
  sparse![348; 0 => 1, 1 => 1, 86 => 1, 173 => 1],
  sparse![348; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 28 => 3, 57 => -1, 86 => -1, 173 => 1],
  sparse![348; 2 => 1, 5 => 1, 28 => 1, 57 => 1],
  sparse![348; 0 => 1, 1 => -1, 2 => -1, 5 => 3, 28 => -1, 57 => 3, 86 => 1, 173 => -1],
  sparse![348; 0 => 2, 1 => -1, 2 => -1, 5 => 2, 28 => -1, 57 => 2, 86 => 2, 173 => -1],
  sparse![348; 0 => 3, 1 => -1, 2 => -1, 5 => 1, 28 => -1, 57 => 1, 86 => 3, 173 => -1],
  sparse![348; 1 => -1, 3 => 3, 5 => 1, 11 => -1, 57 => 1, 115 => -1, 173 => -1, 347 => 3],
  sparse![348; 1 => -1, 3 => 2, 5 => 2, 11 => -1, 57 => 2, 115 => -1, 173 => -1, 347 => 2],
  sparse![348; 1 => 1, 3 => 1, 173 => 1, 347 => 1],
  sparse![348; 1 => -1, 3 => 1, 5 => 3, 11 => -1, 57 => 3, 115 => -1, 173 => -1, 347 => 1],
  sparse![348; 5 => 1, 11 => 1, 57 => 1, 115 => 1],
  sparse![348; 1 => 2, 3 => -1, 5 => -1, 11 => 2, 57 => -1, 115 => 2, 173 => 2, 347 => -1],
  sparse![348; 1 => 3, 3 => -1, 5 => -1, 11 => 1, 57 => -1, 115 => 1, 173 => 3, 347 => -1],
  sparse![348; 0 => 1, 1 => -2, 2 => -3, 3 => 1, 5 => 8, 11 => -3, 57 => -1, 115 => 3, 173 => 1, 347 => -1],
  sparse![348; 0 => 2, 1 => -1, 2 => -1, 5 => 3, 11 => -1, 57 => -1, 86 => -1, 115 => 2, 173 => 3, 347 => -1],
  sparse![348; 0 => 1, 11 => 1, 86 => 1, 115 => 1],
  sparse![348; 2 => 1, 3 => 1, 28 => 1, 347 => 1],
  sparse![348; 2 => 2, 3 => 1, 5 => -1, 86 => -2, 115 => 1, 173 => 5, 347 => -2],
  sparse![348; 0 => 1, 2 => -2, 5 => 5, 11 => -2, 28 => 1, 173 => -1, 347 => 2],
  sparse![348; 2 => -2, 3 => 1, 5 => 5, 11 => -2, 86 => 2, 115 => 1, 173 => -1],
  sparse![348; 1 => -1, 2 => -1, 3 => 2, 5 => 3, 11 => -1, 28 => 2, 57 => -1, 86 => -1, 173 => 3, 347 => -1],
  sparse![348; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 57 => -1, 86 => 1, 115 => 2],
  sparse![348; 0 => -2, 1 => 5, 2 => 1, 3 => -1, 5 => -2, 11 => 1, 28 => 1, 57 => -2, 86 => -2, 115 => 1, 173 => 5, 347 => -1],
  sparse![348; 0 => -2, 1 => 7, 2 => 1, 3 => -3, 5 => -3, 11 => 2, 28 => 1, 57 => -3, 86 => -2, 115 => 2, 173 => 7, 347 => -3],
  sparse![348; 0 => -3, 1 => 7, 2 => 2, 3 => -2, 5 => -3, 11 => 1, 28 => 2, 57 => -3, 86 => -3, 115 => 1, 173 => 7, 347 => -2],
  sparse![348; 0 => -1, 1 => 1, 2 => 1, 3 => 2, 11 => -1, 28 => 1, 86 => -1, 115 => -1, 173 => 1, 347 => 2],
  sparse![348; 0 => -1, 1 => 2, 3 => 1, 5 => 1, 11 => -1, 57 => 1, 86 => -1, 115 => -1, 173 => 2, 347 => 1],
  sparse![348; 0 => -1, 1 => 4, 3 => -1, 86 => -1, 173 => 4, 347 => -1],
  sparse![348; 0 => 2, 1 => -1, 2 => -1, 3 => 1, 5 => 1, 28 => -1, 57 => 1, 86 => 2, 173 => -1, 347 => 1],
  sparse![348; 0 => 2, 1 => 1, 2 => -1, 3 => -1, 11 => 1, 28 => -1, 86 => 2, 115 => 1, 173 => 1, 347 => -1],
  sparse![348; 0 => -2, 1 => 6, 2 => 1, 3 => -3, 5 => -3, 11 => 3, 28 => 1, 57 => -3, 86 => -2, 115 => 3, 173 => 6, 347 => -3],
  sparse![348; 0 => -1, 1 => 4, 2 => 1, 3 => -2, 5 => -2, 11 => 2, 28 => 1, 57 => -2, 86 => -1, 115 => 2, 173 => 4, 347 => -2],
  sparse![348; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 5 => -3, 11 => 1, 28 => 3, 57 => -3, 86 => -3, 115 => 1, 173 => 6, 347 => -2],
  sparse![348; 0 => 1, 1 => -3, 2 => -2, 3 => 3, 5 => 6, 11 => -3, 28 => -2, 57 => 6, 86 => 1, 115 => -3, 173 => -3, 347 => 3],
  sparse![348; 0 => -1, 1 => 3, 2 => 1, 3 => -2, 5 => -2, 11 => 3, 28 => 1, 57 => -2, 86 => -1, 115 => 3, 173 => 3, 347 => -2],
  sparse![348; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -2, 11 => 1, 28 => 3, 57 => -2, 86 => -2, 115 => 1, 173 => 3, 347 => -1],
  sparse![348; 0 => 2, 1 => -3, 2 => -3, 3 => 1, 5 => 7, 11 => -2, 28 => -3, 57 => 7, 86 => 2, 115 => -2, 173 => -3, 347 => 1],
]
```

### Level 349

dim S₂ = **28**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **58**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 350

dim S₂ = **49**; eta rank = **49**; full eta basis = **YES**; Sturm bound B = **120**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![350; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![350; 4 => 1, 9 => 1, 34 => 1, 69 => 1],
  sparse![350; 24 => 1, 49 => 1, 174 => 1, 349 => 1],
  sparse![350; 0 => 2, 34 => 2],
  sparse![350; 0 => 1, 4 => 1, 6 => 1, 34 => 1],
  sparse![350; 4 => 2, 6 => 2],
  sparse![350; 1 => 2, 69 => 2],
  sparse![350; 1 => 1, 9 => 1, 13 => 1, 69 => 1],
  sparse![350; 9 => 2, 13 => 2],
  sparse![350; 4 => 2, 174 => 2],
  sparse![350; 4 => 1, 24 => 1, 34 => 1, 174 => 1],
  sparse![350; 24 => 2, 34 => 2],
  sparse![350; 9 => 2, 349 => 2],
  sparse![350; 9 => 1, 49 => 1, 69 => 1, 349 => 1],
  sparse![350; 49 => 2, 69 => 2],
  sparse![350; 0 => 1, 4 => 2, 9 => -1, 13 => 1, 34 => -1, 69 => 2],
  sparse![350; 4 => 1, 24 => 2, 49 => -1, 69 => 1, 174 => -1, 349 => 2],
  sparse![350; 0 => 1, 4 => 1, 34 => 1, 174 => 1],
  sparse![350; 4 => 2, 6 => 1, 174 => 1],
  sparse![350; 0 => 1, 24 => 1, 34 => 2],
  sparse![350; 4 => 1, 6 => 1, 24 => 1, 34 => 1],
  sparse![350; 1 => 1, 9 => 1, 69 => 1, 349 => 1],
  sparse![350; 9 => 2, 13 => 1, 349 => 1],
  sparse![350; 1 => 1, 49 => 1, 69 => 2],
  sparse![350; 9 => 1, 13 => 1, 49 => 1, 69 => 1],
  sparse![350; 0 => 1, 1 => 1, 174 => 1, 349 => 1],
  sparse![350; 6 => 1, 13 => 1, 24 => 1, 49 => 1],
  sparse![350; 13 => 1, 24 => 1, 49 => 1, 174 => 1],
  sparse![350; 0 => 2, 1 => -1, 34 => 2, 49 => 1],
  sparse![350; 0 => -1, 1 => 2, 24 => 1, 69 => 2],
  sparse![350; 6 => 1, 24 => 1, 49 => 1, 349 => 1],
  sparse![350; 4 => 2, 6 => 2, 13 => -1, 349 => 1],
  sparse![350; 0 => 1, 1 => -1, 4 => -1, 6 => -1, 9 => 3, 13 => 2, 34 => 1, 69 => -1, 349 => 1],
  sparse![350; 0 => -1, 1 => 1, 4 => 3, 6 => 2, 9 => -1, 13 => -1, 34 => -1, 69 => 1, 174 => 1],
  sparse![350; 0 => -1, 1 => 2, 4 => 1, 6 => 1, 9 => -1, 13 => -1, 34 => -1, 49 => 1, 69 => 3],
  sparse![350; 0 => 2, 1 => -1, 4 => -1, 6 => -1, 9 => 1, 13 => 1, 24 => 1, 34 => 3, 69 => -1],
  sparse![350; 4 => -1, 9 => 3, 13 => 1, 24 => 1, 34 => 1, 49 => -1, 69 => -1, 174 => -1, 349 => 2],
  sparse![350; 4 => 3, 6 => 1, 9 => -1, 24 => -1, 34 => -1, 49 => 1, 69 => 1, 174 => 2, 349 => -1],
  sparse![350; 1 => 1, 4 => 1, 9 => -1, 24 => -1, 34 => -1, 49 => 2, 69 => 3, 174 => 1, 349 => -1],
  sparse![350; 0 => 1, 1 => 1, 6 => 1, 349 => 1],
  sparse![350; 0 => 1, 1 => 1, 13 => 1, 174 => 1],
  sparse![350; 0 => 1, 6 => 1, 13 => 1, 49 => 1],
  sparse![350; 0 => 1, 6 => 1, 49 => 1, 349 => 1],
  sparse![350; 0 => 1, 13 => 1, 49 => 1, 174 => 1],
  sparse![350; 0 => 1, 49 => 1, 174 => 1, 349 => 1],
  sparse![350; 1 => 1, 6 => 1, 13 => 1, 24 => 1],
  sparse![350; 1 => 1, 6 => 1, 24 => 1, 349 => 1],
  sparse![350; 0 => -1, 1 => 1, 4 => 3, 9 => -1, 34 => 3, 69 => -1, 174 => -1, 349 => 1],
  sparse![350; 0 => -1, 1 => 1, 4 => 3, 6 => 1, 9 => -1, 34 => -1, 69 => 1, 174 => 2, 349 => -1],
]
```

### Level 351

dim S₂ = **37**; eta rank = **10**; full eta basis = **NO**; Sturm bound B = **84**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![351; 2 => 2, 8 => 2],
  sparse![351; 38 => 2, 116 => 2],
  sparse![351; 8 => 3, 26 => -1, 38 => 2, 116 => -1, 350 => 1],
  sparse![351; 0 => 1, 2 => -1, 8 => 2, 12 => -1, 38 => 3],
  sparse![351; 2 => 2, 116 => 2],
  sparse![351; 2 => 1, 8 => 1, 38 => 1, 116 => 1],
  sparse![351; 0 => -1, 2 => 3, 12 => 1, 38 => -1, 116 => 2],
  sparse![351; 2 => 2, 8 => -1, 26 => 1, 116 => 3, 350 => -1],
  sparse![351; 8 => 2, 38 => 2],
  sparse![351; 2 => 3, 8 => -1, 38 => -1, 116 => 3],
]
```

### Level 352

dim S₂ = **41**; eta rank = **41**; full eta basis = **YES**; Sturm bound B = **96**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![352; 0 => 2, 10 => 2],
  sparse![352; 1 => 2, 21 => 2],
  sparse![352; 3 => 2, 43 => 2],
  sparse![352; 7 => 2, 87 => 2],
  sparse![352; 15 => 2, 175 => 2],
  sparse![352; 31 => 2, 351 => 2],
  sparse![352; 3 => 2, 7 => 2],
  sparse![352; 43 => 2, 87 => 2],
  sparse![352; 0 => 1, 3 => -1, 7 => 2, 10 => 1, 21 => -2, 43 => 5, 87 => -2],
  sparse![352; 1 => 1, 3 => 1, 21 => 1, 43 => 1],
  sparse![352; 0 => -2, 1 => 4, 3 => 1, 7 => -1, 10 => 2, 21 => -2, 43 => 3, 87 => -1],
  sparse![352; 0 => -2, 1 => 5, 3 => -2, 7 => 1, 10 => 2, 21 => -1, 87 => 1],
  sparse![352; 0 => -2, 1 => 5, 3 => -1, 10 => -2, 21 => 5, 43 => -1],
  sparse![352; 1 => 1, 7 => -1, 15 => 2, 21 => 1, 43 => -2, 87 => 5, 175 => -2],
  sparse![352; 3 => 1, 7 => 1, 43 => 1, 87 => 1],
  sparse![352; 1 => -2, 3 => 4, 7 => 1, 15 => -1, 21 => 2, 43 => -2, 87 => 3, 175 => -1],
  sparse![352; 1 => -2, 3 => 5, 7 => -1, 21 => -2, 43 => 5, 87 => -1],
  sparse![352; 3 => 1, 15 => -1, 31 => 2, 43 => 1, 87 => -2, 175 => 5, 351 => -2],
  sparse![352; 7 => 1, 15 => 1, 87 => 1, 175 => 1],
  sparse![352; 3 => -2, 7 => 4, 15 => 1, 31 => -1, 43 => 2, 87 => -2, 175 => 3, 351 => -1],
  sparse![352; 3 => -2, 7 => 5, 15 => -1, 43 => -2, 87 => 5, 175 => -1],
  sparse![352; 0 => 1, 10 => -1, 15 => 1, 21 => 3, 43 => -2, 87 => 3, 175 => -1],
  sparse![352; 1 => 1, 7 => 1, 21 => 1, 87 => 1],
  sparse![352; 0 => -2, 1 => 4, 10 => 2, 21 => -2, 43 => 2],
  sparse![352; 0 => -2, 1 => 4, 3 => 1, 7 => -1, 10 => -2, 21 => 4, 43 => 1, 87 => -1],
  sparse![352; 0 => -2, 1 => 6, 3 => -2, 21 => 1, 43 => -2, 87 => 5, 175 => -2],
  sparse![352; 1 => 1, 21 => -1, 31 => 1, 43 => 3, 87 => -2, 175 => 3, 351 => -1],
  sparse![352; 3 => 1, 15 => 1, 43 => 1, 175 => 1],
  sparse![352; 1 => -2, 3 => 4, 21 => 2, 43 => -2, 87 => 2],
  sparse![352; 1 => -2, 3 => 4, 7 => 1, 15 => -1, 21 => -2, 43 => 4, 87 => 1, 175 => -1],
  sparse![352; 1 => -2, 3 => 6, 7 => -2, 43 => 1, 87 => -2, 175 => 5, 351 => -2],
  sparse![352; 7 => -2, 15 => 7, 31 => -3, 43 => 2, 175 => -1, 351 => 1],
  sparse![352; 3 => 2, 15 => -1, 31 => 1, 87 => -2, 175 => 7, 351 => -3],
  sparse![352; 0 => -3, 1 => 7, 3 => -2, 10 => 1, 21 => -1, 87 => 2],
  sparse![352; 7 => 1, 15 => 1, 43 => -2, 87 => 7, 175 => -3],
  sparse![352; 1 => 1, 15 => 1, 21 => 1, 175 => 1],
  sparse![352; 0 => -3, 1 => 8, 3 => -3, 10 => 1, 43 => -1, 87 => 2],
  sparse![352; 0 => -2, 1 => 4, 3 => -1, 7 => 2, 10 => 2, 15 => -1, 21 => -2, 43 => 1, 87 => 2, 175 => -1],
  sparse![352; 0 => -2, 1 => 4, 7 => -1, 10 => 2, 15 => 1, 21 => -2, 43 => 2, 87 => -1, 175 => 1],
  sparse![352; 0 => -2, 1 => 5, 3 => -3, 7 => 3, 10 => -2, 15 => -1, 21 => 5, 43 => -3, 87 => 3, 175 => -1],
  sparse![352; 0 => -2, 1 => 5, 3 => -3, 7 => 3, 15 => -1, 43 => -3, 87 => 8, 175 => -3],
]
```

### Level 353

dim S₂ = **29**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **59**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 354

dim S₂ = **57**; eta rank = **14**; full eta basis = **NO**; Sturm bound B = **120**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![354; 0 => 2, 58 => 2],
  sparse![354; 1 => 2, 117 => 2],
  sparse![354; 2 => 2, 176 => 2],
  sparse![354; 5 => 2, 353 => 2],
  sparse![354; 0 => 1, 2 => 1, 58 => 1, 176 => 1],
  sparse![354; 1 => 1, 5 => 1, 117 => 1, 353 => 1],
  sparse![354; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 58 => -1, 117 => 1, 176 => 3, 353 => -1],
  sparse![354; 1 => 1, 2 => 2, 5 => -1, 117 => 1, 176 => 2, 353 => -1],
  sparse![354; 0 => 2, 1 => -1, 5 => 1, 58 => 2, 117 => -1, 353 => 1],
  sparse![354; 0 => 3, 1 => -1, 2 => -1, 5 => 1, 58 => 3, 117 => -1, 176 => -1, 353 => 1],
  sparse![354; 0 => 1, 1 => -1, 2 => -1, 5 => 3, 58 => 1, 117 => -1, 176 => -1, 353 => 3],
  sparse![354; 0 => -1, 1 => 2, 2 => 1, 58 => -1, 117 => 2, 176 => 1],
  sparse![354; 0 => 1, 2 => -1, 5 => 2, 58 => 1, 176 => -1, 353 => 2],
  sparse![354; 0 => -1, 1 => 3, 2 => 1, 5 => -1, 58 => -1, 117 => 3, 176 => 1, 353 => -1],
]
```

### Level 355

dim S₂ = **35**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **72**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![355; 0 => 2, 70 => 2],
  sparse![355; 4 => 2, 354 => 2],
  sparse![355; 0 => 1, 4 => 1, 70 => 1, 354 => 1],
]
```

### Level 356

dim S₂ = **43**; eta rank = **7**; full eta basis = **NO**; Sturm bound B = **90**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![356; 0 => 2, 1 => -1, 3 => 1, 88 => -2, 177 => 5, 355 => -1],
  sparse![356; 0 => 1, 1 => -1, 3 => 2, 88 => -1, 177 => 5, 355 => -2],
  sparse![356; 0 => 1, 1 => 2, 3 => -1, 88 => -1, 177 => 2, 355 => 1],
  sparse![356; 1 => 2, 177 => 2],
  sparse![356; 0 => -1, 1 => 2, 3 => 1, 88 => 1, 177 => 2, 355 => -1],
  sparse![356; 0 => -1, 1 => 5, 3 => -2, 88 => 1, 177 => -1, 355 => 2],
  sparse![356; 0 => -2, 1 => 5, 3 => -1, 88 => 2, 177 => -1, 355 => 1],
]
```

### Level 357

dim S₂ = **45**; eta rank = **12**; full eta basis = **NO**; Sturm bound B = **96**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![357; 0 => 1, 2 => 1, 16 => 1, 50 => 1],
  sparse![357; 6 => 1, 20 => 1, 118 => 1, 356 => 1],
  sparse![357; 0 => 2, 118 => 2],
  sparse![357; 0 => 1, 6 => 1, 16 => 1, 118 => 1],
  sparse![357; 6 => 2, 16 => 2],
  sparse![357; 2 => 2, 356 => 2],
  sparse![357; 2 => 1, 20 => 1, 50 => 1, 356 => 1],
  sparse![357; 20 => 2, 50 => 2],
  sparse![357; 0 => 1, 2 => 1, 118 => 1, 356 => 1],
  sparse![357; 2 => 1, 6 => 1, 16 => 1, 356 => 1],
  sparse![357; 0 => 1, 20 => 1, 50 => 1, 118 => 1],
  sparse![357; 6 => 1, 16 => 1, 20 => 1, 50 => 1],
]
```

### Level 358

dim S₂ = **44**; eta rank = **2**; full eta basis = **NO**; Sturm bound B = **90**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![358; 0 => 2, 178 => 2],
  sparse![358; 1 => 2, 357 => 2],
]
```

### Level 359

dim S₂ = **30**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **60**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![359; 0 => 2, 358 => 2],
]
```

### Level 360

dim S₂ = **57**; eta rank = **57**; full eta basis = **YES**; Sturm bound B = **144**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![360; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![360; 1 => 1, 5 => 1, 9 => 1, 29 => 1],
  sparse![360; 2 => 1, 8 => 1, 14 => 1, 44 => 1],
  sparse![360; 3 => 1, 11 => 1, 19 => 1, 59 => 1],
  sparse![360; 5 => 1, 17 => 1, 29 => 1, 89 => 1],
  sparse![360; 7 => 1, 23 => 1, 39 => 1, 119 => 1],
  sparse![360; 11 => 1, 35 => 1, 59 => 1, 179 => 1],
  sparse![360; 23 => 1, 71 => 1, 119 => 1, 359 => 1],
  sparse![360; 1 => 2, 9 => 2],
  sparse![360; 3 => 2, 19 => 2],
  sparse![360; 5 => 2, 29 => 2],
  sparse![360; 11 => 2, 59 => 2],
  sparse![360; 17 => 2, 89 => 2],
  sparse![360; 35 => 2, 179 => 2],
  sparse![360; 1 => 1, 3 => 1, 5 => 1, 11 => 1],
  sparse![360; 5 => 1, 11 => 1, 17 => 1, 35 => 1],
  sparse![360; 9 => 1, 19 => 1, 29 => 1, 59 => 1],
  sparse![360; 29 => 1, 59 => 1, 89 => 1, 179 => 1],
  sparse![360; 0 => 1, 1 => 1, 14 => 1, 29 => 1],
  sparse![360; 1 => 1, 3 => 1, 29 => 1, 59 => 1],
  sparse![360; 2 => 1, 5 => 1, 44 => 1, 89 => 1],
  sparse![360; 3 => 1, 7 => 1, 59 => 1, 119 => 1],
  sparse![360; 5 => 1, 11 => 1, 89 => 1, 179 => 1],
  sparse![360; 11 => 1, 23 => 1, 179 => 1, 359 => 1],
  sparse![360; 5 => 4],
  sparse![360; 11 => 4],
  sparse![360; 29 => 4],
  sparse![360; 59 => 4],
  sparse![360; 0 => -2, 1 => 5, 3 => -1, 4 => 2, 9 => -1, 19 => 1],
  sparse![360; 2 => -2, 5 => 5, 11 => -1, 14 => 2, 29 => -1, 59 => 1],
  sparse![360; 8 => -2, 17 => 5, 35 => -1, 44 => 2, 89 => -1, 179 => 1],
  sparse![360; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -1, 11 => 2],
  sparse![360; 4 => -3, 9 => 7, 14 => 1, 19 => -2, 29 => -1, 59 => 2],
  sparse![360; 0 => -2, 1 => 1, 2 => 7, 5 => -3, 8 => -2, 14 => 1, 17 => 1, 29 => 1],
  sparse![360; 0 => -2, 1 => 3, 2 => 2, 4 => 1, 5 => -1, 14 => 1],
  sparse![360; 0 => -1, 1 => 1, 2 => 1, 4 => 1, 5 => 1, 8 => 1, 17 => -1, 89 => 1],
  sparse![360; 0 => -1, 1 => 2, 8 => 1, 14 => 3, 29 => -1, 44 => -1, 89 => 1],
  sparse![360; 0 => -1, 1 => 2, 5 => 1, 8 => 1, 17 => -1, 29 => 1, 89 => 1],
  sparse![360; 1 => -2, 3 => 1, 5 => 7, 11 => -3, 17 => -2, 29 => 1, 35 => 1, 59 => 1],
  sparse![360; 1 => -2, 3 => 3, 5 => 2, 9 => 1, 11 => -1, 29 => 1],
  sparse![360; 1 => -1, 3 => 1, 5 => 1, 9 => 1, 11 => 1, 17 => 1, 35 => -1, 179 => 1],
  sparse![360; 1 => -1, 3 => 2, 11 => 1, 17 => 1, 35 => -1, 59 => 1, 179 => 1],
  sparse![360; 3 => -2, 7 => 1, 11 => 7, 23 => -3, 35 => -2, 59 => 1, 71 => 1, 119 => 1],
  sparse![360; 3 => -2, 7 => 3, 11 => 2, 19 => 1, 23 => -1, 59 => 1],
  sparse![360; 3 => -1, 7 => 1, 11 => 1, 19 => 1, 23 => 1, 35 => 1, 71 => -1, 359 => 1],
  sparse![360; 3 => -1, 7 => 2, 23 => 1, 35 => 1, 71 => -1, 119 => 1, 359 => 1],
  sparse![360; 0 => -5, 1 => 11, 2 => 1, 3 => -4, 4 => 5, 5 => -2, 9 => -4, 11 => 1, 14 => -1, 19 => 1, 29 => 1],
  sparse![360; 0 => -4, 1 => 10, 2 => 2, 3 => -4, 4 => 1, 5 => -4, 9 => -3, 11 => 2, 14 => -1, 19 => 2, 29 => 3],
  sparse![360; 2 => -5, 5 => 11, 8 => 1, 11 => -4, 14 => 5, 17 => -2, 29 => -4, 35 => 1, 44 => -1, 59 => 1, 89 => 1],
  sparse![360; 2 => -4, 5 => 10, 8 => 2, 11 => -4, 14 => 1, 17 => -4, 29 => -3, 35 => 2, 44 => -1, 59 => 2, 89 => 3],
  sparse![360; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 8 => 1, 11 => 1, 14 => 1, 17 => -2, 29 => -2, 35 => 1, 44 => -3, 59 => 1, 89 => 8, 179 => -3],
  sparse![360; 1 => -4, 3 => 10, 5 => 1, 7 => -4, 11 => -2, 17 => 1, 23 => 1, 29 => 1, 35 => -2, 59 => -2, 71 => 1, 89 => -3, 119 => 1, 179 => 8, 359 => -3],
  sparse![360; 1 => 1, 3 => 1, 5 => -1, 11 => 1, 29 => 2],
  sparse![360; 5 => 2, 9 => 1, 19 => 1, 29 => -1, 59 => 1],
  sparse![360; 1 => 1, 3 => 1, 5 => 1, 11 => -1, 59 => 2],
  sparse![360; 0 => 1, 1 => 1, 2 => 1, 3 => -1, 5 => -1, 11 => 1, 39 => 1, 119 => 1],
  sparse![360; 0 => 1, 1 => -1, 3 => 1, 14 => 1, 23 => 1, 89 => 1, 179 => -1, 359 => 1],
]
```

### Level 361

dim S₂ = **22**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **63**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 362

dim S₂ = **44**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **91**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 363

dim S₂ = **33**; eta rank = **10**; full eta basis = **NO**; Sturm bound B = **88**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![363; 0 => 2, 10 => 2],
  sparse![363; 2 => 2, 32 => 2],
  sparse![363; 10 => 2, 120 => 2],
  sparse![363; 32 => 2, 362 => 2],
  sparse![363; 0 => 1, 2 => 1, 10 => 1, 32 => 1],
  sparse![363; 10 => 1, 32 => 1, 120 => 1, 362 => 1],
  sparse![363; 0 => 1, 10 => 2, 120 => 1],
  sparse![363; 2 => 1, 32 => 2, 362 => 1],
  sparse![363; 0 => 1, 10 => 1, 32 => 1, 362 => 1],
  sparse![363; 2 => 1, 10 => 1, 32 => 1, 120 => 1],
]
```

### Level 364

dim S₂ = **51**; eta rank = **40**; full eta basis = **NO**; Sturm bound B = **112**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![364; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![364; 1 => 1, 3 => 1, 13 => 1, 27 => 1],
  sparse![364; 12 => 1, 25 => 1, 90 => 1, 181 => 1],
  sparse![364; 25 => 1, 51 => 1, 181 => 1, 363 => 1],
  sparse![364; 0 => -1, 1 => 3, 90 => 3, 181 => -1],
  sparse![364; 0 => 3, 1 => -1, 90 => -1, 181 => 3],
  sparse![364; 1 => 1, 6 => 1, 12 => -1, 25 => 2, 90 => 2, 181 => -1],
  sparse![364; 0 => -1, 1 => 2, 6 => 2, 13 => -1, 25 => 1, 90 => 1],
  sparse![364; 0 => 2, 1 => -1, 6 => 2, 12 => -1, 13 => -1, 25 => 2, 90 => -1, 181 => 2],
  sparse![364; 0 => 2, 1 => -1, 12 => -1, 13 => 1, 25 => 2, 90 => 1],
  sparse![364; 0 => 1, 6 => 1, 25 => 1, 181 => 1],
  sparse![364; 1 => 1, 6 => 2, 12 => 1, 13 => -1, 90 => -1, 181 => 2],
  sparse![364; 0 => 1, 6 => -1, 13 => 2, 25 => 1, 90 => 2, 181 => -1],
  sparse![364; 1 => 1, 12 => 1, 13 => 1, 90 => 1],
  sparse![364; 0 => -1, 1 => 2, 6 => 1, 12 => 2, 25 => -1, 181 => 1],
  sparse![364; 0 => -1, 1 => 2, 6 => -1, 12 => 2, 13 => 2, 25 => -1, 90 => 2, 181 => -1],
  sparse![364; 0 => 2, 1 => -1, 6 => -1, 12 => 1, 13 => 2, 181 => 1],
  sparse![364; 0 => 1, 12 => 2, 13 => 1, 25 => -1, 90 => -1, 181 => 2],
  sparse![364; 1 => -1, 3 => 3, 181 => 3, 363 => -1],
  sparse![364; 1 => 3, 3 => -1, 181 => -1, 363 => 3],
  sparse![364; 3 => 1, 13 => 1, 25 => -1, 51 => 2, 181 => 2, 363 => -1],
  sparse![364; 1 => -1, 3 => 2, 13 => 2, 27 => -1, 51 => 1, 181 => 1],
  sparse![364; 1 => 2, 3 => -1, 13 => 2, 25 => -1, 27 => -1, 51 => 2, 181 => -1, 363 => 2],
  sparse![364; 1 => 2, 3 => -1, 25 => -1, 27 => 1, 51 => 2, 181 => 1],
  sparse![364; 1 => 1, 13 => 1, 51 => 1, 363 => 1],
  sparse![364; 3 => 1, 13 => 2, 25 => 1, 27 => -1, 181 => -1, 363 => 2],
  sparse![364; 1 => 1, 13 => -1, 27 => 2, 51 => 1, 181 => 2, 363 => -1],
  sparse![364; 3 => 1, 25 => 1, 27 => 1, 181 => 1],
  sparse![364; 1 => -1, 3 => 2, 13 => 1, 25 => 2, 51 => -1, 363 => 1],
  sparse![364; 1 => -1, 3 => 2, 13 => -1, 25 => 2, 27 => 2, 51 => -1, 181 => 2, 363 => -1],
  sparse![364; 1 => 2, 3 => -1, 13 => -1, 25 => 1, 27 => 2, 363 => 1],
  sparse![364; 1 => 1, 25 => 2, 27 => 1, 51 => -1, 181 => -1, 363 => 2],
  sparse![364; 0 => 1, 3 => 1, 90 => -3, 181 => 8, 363 => -3],
  sparse![364; 0 => -3, 1 => 8, 3 => -3, 90 => 1, 363 => 1],
  sparse![364; 0 => -2, 1 => 5, 3 => -2, 6 => 1, 12 => -1, 13 => -1, 25 => 3, 27 => 1, 51 => -1, 181 => 1],
  sparse![364; 0 => -1, 1 => 3, 3 => -1, 12 => -2, 13 => 1, 25 => 5, 51 => -2, 90 => 1, 181 => -1, 363 => 1],
  sparse![364; 0 => -1, 1 => 3, 3 => -1, 6 => 1, 13 => -1, 25 => 1, 27 => 1, 90 => -2, 181 => 5, 363 => -2],
  sparse![364; 0 => 1, 1 => -1, 3 => 1, 6 => 1, 12 => -1, 13 => -1, 25 => 2, 27 => 1, 90 => -1, 181 => 2],
  sparse![364; 0 => -1, 1 => 2, 6 => -1, 12 => 1, 13 => 2, 25 => -1, 51 => 1, 90 => 1, 181 => -1, 363 => 1],
  sparse![364; 0 => 1, 1 => -1, 3 => 1, 6 => -1, 12 => -2, 13 => 3, 25 => 5, 27 => -1, 51 => -2, 181 => 1],
]
```

### Level 365

dim S₂ = **35**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **74**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 366

dim S₂ = **59**; eta rank = **16**; full eta basis = **NO**; Sturm bound B = **124**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![366; 0 => 1, 2 => 2, 5 => -1, 121 => 1, 182 => -1, 365 => 2],
  sparse![366; 0 => 2, 1 => -1, 2 => 1, 60 => -1, 121 => 2, 365 => 1],
  sparse![366; 1 => 2, 2 => 1, 5 => -1, 60 => 1, 121 => -1, 365 => 2],
  sparse![366; 0 => 1, 1 => 1, 182 => 1, 365 => 1],
  sparse![366; 0 => 2, 2 => -1, 5 => 1, 60 => -1, 121 => 1, 182 => 2],
  sparse![366; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 60 => 3, 121 => -2, 182 => -2, 365 => 3],
  sparse![366; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 60 => 2, 121 => -1, 182 => -1, 365 => 2],
  sparse![366; 1 => 1, 2 => 1, 60 => 1, 365 => 1],
  sparse![366; 0 => 1, 5 => 1, 121 => 1, 182 => 1],
  sparse![366; 0 => 2, 1 => -1, 2 => -1, 5 => 2, 60 => -1, 121 => 2, 182 => 2, 365 => -1],
  sparse![366; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 60 => -2, 121 => 3, 182 => 3, 365 => -2],
  sparse![366; 0 => -1, 1 => 1, 2 => 2, 60 => 2, 182 => -1, 365 => 1],
  sparse![366; 2 => 1, 5 => 1, 60 => 1, 121 => 1],
  sparse![366; 0 => 1, 1 => -1, 5 => 2, 121 => 2, 182 => 1, 365 => -1],
  sparse![366; 0 => -1, 1 => 2, 5 => 1, 60 => 2, 121 => -1, 182 => 1],
  sparse![366; 1 => 1, 2 => -1, 5 => 2, 60 => 1, 182 => 2, 365 => -1],
]
```

### Level 367

dim S₂ = **30**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **61**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 368

dim S₂ = **43**; eta rank = **36**; full eta basis = **NO**; Sturm bound B = **96**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![368; 0 => 2, 22 => 2],
  sparse![368; 1 => 2, 45 => 2],
  sparse![368; 3 => 2, 91 => 2],
  sparse![368; 7 => 2, 183 => 2],
  sparse![368; 15 => 2, 367 => 2],
  sparse![368; 0 => -1, 1 => 3, 22 => -1, 45 => 3],
  sparse![368; 0 => 1, 1 => 1, 22 => 1, 45 => 1],
  sparse![368; 0 => 3, 1 => -1, 22 => 3, 45 => -1],
  sparse![368; 1 => -1, 3 => 3, 45 => -1, 91 => 3],
  sparse![368; 1 => 1, 3 => 1, 45 => 1, 91 => 1],
  sparse![368; 3 => -1, 7 => 3, 91 => -1, 183 => 3],
  sparse![368; 3 => 1, 7 => 1, 91 => 1, 183 => 1],
  sparse![368; 7 => -1, 15 => 3, 183 => -1, 367 => 3],
  sparse![368; 7 => 1, 15 => 1, 183 => 1, 367 => 1],
  sparse![368; 0 => 1, 1 => -1, 3 => 2, 22 => 1, 45 => -1, 91 => 2],
  sparse![368; 1 => 1, 3 => -1, 7 => 2, 45 => 1, 91 => -1, 183 => 2],
  sparse![368; 3 => 1, 7 => -1, 15 => 2, 91 => 1, 183 => -1, 367 => 2],
  sparse![368; 0 => 1, 1 => -2, 3 => 5, 7 => -2, 22 => 1, 45 => -2, 91 => 5, 183 => -2],
  sparse![368; 0 => 2, 1 => -2, 3 => 3, 7 => -1, 22 => 2, 45 => -2, 91 => 3, 183 => -1],
  sparse![368; 0 => 1, 1 => -2, 3 => 4, 7 => -1, 22 => 1, 45 => -2, 91 => 4, 183 => -1],
  sparse![368; 1 => 1, 3 => -2, 7 => 5, 15 => -2, 45 => 1, 91 => -2, 183 => 5, 367 => -2],
  sparse![368; 1 => 2, 3 => -2, 7 => 3, 15 => -1, 45 => 2, 91 => -2, 183 => 3, 367 => -1],
  sparse![368; 1 => 1, 3 => -2, 7 => 4, 15 => -1, 45 => 1, 91 => -2, 183 => 4, 367 => -1],
  sparse![368; 3 => -3, 7 => 8, 15 => -3, 22 => -2, 45 => 5, 91 => -3, 183 => 3, 367 => -1],
  sparse![368; 0 => 1, 1 => -1, 3 => -1, 7 => 5, 15 => -2, 22 => -1, 45 => 4, 91 => -1],
  sparse![368; 0 => 1, 3 => -2, 7 => 5, 15 => -2, 22 => -1, 45 => 5, 91 => -2],
  sparse![368; 1 => -1, 3 => 1, 7 => 4, 15 => -2, 22 => -2, 45 => 4, 91 => 1, 183 => -1],
  sparse![368; 0 => 1, 3 => -2, 7 => 5, 15 => -2, 22 => 3, 45 => -1],
  sparse![368; 7 => 1, 15 => 1, 22 => -2, 45 => 5, 91 => -2, 183 => 2, 367 => -1],
  sparse![368; 3 => -1, 7 => 2, 15 => 1, 22 => -2, 45 => 5, 91 => -3, 183 => 3, 367 => -1],
  sparse![368; 0 => 1, 1 => -2, 3 => 3, 7 => 1, 15 => -1, 22 => 1, 45 => -2, 91 => 3, 183 => 1, 367 => -1],
  sparse![368; 0 => 1, 7 => 2, 15 => -1, 22 => 1, 183 => 2, 367 => -1],
  sparse![368; 3 => -1, 7 => 5, 15 => -2, 22 => -2, 45 => 5, 91 => -1],
  sparse![368; 1 => 1, 3 => -2, 7 => 5, 15 => -2, 22 => -2, 45 => 6, 91 => -2],
  sparse![368; 3 => -1, 7 => 4, 15 => -1, 22 => -2, 45 => 5, 91 => -1, 183 => -1, 367 => 1],
  sparse![368; 0 => -1, 1 => 2, 3 => -2, 7 => 5, 15 => -2, 22 => 1, 45 => 1],
]
```

### Level 369

dim S₂ = **39**; eta rank = **2**; full eta basis = **NO**; Sturm bound B = **84**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![369; 0 => 1, 2 => 1, 40 => 1, 122 => 1],
  sparse![369; 2 => 1, 8 => 1, 122 => 1, 368 => 1],
]
```

### Level 370

dim S₂ = **53**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **114**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 371

dim S₂ = **35**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **72**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![371; 0 => 2, 370 => 2],
  sparse![371; 0 => 1, 6 => 1, 52 => 1, 370 => 1],
  sparse![371; 6 => 2, 52 => 2],
]
```

### Level 372

dim S₂ = **59**; eta rank = **58**; full eta basis = **NO**; Sturm bound B = **128**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![372; 0 => 1, 1 => 1, 30 => 1, 61 => 1],
  sparse![372; 1 => 1, 3 => 1, 61 => 1, 123 => 1],
  sparse![372; 2 => 1, 5 => 1, 92 => 1, 185 => 1],
  sparse![372; 5 => 1, 11 => 1, 185 => 1, 371 => 1],
  sparse![372; 0 => -1, 1 => 4, 3 => -1, 30 => -1, 61 => 4, 123 => -1],
  sparse![372; 2 => -1, 5 => 4, 11 => -1, 92 => -1, 185 => 4, 371 => -1],
  sparse![372; 0 => 1, 1 => -1, 2 => -2, 5 => 4, 30 => -1, 61 => 1, 92 => 4, 185 => -2],
  sparse![372; 0 => -1, 1 => 1, 2 => 4, 5 => -2, 30 => 1, 61 => -1, 92 => -2, 185 => 4],
  sparse![372; 0 => 2, 1 => -1, 5 => 1, 30 => -1, 61 => 2, 92 => 1],
  sparse![372; 0 => 1, 2 => -1, 5 => 2, 61 => 1, 92 => 2, 185 => -1],
  sparse![372; 0 => 2, 1 => -1, 2 => -1, 5 => 2, 30 => 2, 61 => -1, 92 => -1, 185 => 2],
  sparse![372; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 30 => -1, 61 => 2, 92 => 2, 185 => -1],
  sparse![372; 1 => 1, 2 => 2, 5 => -1, 30 => 1, 92 => -1, 185 => 2],
  sparse![372; 0 => -1, 1 => 2, 2 => 1, 30 => 2, 61 => -1, 185 => 1],
  sparse![372; 0 => 4, 1 => -2, 2 => -1, 5 => 1, 30 => -2, 61 => 4, 92 => 1, 185 => -1],
  sparse![372; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 30 => 4, 61 => -2, 92 => -1, 185 => 1],
  sparse![372; 1 => 1, 3 => -1, 5 => -2, 11 => 4, 61 => -1, 123 => 1, 185 => 4, 371 => -2],
  sparse![372; 1 => -1, 3 => 1, 5 => 4, 11 => -2, 61 => 1, 123 => -1, 185 => -2, 371 => 4],
  sparse![372; 1 => 2, 3 => -1, 11 => 1, 61 => -1, 123 => 2, 185 => 1],
  sparse![372; 1 => 1, 5 => -1, 11 => 2, 123 => 1, 185 => 2, 371 => -1],
  sparse![372; 1 => 2, 3 => -1, 5 => -1, 11 => 2, 61 => 2, 123 => -1, 185 => -1, 371 => 2],
  sparse![372; 1 => -1, 3 => 2, 5 => 2, 11 => -1, 61 => -1, 123 => 2, 185 => 2, 371 => -1],
  sparse![372; 3 => 1, 5 => 2, 11 => -1, 61 => 1, 185 => -1, 371 => 2],
  sparse![372; 1 => -1, 3 => 2, 5 => 1, 61 => 2, 123 => -1, 371 => 1],
  sparse![372; 1 => 4, 3 => -2, 5 => -1, 11 => 1, 61 => -2, 123 => 4, 185 => 1, 371 => -1],
  sparse![372; 1 => -2, 3 => 4, 5 => 1, 11 => -1, 61 => 4, 123 => -2, 185 => -1, 371 => 1],
  sparse![372; 1 => 2, 2 => 1, 3 => -1, 5 => -1, 11 => 1, 61 => 2, 92 => 1, 123 => -1, 185 => -1, 371 => 1],
  sparse![372; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 11 => 1, 30 => -1, 61 => 2, 92 => 1, 185 => -1, 371 => 1],
  sparse![372; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 11 => 1, 30 => 2, 61 => -2, 92 => -1, 123 => 2, 185 => 2, 371 => -1],
  sparse![372; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -2, 11 => 1, 61 => 4, 123 => -2, 185 => -1, 371 => 1],
  sparse![372; 0 => -3, 1 => 7, 2 => 2, 3 => -2, 5 => -3, 11 => 1, 30 => 1, 61 => -3, 92 => -2, 123 => 2, 185 => 7, 371 => -3],
  sparse![372; 0 => -3, 1 => 8, 3 => -3, 30 => -1, 61 => 2, 92 => 2, 123 => -1, 185 => -2, 371 => 2],
  sparse![372; 0 => -3, 1 => 8, 2 => 1, 3 => -3, 5 => -3, 11 => 2, 61 => -1, 123 => 1, 185 => 4, 371 => -2],
  sparse![372; 0 => -3, 1 => 8, 2 => 2, 3 => -3, 5 => -3, 11 => 1, 30 => 1, 61 => -1, 92 => -2, 185 => 4],
  sparse![372; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -2, 11 => 1, 30 => 2, 61 => 1, 92 => -1, 123 => -1, 371 => 1],
  sparse![372; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -1, 30 => 2, 61 => -2, 92 => -1, 123 => 2, 185 => 2, 371 => -1],
  sparse![372; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 30 => -2, 61 => 7, 92 => 1, 123 => -3, 185 => -2, 371 => 1],
  sparse![372; 0 => -2, 1 => 4, 2 => 2, 3 => -1, 5 => -1, 30 => -1, 61 => 3, 92 => -1, 123 => -1, 185 => 2],
  sparse![372; 0 => -2, 1 => 5, 3 => -2, 5 => 1, 30 => 1, 61 => -1, 92 => -1, 123 => 1, 185 => 3, 371 => -1],
  sparse![372; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 5 => -2, 11 => 2, 30 => 1, 61 => -1, 123 => 1, 371 => 1],
  sparse![372; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 5 => -1, 11 => 1, 30 => -2, 61 => 5, 92 => 1, 123 => -2, 185 => -1, 371 => 1],
  sparse![372; 0 => -2, 1 => 5, 2 => 2, 3 => -2, 5 => -2, 11 => 1, 30 => 1, 61 => -1, 92 => 1, 123 => 1],
  sparse![372; 0 => -2, 1 => 6, 3 => -2, 30 => 1, 61 => -2, 92 => -1, 123 => 1, 185 => 4, 371 => -1],
  sparse![372; 0 => -2, 1 => 7, 2 => 1, 3 => -3, 5 => -3, 11 => 2, 30 => 2, 61 => -3, 92 => -3, 123 => 1, 185 => 7, 371 => -2],
  sparse![372; 0 => -2, 1 => 7, 2 => 1, 3 => -3, 5 => -2, 11 => 1, 30 => -2, 61 => 4, 92 => 1, 185 => -1],
  sparse![372; 0 => -1, 2 => 2, 3 => 1, 5 => 1, 11 => -1, 30 => 3, 61 => -2, 92 => -2, 123 => 1, 185 => 3, 371 => -1],
  sparse![372; 0 => -1, 1 => 1, 2 => 1, 5 => 1, 30 => 2],
  sparse![372; 0 => -1, 1 => 1, 2 => 1, 3 => 2, 11 => -1, 30 => -1, 61 => 3, 92 => 1, 123 => -2, 185 => -2, 371 => 3],
  sparse![372; 0 => -1, 1 => 1, 2 => 2, 5 => 1, 11 => -1, 30 => -1, 61 => 2, 92 => 2, 123 => -1, 185 => -2, 371 => 2],
  sparse![372; 0 => -1, 1 => 1, 2 => 2, 3 => 1, 5 => -1, 92 => -1, 123 => 1, 185 => 2],
  sparse![372; 0 => -1, 1 => 3, 2 => 1, 3 => -2, 5 => -2, 11 => 3, 30 => -1, 61 => 1, 92 => 1, 123 => 2, 371 => -1],
  sparse![372; 0 => -1, 1 => 4, 2 => 1, 3 => -1, 5 => -2, 11 => 1, 92 => -2, 185 => 6, 371 => -2],
  sparse![372; 2 => -2, 5 => 6, 11 => -2, 30 => -1, 61 => 4, 92 => 1, 123 => -1, 185 => -2, 371 => 1],
  sparse![372; 11 => 2, 61 => 1, 123 => 1, 185 => 1, 371 => -1],
  sparse![372; 3 => 2, 61 => 1, 123 => -1, 185 => 1, 371 => 1],
  sparse![372; 0 => 1, 1 => -3, 2 => -2, 3 => 2, 5 => 7, 11 => -3, 30 => -3, 61 => 7, 92 => 2, 123 => -2, 185 => -3, 371 => 1],
  sparse![372; 0 => 1, 1 => 1, 2 => -1, 5 => 1, 92 => 2],
  sparse![372; 0 => 2, 30 => -1, 61 => 1, 92 => 1, 185 => 1],
]
```

### Level 373

dim S₂ = **30**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **62**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 374

dim S₂ = **51**; eta rank = **18**; full eta basis = **NO**; Sturm bound B = **108**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![374; 0 => 2, 10 => 2],
  sparse![374; 1 => 2, 21 => 2],
  sparse![374; 16 => 2, 186 => 2],
  sparse![374; 33 => 2, 373 => 2],
  sparse![374; 0 => 1, 10 => 1, 16 => 1, 186 => 1],
  sparse![374; 1 => 1, 21 => 1, 33 => 1, 373 => 1],
  sparse![374; 10 => 3, 16 => -1, 21 => -1, 33 => 3],
  sparse![374; 10 => -1, 16 => 3, 21 => 3, 33 => -1],
  sparse![374; 0 => -1, 1 => 2, 10 => 1, 33 => 1, 186 => 2, 373 => -1],
  sparse![374; 1 => 1, 10 => 2, 16 => -1, 21 => -1, 33 => 2, 186 => 1],
  sparse![374; 0 => -1, 1 => 2, 10 => -1, 16 => 1, 21 => 2, 186 => 1],
  sparse![374; 0 => 1, 10 => 1, 16 => -1, 33 => 2, 186 => -1, 373 => 2],
  sparse![374; 1 => 1, 16 => 2, 21 => 1, 33 => -1, 186 => 2, 373 => -1],
  sparse![374; 0 => 2, 1 => -1, 10 => 2, 21 => -1, 33 => 1, 373 => 1],
  sparse![374; 0 => 1, 10 => -1, 16 => 2, 21 => 2, 33 => -1, 373 => 1],
  sparse![374; 0 => 2, 1 => -1, 16 => 1, 21 => 1, 186 => -1, 373 => 2],
  sparse![374; 0 => -1, 1 => 3, 186 => 3, 373 => -1],
  sparse![374; 0 => 3, 1 => -1, 186 => -1, 373 => 3],
]
```

### Level 375

dim S₂ = **41**; eta rank = **16**; full eta basis = **NO**; Sturm bound B = **100**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![375; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![375; 4 => 1, 14 => 1, 24 => 1, 74 => 1],
  sparse![375; 24 => 1, 74 => 1, 124 => 1, 374 => 1],
  sparse![375; 0 => 1, 4 => 1, 14 => 1, 74 => 1],
  sparse![375; 2 => 1, 4 => 1, 14 => 1, 24 => 1],
  sparse![375; 4 => 1, 24 => 1, 74 => 1, 374 => 1],
  sparse![375; 14 => 1, 24 => 1, 74 => 1, 124 => 1],
  sparse![375; 0 => 1, 74 => 1, 124 => 1, 374 => 1],
  sparse![375; 2 => 1, 24 => 1, 124 => 1, 374 => 1],
  sparse![375; 0 => 1, 2 => 1, 124 => 1, 374 => 1],
  sparse![375; 0 => 1, 4 => 1, 74 => 1, 374 => 1],
  sparse![375; 2 => 1, 4 => 1, 24 => 1, 374 => 1],
  sparse![375; 0 => 1, 14 => 1, 74 => 1, 124 => 1],
  sparse![375; 2 => 1, 14 => 1, 24 => 1, 124 => 1],
  sparse![375; 0 => 1, 2 => 1, 4 => 1, 374 => 1],
  sparse![375; 0 => 1, 2 => 1, 14 => 1, 124 => 1],
]
```

### Level 376

dim S₂ = **45**; eta rank = **28**; full eta basis = **NO**; Sturm bound B = **96**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![376; 0 => 2, 46 => 2],
  sparse![376; 1 => 2, 93 => 2],
  sparse![376; 3 => 2, 187 => 2],
  sparse![376; 7 => 2, 375 => 2],
  sparse![376; 0 => -1, 1 => 3, 46 => -1, 93 => 3],
  sparse![376; 0 => 1, 1 => 1, 46 => 1, 93 => 1],
  sparse![376; 0 => 3, 1 => -1, 46 => 3, 93 => -1],
  sparse![376; 1 => -1, 3 => 3, 93 => -1, 187 => 3],
  sparse![376; 1 => 1, 3 => 1, 93 => 1, 187 => 1],
  sparse![376; 1 => 3, 3 => -1, 93 => 3, 187 => -1],
  sparse![376; 3 => -1, 7 => 3, 187 => -1, 375 => 3],
  sparse![376; 3 => 1, 7 => 1, 187 => 1, 375 => 1],
  sparse![376; 3 => 3, 7 => -1, 187 => 3, 375 => -1],
  sparse![376; 0 => 1, 1 => -1, 3 => 2, 46 => 1, 93 => -1, 187 => 2],
  sparse![376; 0 => -1, 1 => 2, 3 => 1, 46 => -1, 93 => 2, 187 => 1],
  sparse![376; 0 => 1, 3 => 1, 46 => 1, 187 => 1],
  sparse![376; 0 => 2, 1 => -1, 3 => 1, 46 => 2, 93 => -1, 187 => 1],
  sparse![376; 0 => -1, 1 => 4, 3 => -1, 46 => -1, 93 => 4, 187 => -1],
  sparse![376; 0 => 1, 1 => 2, 3 => -1, 46 => 1, 93 => 2, 187 => -1],
  sparse![376; 1 => 1, 3 => -1, 7 => 2, 93 => 1, 187 => -1, 375 => 2],
  sparse![376; 1 => -1, 3 => 2, 7 => 1, 93 => -1, 187 => 2, 375 => 1],
  sparse![376; 1 => 2, 3 => -1, 7 => 1, 93 => 2, 187 => -1, 375 => 1],
  sparse![376; 0 => 1, 1 => -2, 3 => 5, 7 => -2, 46 => 1, 93 => -2, 187 => 5, 375 => -2],
  sparse![376; 0 => -1, 1 => 1, 3 => 4, 7 => -2, 46 => -1, 93 => 1, 187 => 4, 375 => -2],
  sparse![376; 0 => 2, 1 => -2, 3 => 3, 7 => -1, 46 => 2, 93 => -2, 187 => 3, 375 => -1],
  sparse![376; 0 => 1, 1 => -2, 3 => 4, 7 => -1, 46 => 1, 93 => -2, 187 => 4, 375 => -1],
  sparse![376; 0 => 1, 1 => -1, 3 => 3, 7 => -1, 46 => 1, 93 => -1, 187 => 3, 375 => -1],
  sparse![376; 0 => 2, 1 => -1, 7 => 1, 46 => 2, 93 => -1, 375 => 1],
]
```

### Level 377

dim S₂ = **33**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **70**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 378

dim S₂ = **61**; eta rank = **61**; full eta basis = **YES**; Sturm bound B = **144**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![378; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![378; 2 => 1, 5 => 1, 20 => 1, 41 => 1],
  sparse![378; 8 => 1, 17 => 1, 62 => 1, 125 => 1],
  sparse![378; 26 => 1, 53 => 1, 188 => 1, 377 => 1],
  sparse![378; 2 => 2, 8 => 2],
  sparse![378; 5 => 2, 17 => 2],
  sparse![378; 20 => 2, 62 => 2],
  sparse![378; 41 => 2, 125 => 2],
  sparse![378; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 6 => 4, 13 => -2, 20 => -1, 41 => 1],
  sparse![378; 0 => -1, 1 => 1, 2 => 4, 5 => -2, 6 => 1, 13 => -1, 20 => -2, 41 => 4],
  sparse![378; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 6 => -1, 13 => 2, 20 => 2, 41 => -1],
  sparse![378; 2 => -2, 5 => 4, 8 => 1, 17 => -1, 20 => 4, 41 => -2, 62 => -1, 125 => 1],
  sparse![378; 2 => -1, 5 => 1, 8 => 4, 17 => -2, 20 => 1, 41 => -1, 62 => -2, 125 => 4],
  sparse![378; 2 => -1, 5 => 2, 8 => 2, 17 => -1, 20 => -1, 41 => 2, 62 => 2, 125 => -1],
  sparse![378; 8 => -2, 17 => 4, 26 => 1, 53 => -1, 62 => 4, 125 => -2, 188 => -1, 377 => 1],
  sparse![378; 8 => -1, 17 => 1, 26 => 4, 53 => -2, 62 => 1, 125 => -1, 188 => -2, 377 => 4],
  sparse![378; 8 => -1, 17 => 2, 26 => 2, 53 => -1, 62 => -1, 125 => 2, 188 => 2, 377 => -1],
  sparse![378; 0 => -1, 1 => 2, 5 => 2, 8 => 1],
  sparse![378; 0 => -1, 1 => 2, 2 => 1, 17 => 1, 26 => 2, 53 => -1],
  sparse![378; 6 => -1, 13 => 2, 41 => 2, 62 => 1],
  sparse![378; 6 => -1, 13 => 2, 20 => 1, 125 => 1, 188 => 2, 377 => -1],
  sparse![378; 2 => 2, 20 => 2],
  sparse![378; 0 => -1, 2 => 4, 6 => 1, 8 => -1, 62 => 1],
  sparse![378; 5 => 2, 41 => 2],
  sparse![378; 1 => -1, 5 => 4, 13 => 1, 17 => -1, 125 => 1],
  sparse![378; 8 => 2, 62 => 2],
  sparse![378; 2 => -1, 8 => 4, 20 => 1, 26 => -1, 188 => 1],
  sparse![378; 17 => 2, 125 => 2],
  sparse![378; 5 => -1, 17 => 4, 41 => 1, 53 => -1, 377 => 1],
  sparse![378; 2 => -1, 5 => 1, 8 => 4, 17 => -2, 20 => -1, 41 => 1, 62 => 4, 125 => -2],
  sparse![378; 0 => 1, 1 => 1, 62 => 1, 125 => 1],
  sparse![378; 0 => 1, 13 => 1, 17 => 1, 62 => 1],
  sparse![378; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 8 => -1, 13 => 1, 17 => 1, 20 => -1, 41 => 2, 62 => 1, 125 => -1],
  sparse![378; 8 => -1, 17 => 1, 26 => 4, 53 => -2, 62 => -1, 125 => 1, 188 => 4, 377 => -2],
  sparse![378; 2 => 1, 5 => 1, 188 => 1, 377 => 1],
  sparse![378; 2 => 1, 41 => 1, 53 => 1, 188 => 1],
  sparse![378; 2 => -2, 5 => 3, 8 => 3, 17 => -2, 26 => -1, 41 => 1, 53 => 1, 62 => -1, 125 => 2, 188 => 1, 377 => -1],
  sparse![378; 0 => 1, 6 => 2, 8 => 1],
  sparse![378; 0 => 2, 6 => 1, 62 => 1],
  sparse![378; 2 => 1, 8 => 1, 20 => 1, 62 => 1],
  sparse![378; 0 => -1, 2 => 3, 6 => 1, 20 => -1, 62 => 2],
  sparse![378; 2 => -1, 8 => 3, 20 => 3, 62 => -1],
  sparse![378; 2 => 1, 26 => 1, 188 => 2],
  sparse![378; 20 => 1, 26 => 2, 188 => 1],
  sparse![378; 1 => 1, 13 => 2, 17 => 1],
  sparse![378; 1 => 2, 13 => 1, 125 => 1],
  sparse![378; 5 => 1, 17 => 1, 41 => 1, 125 => 1],
  sparse![378; 1 => -1, 5 => 3, 13 => 1, 41 => -1, 125 => 2],
  sparse![378; 5 => -1, 17 => 3, 41 => 3, 125 => -1],
  sparse![378; 5 => 1, 53 => 1, 377 => 2],
  sparse![378; 41 => 1, 53 => 2, 377 => 1],
  sparse![378; 5 => -1, 17 => 3, 26 => 1, 41 => 2, 53 => -1, 125 => -1, 188 => 1],
  sparse![378; 2 => -1, 8 => 3, 20 => 2, 26 => -1, 53 => 1, 62 => -1, 377 => 1],
  sparse![378; 5 => 2, 17 => -1, 26 => 1, 41 => -1, 125 => 3, 188 => 1, 377 => -1],
  sparse![378; 2 => 2, 8 => -1, 20 => -1, 53 => 1, 62 => 3, 188 => -1, 377 => 1],
  sparse![378; 0 => 1, 1 => -1, 5 => 3, 6 => 1, 17 => -1, 41 => -1, 125 => 2],
  sparse![378; 0 => 1, 5 => -1, 6 => 1, 13 => -1, 17 => 2, 41 => 3, 125 => -1],
  sparse![378; 2 => 1, 17 => 1, 20 => 1, 125 => 1],
  sparse![378; 5 => 1, 8 => 1, 41 => 1, 62 => 1],
  sparse![378; 0 => 2, 1 => -1, 17 => 1, 62 => 2],
  sparse![378; 0 => 1, 1 => -1, 5 => 1, 6 => 1, 17 => 1, 41 => 1],
]
```

### Level 379

dim S₂ = **31**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **63**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 380

dim S₂ = **55**; eta rank = **49**; full eta basis = **NO**; Sturm bound B = **120**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![380; 1 => 2, 9 => 2],
  sparse![380; 37 => 2, 189 => 2],
  sparse![380; 0 => 3, 1 => -1, 18 => -1, 37 => 3],
  sparse![380; 0 => -1, 1 => 3, 18 => 3, 37 => -1],
  sparse![380; 1 => 3, 3 => -1, 37 => -1, 75 => 3],
  sparse![380; 1 => -1, 3 => 3, 37 => 3, 75 => -1],
  sparse![380; 4 => 3, 9 => -1, 94 => -1, 189 => 3],
  sparse![380; 4 => -1, 9 => 3, 94 => 3, 189 => -1],
  sparse![380; 9 => 3, 19 => -1, 189 => -1, 379 => 3],
  sparse![380; 9 => -1, 19 => 3, 189 => 3, 379 => -1],
  sparse![380; 0 => 1, 3 => 1, 18 => -3, 37 => 8, 75 => -3],
  sparse![380; 4 => 1, 19 => 1, 94 => -3, 189 => 8, 379 => -3],
  sparse![380; 0 => 2, 94 => 2],
  sparse![380; 0 => 1, 4 => 1, 18 => 1, 94 => 1],
  sparse![380; 4 => 2, 18 => 2],
  sparse![380; 1 => 2, 189 => 2],
  sparse![380; 1 => 1, 9 => 1, 37 => 1, 189 => 1],
  sparse![380; 9 => 2, 37 => 2],
  sparse![380; 3 => 2, 379 => 2],
  sparse![380; 3 => 1, 19 => 1, 75 => 1, 379 => 1],
  sparse![380; 19 => 2, 75 => 2],
  sparse![380; 0 => 3, 1 => -1, 18 => 4, 37 => -2, 94 => -1, 189 => 1],
  sparse![380; 0 => 4, 1 => -2, 4 => -1, 9 => 1, 18 => 3, 37 => -1],
  sparse![380; 0 => -2, 1 => 4, 4 => 1, 9 => -1, 18 => 4, 37 => -2, 94 => -1, 189 => 1],
  sparse![380; 0 => 4, 1 => -2, 4 => -1, 9 => 1, 18 => -2, 37 => 4, 94 => 1, 189 => -1],
  sparse![380; 0 => 1, 1 => 1, 94 => 1, 189 => 1],
  sparse![380; 0 => -1, 1 => 2, 4 => 2, 9 => -1, 18 => 2, 37 => -1, 94 => -1, 189 => 2],
  sparse![380; 1 => 1, 4 => 2, 9 => -1, 18 => 2, 37 => -1, 189 => 1],
  sparse![380; 0 => 1, 4 => 2, 9 => -1, 18 => 2, 37 => -1, 94 => 1],
  sparse![380; 0 => -1, 1 => 2, 4 => 1, 18 => 1, 94 => -1, 189 => 2],
  sparse![380; 1 => 1, 4 => 1, 18 => 1, 189 => 1],
  sparse![380; 0 => 1, 9 => 1, 37 => 1, 94 => 1],
  sparse![380; 4 => 1, 9 => 1, 18 => 1, 37 => 1],
  sparse![380; 1 => 3, 3 => -1, 37 => 4, 75 => -2, 189 => -1, 379 => 1],
  sparse![380; 1 => 4, 3 => -2, 9 => -1, 19 => 1, 37 => 3, 75 => -1],
  sparse![380; 1 => -2, 3 => 4, 9 => 1, 19 => -1, 37 => 4, 75 => -2, 189 => -1, 379 => 1],
  sparse![380; 1 => 4, 3 => -2, 9 => -1, 19 => 1, 37 => -2, 75 => 4, 189 => 1, 379 => -1],
  sparse![380; 1 => 1, 3 => 1, 189 => 1, 379 => 1],
  sparse![380; 1 => -1, 3 => 2, 9 => 2, 19 => -1, 37 => 2, 75 => -1, 189 => -1, 379 => 2],
  sparse![380; 3 => 1, 9 => 2, 19 => -1, 37 => 2, 75 => -1, 379 => 1],
  sparse![380; 3 => 1, 9 => 1, 37 => 1, 379 => 1],
  sparse![380; 0 => 1, 4 => 1, 18 => -2, 37 => 5, 75 => -2, 189 => -1, 379 => 2],
  sparse![380; 0 => 2, 1 => -1, 4 => 1, 18 => -2, 37 => 5, 75 => -2, 94 => 1, 189 => -2, 379 => 2],
  sparse![380; 0 => 1, 4 => 2, 9 => -1, 18 => -1, 37 => 4, 75 => -2, 189 => -1, 379 => 2],
  sparse![380; 0 => -1, 1 => 4, 3 => -2, 9 => -1, 18 => -2, 19 => 2, 37 => 5, 75 => -2, 94 => 1, 189 => -2, 379 => 2],
  sparse![380; 0 => 2, 1 => -1, 4 => -1, 9 => 1, 18 => -2, 19 => 1, 37 => 5, 75 => -2, 94 => -1, 189 => 3, 379 => -1],
  sparse![380; 0 => 3, 1 => -2, 3 => 1, 4 => -1, 9 => 1, 18 => -1, 37 => 1, 94 => 3, 189 => -2, 379 => 1],
  sparse![380; 0 => 1, 19 => 1, 75 => 1, 94 => 1],
  sparse![380; 0 => 2, 1 => -1, 9 => -1, 18 => -1, 19 => 2, 37 => 3, 75 => -1, 94 => -1, 189 => 3, 379 => -1],
]
```

### Level 381

dim S₂ = **41**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **85**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 382

dim S₂ = **47**; eta rank = **5**; full eta basis = **NO**; Sturm bound B = **96**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![382; 0 => 2, 190 => 2],
  sparse![382; 1 => 2, 381 => 2],
  sparse![382; 0 => -1, 1 => 3, 190 => -1, 381 => 3],
  sparse![382; 0 => 1, 1 => 1, 190 => 1, 381 => 1],
  sparse![382; 0 => 3, 1 => -1, 190 => 3, 381 => -1],
]
```

### Level 383

dim S₂ = **32**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **64**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![383; 0 => 2, 382 => 2],
]
```

### Level 384

dim S₂ = **49**; eta rank = **49**; full eta basis = **YES**; Sturm bound B = **128**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![384; 1 => 1, 3 => 1, 5 => 1, 11 => 1],
  sparse![384; 3 => 1, 7 => 1, 11 => 1, 23 => 1],
  sparse![384; 7 => 1, 15 => 1, 23 => 1, 47 => 1],
  sparse![384; 15 => 1, 31 => 1, 47 => 1, 95 => 1],
  sparse![384; 31 => 1, 63 => 1, 95 => 1, 191 => 1],
  sparse![384; 3 => 2, 7 => 2],
  sparse![384; 7 => 2, 15 => 2],
  sparse![384; 11 => 2, 23 => 2],
  sparse![384; 15 => 2, 31 => 2],
  sparse![384; 23 => 2, 47 => 2],
  sparse![384; 47 => 2, 95 => 2],
  sparse![384; 0 => -2, 1 => 4, 2 => 2, 5 => -2, 11 => 2],
  sparse![384; 1 => -2, 3 => 4, 5 => 2, 11 => -2, 23 => 2],
  sparse![384; 3 => -2, 7 => 4, 11 => 2, 23 => -2, 47 => 2],
  sparse![384; 7 => -2, 15 => 4, 23 => 2, 47 => -2, 95 => 2],
  sparse![384; 0 => -2, 1 => 5, 3 => -2, 7 => 3],
  sparse![384; 1 => -2, 3 => 5, 7 => -2, 15 => 3],
  sparse![384; 2 => -2, 5 => 5, 11 => -2, 23 => 3],
  sparse![384; 5 => -2, 11 => 5, 23 => -2, 47 => 3],
  sparse![384; 1 => 1, 5 => 1, 15 => 1, 47 => 1],
  sparse![384; 0 => -2, 1 => 2, 2 => 2, 3 => 3, 7 => -1, 11 => -1, 23 => 1],
  sparse![384; 3 => 1, 11 => 1, 31 => 1, 95 => 1],
  sparse![384; 1 => -2, 3 => 2, 5 => 2, 7 => 3, 15 => -1, 23 => -1, 47 => 1],
  sparse![384; 7 => 1, 23 => 1, 63 => 1, 191 => 1],
  sparse![384; 3 => -2, 7 => 2, 11 => 2, 15 => 3, 31 => -1, 47 => -1, 95 => 1],
  sparse![384; 1 => -2, 3 => 5, 7 => -1, 15 => 1, 31 => -1, 63 => 2],
  sparse![384; 1 => 2, 3 => 1, 15 => 1],
  sparse![384; 3 => 2, 31 => 2],
  sparse![384; 7 => 1, 31 => 1, 63 => 2],
  sparse![384; 5 => -2, 11 => 5, 23 => -1, 47 => 1, 95 => -1, 191 => 2],
  sparse![384; 5 => 2, 11 => 1, 47 => 1],
  sparse![384; 11 => 2, 95 => 2],
  sparse![384; 23 => 1, 95 => 1, 191 => 2],
  sparse![384; 0 => -4, 1 => 9, 2 => 2, 3 => -4, 5 => -2, 7 => 1, 11 => 2],
  sparse![384; 0 => -4, 1 => 11, 2 => 2, 3 => -3, 5 => -4, 11 => 1, 23 => 1],
  sparse![384; 0 => -3, 1 => 7, 2 => 1, 3 => -4, 5 => -1, 7 => 3, 11 => 2, 15 => -1, 23 => -1, 47 => 1],
  sparse![384; 0 => -3, 1 => 9, 2 => 1, 3 => -3, 5 => -3, 11 => 1, 23 => 1, 31 => 2, 63 => -1, 95 => -1, 191 => 1],
  sparse![384; 1 => -4, 3 => 9, 5 => 2, 7 => -4, 11 => -2, 15 => 1, 23 => 2],
  sparse![384; 1 => -4, 3 => 11, 5 => 2, 7 => -3, 11 => -4, 23 => 1, 47 => 1],
  sparse![384; 1 => -3, 3 => 7, 5 => 1, 7 => -4, 11 => -1, 15 => 3, 23 => 2, 31 => -1, 47 => -1, 95 => 1],
  sparse![384; 1 => -3, 3 => 9, 5 => 1, 7 => -3, 11 => -3, 23 => 1, 47 => 1, 63 => 2, 127 => -1, 191 => -1, 383 => 1],
  sparse![384; 1 => 1, 3 => 2, 5 => -1, 7 => 2, 11 => 1, 15 => -1, 23 => -1, 31 => -1, 63 => 1, 95 => 2, 191 => -1],
  sparse![384; 1 => -1, 3 => 1, 5 => 1, 7 => -1, 11 => 2, 23 => 2, 31 => 2, 47 => -1, 63 => -1, 95 => -1, 191 => 1],
  sparse![384; 1 => 1, 3 => -1, 5 => -1, 7 => -1, 11 => 2, 15 => 2, 31 => 2, 47 => -1, 63 => 1, 95 => 1, 191 => -1],
  sparse![384; 1 => -1, 3 => 2, 5 => 1, 11 => -1, 15 => -1, 23 => -1, 31 => 1, 47 => 2, 63 => -1, 95 => 2, 191 => 1],
  sparse![384; 0 => -1, 1 => 2, 2 => 1, 3 => -1, 5 => -1, 11 => 3, 23 => -1, 31 => 2],
  sparse![384; 2 => -2, 5 => 5, 7 => 1, 11 => -2, 15 => 1, 47 => -1, 95 => 2],
  sparse![384; 1 => 1, 5 => 1, 63 => 1, 191 => 1],
  sparse![384; 0 => 1, 1 => 1, 2 => 1, 3 => -1, 5 => 1, 15 => 1],
]
```

### Level 385

dim S₂ = **45**; eta rank = **18**; full eta basis = **NO**; Sturm bound B = **96**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![385; 0 => 2, 10 => 2],
  sparse![385; 4 => 2, 54 => 2],
  sparse![385; 6 => 2, 76 => 2],
  sparse![385; 34 => 2, 384 => 2],
  sparse![385; 0 => 2, 34 => 2],
  sparse![385; 0 => 1, 4 => 1, 6 => 1, 34 => 1],
  sparse![385; 4 => 2, 6 => 2],
  sparse![385; 10 => 2, 384 => 2],
  sparse![385; 10 => 1, 54 => 1, 76 => 1, 384 => 1],
  sparse![385; 54 => 2, 76 => 2],
  sparse![385; 0 => 1, 4 => 1, 10 => 1, 54 => 1],
  sparse![385; 6 => 1, 34 => 1, 76 => 1, 384 => 1],
  sparse![385; 0 => 1, 6 => 1, 10 => 1, 76 => 1],
  sparse![385; 4 => 1, 34 => 1, 54 => 1, 384 => 1],
  sparse![385; 0 => 1, 10 => 1, 34 => 1, 384 => 1],
  sparse![385; 4 => 1, 6 => 1, 10 => 1, 384 => 1],
  sparse![385; 0 => 1, 34 => 1, 54 => 1, 76 => 1],
  sparse![385; 4 => 1, 6 => 1, 54 => 1, 76 => 1],
]
```

### Level 386

dim S₂ = **47**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **97**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 387

dim S₂ = **41**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **88**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![387; 0 => 1, 8 => 1, 42 => -1, 128 => 4, 386 => -1],
  sparse![387; 2 => 2, 128 => 2],
  sparse![387; 0 => -1, 2 => 4, 8 => -1, 42 => 1, 386 => 1],
]
```

### Level 388

dim S₂ = **47**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **98**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 389

dim S₂ = **32**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **65**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 390

dim S₂ = **77**; eta rank = **77**; full eta basis = **YES**; Sturm bound B = **168**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![390; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![390; 1 => 1, 5 => 1, 9 => 1, 29 => 1],
  sparse![390; 12 => 1, 38 => 1, 64 => 1, 194 => 1],
  sparse![390; 25 => 1, 77 => 1, 129 => 1, 389 => 1],
  sparse![390; 0 => 1, 1 => 1, 14 => 1, 29 => 1],
  sparse![390; 12 => 1, 25 => 1, 194 => 1, 389 => 1],
  sparse![390; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 12 => 3, 25 => -2, 38 => -2, 77 => 3],
  sparse![390; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 12 => -2, 25 => 3, 38 => 3, 77 => -2],
  sparse![390; 0 => 1, 1 => 1, 38 => 1, 77 => 1],
  sparse![390; 0 => 1, 5 => 1, 25 => 1, 38 => 1],
  sparse![390; 1 => 1, 2 => 1, 12 => 1, 77 => 1],
  sparse![390; 2 => 1, 5 => 1, 12 => 1, 25 => 1],
  sparse![390; 0 => -1, 1 => 1, 2 => 2, 12 => 2, 38 => -1, 77 => 1],
  sparse![390; 0 => -1, 1 => 2, 5 => 1, 12 => 2, 25 => -1, 38 => 1],
  sparse![390; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 12 => 2, 25 => -1, 38 => -1, 77 => 2],
  sparse![390; 1 => 1, 2 => -1, 5 => 2, 12 => 1, 38 => 2, 77 => -1],
  sparse![390; 0 => 1, 1 => -1, 5 => 2, 25 => 2, 38 => 1, 77 => -1],
  sparse![390; 4 => -2, 9 => 3, 14 => 3, 29 => -2, 64 => 3, 129 => -2, 194 => -2, 389 => 3],
  sparse![390; 4 => 3, 9 => -2, 14 => -2, 29 => 3, 64 => -2, 129 => 3, 194 => 3, 389 => -2],
  sparse![390; 4 => 1, 9 => 1, 194 => 1, 389 => 1],
  sparse![390; 4 => 1, 29 => 1, 129 => 1, 194 => 1],
  sparse![390; 9 => 1, 14 => 1, 64 => 1, 389 => 1],
  sparse![390; 14 => 1, 29 => 1, 64 => 1, 129 => 1],
  sparse![390; 4 => -1, 9 => 1, 14 => 2, 64 => 2, 194 => -1, 389 => 1],
  sparse![390; 4 => -1, 9 => 2, 29 => 1, 64 => 2, 129 => -1, 194 => 1],
  sparse![390; 4 => -1, 9 => 2, 14 => 2, 29 => -1, 64 => 2, 129 => -1, 194 => -1, 389 => 2],
  sparse![390; 9 => 1, 14 => -1, 29 => 2, 64 => 1, 194 => 2, 389 => -1],
  sparse![390; 4 => 1, 9 => -1, 29 => 2, 129 => 2, 194 => 1, 389 => -1],
  sparse![390; 0 => 1, 2 => 1, 64 => 1, 194 => 1],
  sparse![390; 0 => -1, 2 => 2, 4 => 2, 12 => 2, 14 => -1, 38 => -1, 64 => -1, 194 => 2],
  sparse![390; 0 => 1, 4 => 1, 38 => 1, 194 => 1],
  sparse![390; 2 => 1, 4 => 1, 12 => 1, 194 => 1],
  sparse![390; 0 => 1, 14 => 1, 38 => 1, 64 => 1],
  sparse![390; 2 => 1, 12 => 1, 14 => 1, 64 => 1],
  sparse![390; 0 => 2, 2 => -1, 4 => -1, 12 => -1, 14 => 2, 38 => 2, 64 => 2, 194 => -1],
  sparse![390; 4 => 1, 12 => 1, 14 => 1, 38 => 1],
  sparse![390; 1 => 1, 5 => 1, 129 => 1, 389 => 1],
  sparse![390; 1 => -1, 5 => 2, 9 => 2, 25 => 2, 29 => -1, 77 => -1, 129 => -1, 389 => 2],
  sparse![390; 1 => 1, 9 => 1, 77 => 1, 389 => 1],
  sparse![390; 5 => 1, 9 => 1, 25 => 1, 389 => 1],
  sparse![390; 1 => 1, 29 => 1, 77 => 1, 129 => 1],
  sparse![390; 5 => 1, 25 => 1, 29 => 1, 129 => 1],
  sparse![390; 1 => 2, 5 => -1, 9 => -1, 25 => -1, 29 => 2, 77 => 2, 129 => 2, 389 => -1],
  sparse![390; 9 => 1, 25 => 1, 29 => 1, 77 => 1],
  sparse![390; 1 => 1, 4 => 1, 9 => -1, 12 => 2, 25 => -1, 29 => 1, 38 => -1, 77 => 1, 389 => 1],
  sparse![390; 4 => -1, 5 => 1, 9 => 2, 14 => 1, 25 => 1, 29 => -1, 64 => 1, 129 => -1, 194 => -1, 389 => 2],
  sparse![390; 2 => 2, 4 => 1, 5 => -1, 9 => -1, 12 => -1, 14 => -1, 25 => 2, 29 => 2, 64 => 1],
  sparse![390; 2 => 1, 4 => 2, 9 => -1, 12 => 1, 14 => -1, 29 => 1, 64 => -1, 129 => 1, 194 => 2, 389 => -1],
  sparse![390; 1 => 1, 2 => 1, 4 => 1, 5 => -1, 9 => -1, 12 => -1, 25 => 1, 29 => 1, 38 => 1, 64 => 1, 194 => -1, 389 => 1],
  sparse![390; 0 => 1, 1 => -1, 5 => 1, 9 => 1, 12 => 1, 14 => 1, 29 => -1, 38 => -1, 64 => -1, 77 => 1, 129 => 1, 194 => 1],
  sparse![390; 2 => 1, 4 => 2, 9 => -1, 12 => -1, 14 => -1, 25 => 2, 29 => 1, 38 => 1, 77 => -1, 389 => 1],
  sparse![390; 4 => -1, 5 => 1, 9 => 2, 12 => 2, 14 => 1, 25 => -1, 29 => -1, 38 => -1, 77 => 1, 194 => 1],
  sparse![390; 4 => 2, 5 => 1, 9 => -1, 38 => 1, 64 => -1, 129 => 2],
  sparse![390; 0 => 1, 4 => 1, 9 => -1, 14 => -1, 29 => 2, 38 => -1, 77 => 2, 129 => 1],
  sparse![390; 1 => 1, 4 => -1, 9 => 1, 14 => 2, 29 => -1, 38 => 2, 64 => 1, 77 => -1],
  sparse![390; 2 => 1, 4 => -1, 9 => 2, 12 => -1, 14 => 1, 25 => 2, 29 => -1, 389 => 1],
  sparse![390; 0 => 1, 1 => -1, 2 => -1, 4 => 1, 5 => 2, 25 => 1, 194 => -1, 389 => 2],
  sparse![390; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 9 => 1, 12 => 1, 194 => 2, 389 => -1],
  sparse![390; 1 => 1, 2 => 1, 5 => -1, 14 => -1, 29 => 2, 38 => -1, 77 => 2, 129 => 1, 194 => 1, 389 => -1],
  sparse![390; 0 => 1, 14 => 1, 25 => 1, 389 => 1],
  sparse![390; 1 => 1, 12 => 1, 29 => 1, 194 => 1],
  sparse![390; 2 => 1, 4 => 1, 77 => 1, 129 => 1],
  sparse![390; 5 => 1, 9 => 1, 38 => 1, 64 => 1],
  sparse![390; 0 => 2, 2 => -1, 5 => 1, 64 => 1, 129 => -1, 389 => 2],
  sparse![390; 0 => 2, 1 => -1, 12 => -1, 25 => 2, 29 => 1, 194 => 1],
  sparse![390; 0 => 1, 1 => -1, 5 => 2, 64 => 2, 194 => -1, 389 => 1],
  sparse![390; 0 => 1, 14 => -1, 25 => 1, 29 => 2, 194 => 2, 389 => -1],
  sparse![390; 1 => 2, 2 => 1, 5 => -1, 64 => -1, 129 => 1, 194 => 2],
  sparse![390; 0 => -1, 1 => 2, 12 => 2, 14 => 1, 25 => -1, 389 => 1],
  sparse![390; 0 => -1, 1 => 1, 2 => 2, 129 => 2, 194 => 1, 389 => -1],
  sparse![390; 1 => 1, 12 => 1, 14 => 2, 29 => -1, 194 => -1, 389 => 2],
  sparse![390; 2 => 2, 5 => -1, 9 => 1, 38 => -1, 64 => 1, 77 => 2],
  sparse![390; 4 => 2, 12 => 1, 14 => -1, 25 => -1, 29 => 1, 77 => 2],
  sparse![390; 9 => 2, 12 => -1, 14 => 1, 25 => 1, 29 => -1, 38 => 2],
  sparse![390; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 129 => 1, 194 => 1],
  sparse![390; 0 => 1, 5 => 1, 64 => -2, 129 => 3, 194 => 3, 389 => -2],
  sparse![390; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 64 => 1, 389 => 1],
]
```

### Level 391

dim S₂ = **35**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **72**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![391; 0 => 2, 22 => 2],
  sparse![391; 16 => 2, 390 => 2],
  sparse![391; 0 => 1, 16 => 1, 22 => 1, 390 => 1],
]
```

### Level 392

dim S₂ = **41**; eta rank = **41**; full eta basis = **YES**; Sturm bound B = **112**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![392; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![392; 1 => 1, 3 => 1, 13 => 1, 27 => 1],
  sparse![392; 3 => 1, 7 => 1, 27 => 1, 55 => 1],
  sparse![392; 6 => 1, 13 => 1, 48 => 1, 97 => 1],
  sparse![392; 13 => 1, 27 => 1, 97 => 1, 195 => 1],
  sparse![392; 27 => 1, 55 => 1, 195 => 1, 391 => 1],
  sparse![392; 0 => 1, 6 => 1, 7 => 1, 55 => 1],
  sparse![392; 1 => -1, 3 => 3, 13 => 3, 27 => -1],
  sparse![392; 6 => 1, 48 => 1, 55 => 1, 391 => 1],
  sparse![392; 13 => -1, 27 => 3, 97 => 3, 195 => -1],
  sparse![392; 0 => 2, 1 => -1, 6 => 1, 13 => 1, 48 => -1, 97 => 2],
  sparse![392; 0 => 1, 6 => 1, 13 => 1, 97 => 1],
  sparse![392; 1 => 1, 6 => 1, 13 => 1, 48 => 1],
  sparse![392; 0 => -1, 1 => 2, 6 => 1, 13 => 1, 48 => 2, 97 => -1],
  sparse![392; 1 => 2, 3 => -1, 13 => 1, 27 => 1, 97 => -1, 195 => 2],
  sparse![392; 1 => 1, 13 => 1, 27 => 1, 195 => 1],
  sparse![392; 3 => 1, 13 => 1, 27 => 1, 97 => 1],
  sparse![392; 1 => -1, 3 => 2, 13 => 1, 27 => 1, 97 => 2, 195 => -1],
  sparse![392; 3 => 2, 7 => -1, 27 => 1, 55 => 1, 195 => -1, 391 => 2],
  sparse![392; 3 => 1, 27 => 1, 55 => 1, 391 => 1],
  sparse![392; 7 => 1, 27 => 1, 55 => 1, 195 => 1],
  sparse![392; 3 => -1, 7 => 2, 27 => 1, 55 => 1, 195 => 2, 391 => -1],
  sparse![392; 0 => -2, 1 => 5, 3 => -2, 6 => -1, 13 => 4, 27 => -1, 48 => 1, 97 => -1, 195 => 1],
  sparse![392; 0 => -1, 1 => 2, 6 => -1, 13 => 4, 27 => -1, 97 => 2, 195 => -1],
  sparse![392; 1 => -1, 3 => 2, 13 => -1, 27 => 4, 55 => -1, 195 => 2, 391 => -1],
  sparse![392; 0 => -1, 1 => 4, 3 => -2, 13 => -1, 27 => 3, 48 => 1, 97 => -1, 195 => 1],
  sparse![392; 0 => 1, 6 => 1, 55 => 1, 391 => 1],
  sparse![392; 6 => 1, 7 => 1, 48 => 1, 55 => 1],
  sparse![392; 0 => -1, 1 => 2, 6 => -1, 13 => 2, 27 => 2, 55 => -1, 195 => 2, 391 => -1],
  sparse![392; 0 => -1, 1 => 2, 13 => -1, 27 => 3, 48 => 1, 97 => 1, 195 => -1],
  sparse![392; 0 => -1, 1 => 3, 3 => -1, 13 => -1, 27 => 3, 48 => 1],
  sparse![392; 1 => -2, 3 => 4, 7 => -1, 13 => 3, 27 => -1, 97 => 1, 195 => -1, 391 => 1],
  sparse![392; 1 => -1, 3 => 1, 7 => 1, 13 => 3, 27 => -1, 195 => 2, 391 => -1],
  sparse![392; 1 => -1, 3 => 2, 13 => 3, 27 => -1, 195 => 1],
  sparse![392; 1 => -1, 3 => 3, 7 => -1, 13 => 3, 27 => -1, 391 => 1],
  sparse![392; 7 => 1, 13 => 3, 27 => -1, 97 => -1, 195 => 3, 391 => -1],
  sparse![392; 3 => 1, 13 => 3, 27 => -1, 97 => -1, 195 => 2],
  sparse![392; 3 => 2, 6 => -1, 7 => -1, 13 => 2, 27 => 2, 48 => -1, 55 => -1, 97 => 2],
  sparse![392; 3 => 2, 7 => -1, 13 => 3, 27 => -1, 97 => -1, 195 => 1, 391 => 1],
  sparse![392; 1 => 1, 3 => -1, 7 => 1, 13 => 3, 27 => -1, 97 => -2, 195 => 4, 391 => -1],
  sparse![392; 1 => 1, 13 => -1, 27 => 3, 97 => 2, 195 => -1],
]
```

### Level 393

dim S₂ = **43**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **88**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![393; 0 => 2, 130 => 2],
  sparse![393; 2 => 2, 392 => 2],
  sparse![393; 0 => 1, 2 => 1, 130 => 1, 392 => 1],
]
```

### Level 394

dim S₂ = **48**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **99**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 395

dim S₂ = **39**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **80**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![395; 0 => 2, 394 => 2],
  sparse![395; 0 => 1, 4 => 1, 78 => 1, 394 => 1],
  sparse![395; 4 => 2, 78 => 2],
]
```

### Level 396

dim S₂ = **61**; eta rank = **61**; full eta basis = **YES**; Sturm bound B = **144**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![396; 0 => 2, 10 => 2],
  sparse![396; 1 => 2, 21 => 2],
  sparse![396; 2 => 2, 32 => 2],
  sparse![396; 3 => 2, 43 => 2],
  sparse![396; 5 => 2, 65 => 2],
  sparse![396; 8 => 2, 98 => 2],
  sparse![396; 11 => 2, 131 => 2],
  sparse![396; 17 => 2, 197 => 2],
  sparse![396; 35 => 2, 395 => 2],
  sparse![396; 0 => 1, 2 => 1, 10 => 1, 32 => 1],
  sparse![396; 1 => 1, 5 => 1, 21 => 1, 65 => 1],
  sparse![396; 2 => 1, 8 => 1, 32 => 1, 98 => 1],
  sparse![396; 3 => 1, 11 => 1, 43 => 1, 131 => 1],
  sparse![396; 5 => 1, 17 => 1, 65 => 1, 197 => 1],
  sparse![396; 11 => 1, 35 => 1, 131 => 1, 395 => 1],
  sparse![396; 5 => 4],
  sparse![396; 65 => 4],
  sparse![396; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 10 => -1, 21 => 1, 32 => 3, 65 => -1],
  sparse![396; 1 => -1, 3 => 1, 5 => 3, 11 => -1, 21 => -1, 43 => 1, 65 => 3, 131 => -1],
  sparse![396; 2 => -1, 5 => 1, 8 => 3, 17 => -1, 32 => -1, 65 => 1, 98 => 3, 197 => -1],
  sparse![396; 5 => -1, 11 => 1, 17 => 3, 35 => -1, 65 => -1, 131 => 1, 197 => 3, 395 => -1],
  sparse![396; 0 => 1, 8 => 1, 10 => 1, 98 => 1],
  sparse![396; 1 => 1, 17 => 1, 21 => 1, 197 => 1],
  sparse![396; 3 => 1, 35 => 1, 43 => 1, 395 => 1],
  sparse![396; 0 => -4, 1 => 9, 2 => 2, 3 => -3, 5 => -3, 10 => 2, 11 => 1],
  sparse![396; 0 => -4, 1 => 10, 2 => 2, 3 => -4, 5 => -4, 11 => 2, 32 => -2, 65 => 6, 131 => -2],
  sparse![396; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 5 => -3, 10 => 1, 11 => 1, 32 => -1, 65 => 3, 131 => -1],
  sparse![396; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -1, 131 => 2],
  sparse![396; 0 => -3, 1 => 8, 2 => 1, 3 => -3, 5 => -2, 10 => -1, 11 => 1, 21 => 1, 32 => 3, 65 => -1],
  sparse![396; 0 => -3, 1 => 9, 2 => 1, 3 => -4, 5 => -3, 11 => 2, 43 => 2],
  sparse![396; 0 => -2, 1 => 6, 3 => -2, 21 => -1, 32 => 2, 43 => 1, 65 => 1, 131 => -1],
  sparse![396; 0 => -2, 1 => 7, 3 => -3, 5 => -1, 11 => 1, 32 => 2],
  sparse![396; 2 => -4, 5 => 9, 8 => 2, 11 => -3, 17 => -3, 32 => 2, 35 => 1],
  sparse![396; 2 => -4, 5 => 10, 8 => 2, 11 => -4, 17 => -4, 35 => 2, 98 => -2, 197 => 6, 395 => -2],
  sparse![396; 2 => -3, 5 => 6, 8 => 3, 11 => -2, 17 => -3, 32 => 1, 35 => 1, 98 => -1, 197 => 3, 395 => -1],
  sparse![396; 2 => -3, 5 => 7, 8 => 1, 11 => -2, 17 => -1, 395 => 2],
  sparse![396; 2 => -3, 5 => 8, 8 => 1, 11 => -3, 17 => -2, 32 => -1, 35 => 1, 65 => 1, 98 => 3, 197 => -1],
  sparse![396; 2 => -3, 5 => 9, 8 => 1, 11 => -4, 17 => -3, 35 => 2, 131 => 2],
  sparse![396; 2 => -2, 5 => 6, 11 => -2, 65 => -1, 98 => 2, 131 => 1, 197 => 1, 395 => -1],
  sparse![396; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 10 => -1, 17 => 1, 21 => 2, 32 => 1, 65 => -1, 197 => 1],
  sparse![396; 0 => 1, 2 => -1, 5 => 1, 8 => 2, 10 => 1, 17 => -1, 32 => -1, 65 => 1, 98 => 2, 197 => -1],
  sparse![396; 2 => 1, 5 => -1, 8 => -1, 10 => -1, 17 => 3, 21 => 2, 32 => 1, 65 => -1, 197 => 1],
  sparse![396; 2 => -1, 5 => 1, 8 => 3, 10 => 2, 17 => -1, 21 => -1, 32 => -1, 65 => 1, 98 => 1],
  sparse![396; 0 => -1, 1 => 3, 2 => 1, 5 => -1, 21 => 1, 32 => 1, 65 => -1, 98 => -1, 197 => 2],
  sparse![396; 0 => 2, 1 => -1, 2 => -1, 5 => 1, 8 => 1, 10 => 2, 21 => -1, 32 => -1, 65 => 1, 98 => 1],
  sparse![396; 0 => -2, 1 => 1, 2 => 6, 5 => -2, 8 => -2, 10 => 2, 17 => 1, 21 => -1, 32 => -2, 65 => 2, 98 => 2, 197 => -1],
  sparse![396; 0 => -2, 1 => 2, 2 => 5, 5 => -3, 8 => -2, 10 => 1, 17 => 2, 21 => -1, 32 => -1, 65 => 3, 98 => 1, 197 => -1],
  sparse![396; 0 => -2, 1 => 3, 2 => 2, 5 => -1, 10 => 1, 32 => 1],
  sparse![396; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 8 => -1, 10 => -1, 17 => 1, 21 => 1, 32 => 2, 65 => -1, 98 => 1],
  sparse![396; 0 => -1, 1 => 2, 5 => 1, 8 => 1, 17 => -1, 65 => 1, 197 => 1],
  sparse![396; 1 => -1, 3 => 2, 5 => 1, 11 => -1, 21 => -1, 35 => 1, 43 => 2, 65 => 1, 131 => -1, 395 => 1],
  sparse![396; 1 => 1, 5 => -1, 11 => 1, 17 => 2, 21 => 1, 35 => -1, 65 => -1, 131 => 1, 197 => 2, 395 => -1],
  sparse![396; 5 => 1, 11 => -1, 17 => -1, 21 => -1, 35 => 3, 43 => 2, 65 => 1, 131 => -1, 395 => 1],
  sparse![396; 5 => -1, 11 => 1, 17 => 3, 21 => 2, 35 => -1, 43 => -1, 65 => -1, 131 => 1, 197 => 1],
  sparse![396; 1 => -1, 3 => 3, 5 => 1, 11 => -1, 43 => 1, 65 => 1, 131 => -1, 197 => -1, 395 => 2],
  sparse![396; 1 => 2, 3 => -1, 5 => -1, 11 => 1, 17 => 1, 21 => 2, 43 => -1, 65 => -1, 131 => 1, 197 => 1],
  sparse![396; 1 => -2, 3 => 1, 5 => 6, 11 => -2, 17 => -2, 21 => 2, 35 => 1, 43 => -1, 65 => -2, 131 => 2, 197 => 2, 395 => -1],
  sparse![396; 1 => -2, 3 => 3, 5 => 2, 11 => -1, 21 => 1, 65 => 1],
  sparse![396; 0 => 1, 1 => 1, 2 => -1, 5 => 1, 32 => 2],
  sparse![396; 0 => 1, 1 => 1, 32 => -1, 65 => 3],
  sparse![396; 2 => 2, 10 => 1, 21 => 1, 32 => -1, 65 => 1],
]
```

### Level 397

dim S₂ = **32**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **66**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 398

dim S₂ = **49**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **100**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![398; 0 => 1, 1 => 1, 198 => 1, 397 => 1],
]
```

### Level 399

dim S₂ = **49**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **106**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 400

dim S₂ = **43**; eta rank = **43**; full eta basis = **YES**; Sturm bound B = **120**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![400; 0 => -2, 1 => 3, 3 => 1, 4 => 3, 7 => -1, 9 => -2, 19 => 1, 24 => -1, 49 => 1, 199 => 1],
  sparse![400; 0 => -2, 1 => 4, 3 => -2, 4 => 3, 7 => 1, 9 => -2, 19 => 1, 24 => -1, 99 => 3, 199 => -1],
  sparse![400; 0 => -2, 1 => 4, 3 => -1, 4 => 2, 9 => -1, 19 => 1, 49 => 1],
  sparse![400; 0 => -2, 1 => 4, 4 => 1, 7 => -1, 9 => -1, 24 => 1, 39 => 2, 49 => -1, 99 => 2, 199 => -1],
  sparse![400; 0 => -2, 1 => 5, 3 => -3, 4 => 1, 7 => 1, 9 => -3, 19 => 6, 24 => 1, 39 => -2, 99 => -1, 199 => 1],
  sparse![400; 0 => -2, 1 => 5, 3 => -2, 4 => -2, 9 => 5, 19 => -1, 99 => 1],
  sparse![400; 0 => -2, 1 => 5, 3 => -2, 19 => -1, 39 => 5, 79 => -2, 99 => 1],
  sparse![400; 0 => -2, 1 => 5, 3 => -2, 4 => 1, 9 => -2, 19 => 3, 24 => 1, 49 => -1, 99 => 1],
  sparse![400; 0 => -2, 1 => 5, 3 => -1, 4 => -2, 9 => 5, 19 => -1],
  sparse![400; 0 => -2, 1 => 5, 3 => -1, 19 => -1, 39 => 5, 79 => -2],
  sparse![400; 0 => -1, 3 => 1, 4 => 6, 9 => -3, 19 => 1, 24 => -1, 49 => 1],
  sparse![400; 0 => -1, 3 => 3, 4 => 3, 7 => -1, 9 => -2, 19 => 1, 24 => -2, 49 => 4, 99 => -2, 199 => 1],
  sparse![400; 0 => -1, 1 => 1, 4 => 3, 7 => 1, 9 => -2, 19 => 1, 24 => -2, 49 => 3, 99 => 1, 199 => -1],
  sparse![400; 0 => -1, 1 => 1, 4 => 6, 9 => -3, 19 => 1, 24 => -1, 99 => 1],
  sparse![400; 0 => -1, 1 => 1, 3 => 1, 4 => 1, 9 => 1, 99 => 1],
  sparse![400; 0 => -1, 1 => 1, 3 => 2, 4 => 1, 7 => -1, 39 => 1, 49 => 1],
  sparse![400; 0 => -1, 1 => 1, 3 => 2, 4 => 1, 7 => -1, 9 => 1, 199 => 1],
  sparse![400; 0 => -1, 1 => 1, 3 => 2, 4 => 1, 9 => 1],
  sparse![400; 0 => -1, 1 => 1, 3 => 3, 7 => -2, 19 => -1, 24 => 1, 39 => 3, 49 => -1, 99 => 2, 199 => -1],
  sparse![400; 0 => -1, 1 => 2, 3 => -2, 4 => 1, 7 => 3, 15 => -1, 19 => 1, 39 => -1, 79 => 1, 99 => 1],
  sparse![400; 0 => -1, 1 => 2, 3 => -1, 9 => 3, 19 => 1, 24 => 1, 49 => -1],
  sparse![400; 0 => -1, 1 => 2, 3 => -1, 7 => 2, 9 => 1, 15 => -1, 24 => -1, 39 => 1, 49 => 2, 99 => -1, 199 => 2, 399 => -1],
  sparse![400; 0 => -1, 1 => 2, 3 => -1, 4 => 1, 9 => -1, 19 => 4, 49 => 1, 99 => -1],
  sparse![400; 0 => -1, 1 => 2, 3 => -1, 4 => 1, 19 => 1, 39 => 3, 79 => -1, 199 => -1, 399 => 1],
  sparse![400; 0 => -1, 1 => 2, 3 => -1, 4 => 1, 7 => 1, 39 => 2, 79 => -1, 99 => 1, 199 => -1, 399 => 1],
  sparse![400; 0 => -1, 1 => 2, 3 => -1, 4 => 1, 7 => 2, 9 => -1, 15 => -1, 19 => 1, 49 => 1, 79 => 1],
  sparse![400; 0 => -1, 1 => 2, 3 => -1, 4 => 1, 7 => 2, 15 => -1, 19 => 1, 39 => -1, 79 => 1, 199 => 1],
  sparse![400; 0 => -1, 1 => 2, 3 => -1, 4 => 1, 7 => 3, 15 => -1, 19 => 1, 39 => -1, 79 => 1],
  sparse![400; 0 => -1, 1 => 2, 7 => -1, 9 => 1, 15 => 1, 24 => -1, 39 => 1, 49 => 2, 199 => -1, 399 => 1],
  sparse![400; 0 => -1, 1 => 2, 19 => -1, 24 => -1, 39 => 5, 49 => 3, 79 => -2, 99 => -1],
  sparse![400; 0 => -1, 1 => 2, 3 => 1, 4 => -1, 7 => -1, 9 => 2, 19 => -1, 24 => 2, 39 => 2, 49 => -2, 99 => 2, 199 => -1],
  sparse![400; 0 => -1, 1 => 2, 3 => 1, 7 => -1, 9 => -1, 19 => 2, 24 => 1, 39 => 1, 49 => -1, 99 => 1],
  sparse![400; 0 => -1, 1 => 3, 3 => -3, 7 => 3, 9 => -3, 15 => -1, 19 => 8, 24 => 1, 39 => -3, 99 => -1, 399 => 1],
  sparse![400; 0 => -1, 1 => 3, 3 => -2, 9 => -3, 15 => 1, 19 => 8, 24 => 1, 39 => -3, 99 => -2, 199 => 3, 399 => -1],
  sparse![400; 0 => -1, 1 => 3, 3 => -2, 4 => 1, 7 => 2, 9 => -1, 15 => -1, 19 => 1, 79 => 1, 99 => 1],
  sparse![400; 0 => -1, 1 => 4, 3 => -2, 9 => -1, 19 => 3, 24 => 1, 49 => 1, 99 => -1],
  sparse![400; 1 => -2, 3 => 3, 7 => 1, 9 => 3, 15 => -1, 19 => -1, 49 => -1, 99 => 2, 199 => -1, 399 => 1],
  sparse![400; 1 => -2, 3 => 4, 7 => -1, 9 => 3, 19 => -1, 49 => -1, 99 => 1, 199 => 1],
  sparse![400; 1 => -2, 3 => 5, 7 => -2, 9 => 1, 19 => -1, 39 => 2, 49 => 1],
  sparse![400; 1 => -2, 3 => 5, 7 => -2, 9 => 2, 19 => -1, 39 => 1, 199 => 1],
  sparse![400; 1 => -1, 7 => 4, 9 => 2, 15 => -2, 39 => -1, 49 => -1, 79 => 1, 99 => 2, 199 => -1, 399 => 1],
  sparse![400; 1 => -1, 3 => 1, 7 => 2, 9 => 1, 15 => -1, 19 => 2, 39 => -1, 99 => 1, 199 => -1, 399 => 1],
  sparse![400; 1 => -1, 3 => 1, 7 => 3, 15 => -2, 19 => 1, 39 => -2, 49 => 1, 79 => 3, 199 => 1, 399 => -1],
]
```

### Level 401

dim S₂ = **33**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **67**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 402

dim S₂ = **65**; eta rank = **16**; full eta basis = **NO**; Sturm bound B = **136**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![402; 0 => 3, 1 => -1, 66 => -1, 133 => 3],
  sparse![402; 0 => -1, 1 => 3, 66 => 3, 133 => -1],
  sparse![402; 2 => 3, 5 => -1, 200 => -1, 401 => 3],
  sparse![402; 2 => -1, 5 => 3, 200 => 3, 401 => -1],
  sparse![402; 1 => 1, 2 => 1, 66 => -2, 133 => 3, 200 => 3, 401 => -2],
  sparse![402; 0 => 1, 1 => -1, 5 => 2, 66 => -1, 133 => 1, 200 => 2],
  sparse![402; 0 => 1, 2 => -1, 5 => 2, 133 => 1, 200 => 2, 401 => -1],
  sparse![402; 0 => 2, 1 => -1, 5 => 1, 66 => -1, 133 => 2, 200 => 1],
  sparse![402; 0 => 2, 2 => -1, 5 => 1, 133 => 2, 200 => 1, 401 => -1],
  sparse![402; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 66 => 1, 401 => 1],
  sparse![402; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 133 => 1, 200 => 1],
  sparse![402; 0 => -1, 1 => 1, 2 => 2, 66 => 1, 133 => -1, 401 => 2],
  sparse![402; 0 => -1, 1 => 2, 2 => 1, 66 => 2, 133 => -1, 401 => 1],
  sparse![402; 1 => 1, 2 => 2, 5 => -1, 66 => 1, 200 => -1, 401 => 2],
  sparse![402; 1 => 2, 2 => 1, 5 => -1, 66 => 2, 200 => -1, 401 => 1],
  sparse![402; 0 => 1, 5 => 1, 66 => 3, 133 => -2, 200 => -2, 401 => 3],
]
```

### Level 403

dim S₂ = **35**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **74**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 404

dim S₂ = **49**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **102**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![404; 1 => 2, 201 => 2],
]
```

### Level 405

dim S₂ = **43**; eta rank = **43**; full eta basis = **YES**; Sturm bound B = **108**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![405; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![405; 2 => 1, 8 => 1, 14 => 1, 44 => 1],
  sparse![405; 8 => 1, 26 => 1, 44 => 1, 134 => 1],
  sparse![405; 26 => 1, 80 => 1, 134 => 1, 404 => 1],
  sparse![405; 2 => 2, 8 => 2],
  sparse![405; 8 => 2, 26 => 2],
  sparse![405; 14 => 2, 44 => 2],
  sparse![405; 44 => 2, 134 => 2],
  sparse![405; 2 => -1, 8 => 6, 26 => -1],
  sparse![405; 2 => 1, 8 => 2, 26 => 1],
  sparse![405; 14 => -1, 44 => 6, 134 => -1],
  sparse![405; 14 => 1, 44 => 2, 134 => 1],
  sparse![405; 0 => 1, 4 => 1, 26 => 1, 134 => 1],
  sparse![405; 2 => 2, 44 => 2],
  sparse![405; 8 => 2, 14 => 2],
  sparse![405; 0 => -1, 2 => 2, 4 => 2, 8 => 1],
  sparse![405; 0 => -1, 2 => 3, 4 => 2, 14 => -1, 44 => 1],
  sparse![405; 2 => -1, 8 => 3, 14 => 3, 44 => -1],
  sparse![405; 14 => 1, 26 => 2, 44 => 2, 134 => -1],
  sparse![405; 8 => 3, 14 => 1, 26 => -1, 44 => -1, 134 => 2],
  sparse![405; 2 => 1, 14 => 1, 80 => 1, 404 => 1],
  sparse![405; 8 => 2, 134 => 2],
  sparse![405; 26 => 2, 44 => 2],
  sparse![405; 2 => -1, 8 => 2, 14 => 2, 26 => 1],
  sparse![405; 2 => -1, 8 => 3, 14 => 2, 44 => -1, 134 => 1],
  sparse![405; 8 => -1, 26 => 3, 44 => 3, 134 => -1],
  sparse![405; 44 => 1, 80 => 2, 134 => 2, 404 => -1],
  sparse![405; 2 => 1, 8 => -1, 14 => -1, 26 => 2, 44 => 3],
  sparse![405; 2 => -1, 8 => 3, 14 => 1, 44 => -1, 134 => 2],
  sparse![405; 2 => 2, 8 => -1, 26 => 1, 44 => 3, 134 => -1],
  sparse![405; 8 => 2, 14 => 1, 134 => 1],
  sparse![405; 2 => 1, 26 => 1, 44 => 2],
  sparse![405; 0 => 1, 2 => 1, 4 => 1, 134 => 1],
  sparse![405; 0 => 1, 4 => 1, 14 => 1, 26 => 1],
  sparse![405; 2 => 1, 8 => 1, 44 => 1, 134 => 1],
  sparse![405; 2 => 1, 80 => 1, 134 => 1, 404 => 1],
  sparse![405; 8 => 1, 14 => 1, 26 => 1, 44 => 1],
  sparse![405; 0 => -1, 2 => 2, 4 => 2, 14 => -1, 26 => 1, 44 => 1],
  sparse![405; 0 => -1, 2 => 2, 4 => 2, 8 => 1, 14 => -1, 134 => 1],
  sparse![405; 2 => -1, 8 => 3, 44 => 3, 134 => -1],
  sparse![405; 8 => 1, 14 => 1, 26 => -1, 80 => 2, 134 => 2, 404 => -1],
  sparse![405; 8 => 3, 14 => -1, 26 => -1, 44 => 3],
  sparse![405; 2 => 1, 26 => -1, 44 => 1, 80 => 2, 134 => 2, 404 => -1],
]
```

### Level 406

dim S₂ = **57**; eta rank = **18**; full eta basis = **NO**; Sturm bound B = **120**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![406; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![406; 28 => 1, 57 => 1, 202 => 1, 405 => 1],
  sparse![406; 0 => 2, 202 => 2],
  sparse![406; 0 => 1, 6 => 1, 28 => 1, 202 => 1],
  sparse![406; 6 => 2, 28 => 2],
  sparse![406; 1 => 2, 405 => 2],
  sparse![406; 1 => 1, 13 => 1, 57 => 1, 405 => 1],
  sparse![406; 13 => 2, 57 => 2],
  sparse![406; 0 => 2, 1 => -1, 6 => 2, 13 => -1, 28 => -1, 57 => 2, 202 => -1, 405 => 2],
  sparse![406; 0 => -1, 1 => 2, 6 => 2, 13 => -1, 57 => 1, 202 => 1],
  sparse![406; 1 => 1, 6 => 1, 28 => -1, 57 => 2, 202 => 2, 405 => -1],
  sparse![406; 0 => -1, 1 => 2, 6 => 1, 28 => 1, 202 => -1, 405 => 2],
  sparse![406; 0 => 1, 6 => -1, 13 => 2, 28 => -1, 57 => 2, 202 => 1],
  sparse![406; 1 => 1, 6 => 2, 13 => -1, 28 => 2, 57 => -1, 405 => 1],
  sparse![406; 0 => 2, 1 => -1, 13 => 1, 57 => 1, 202 => 2, 405 => -1],
  sparse![406; 0 => 1, 13 => 1, 28 => 2, 57 => -1, 202 => -1, 405 => 2],
  sparse![406; 0 => 2, 1 => -1, 6 => -1, 13 => 2, 28 => 1, 405 => 1],
  sparse![406; 0 => -1, 1 => 2, 6 => -1, 13 => 2, 28 => 2, 57 => -1, 202 => 2, 405 => -1],
]
```

### Level 407

dim S₂ = **37**; eta rank = **5**; full eta basis = **NO**; Sturm bound B = **76**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![407; 0 => 2, 10 => 2],
  sparse![407; 36 => 2, 406 => 2],
  sparse![407; 0 => 2, 406 => 2],
  sparse![407; 0 => 1, 10 => 1, 36 => 1, 406 => 1],
  sparse![407; 10 => 2, 36 => 2],
]
```

### Level 408

dim S₂ = **65**; eta rank = **65**; full eta basis = **YES**; Sturm bound B = **144**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![408; 1 => 1, 3 => 1, 5 => 1, 11 => 1],
  sparse![408; 33 => 1, 67 => 1, 101 => 1, 203 => 1],
  sparse![408; 0 => 1, 2 => 1, 16 => 1, 50 => 1],
  sparse![408; 1 => 1, 5 => 1, 33 => 1, 101 => 1],
  sparse![408; 3 => 1, 11 => 1, 67 => 1, 203 => 1],
  sparse![408; 7 => 1, 23 => 1, 135 => 1, 407 => 1],
  sparse![408; 0 => 2, 1 => -1, 3 => 1, 16 => -2, 33 => 5, 67 => -1],
  sparse![408; 0 => 1, 1 => -1, 3 => 2, 16 => -1, 33 => 5, 67 => -2],
  sparse![408; 0 => 1, 1 => 2, 3 => -1, 16 => -1, 33 => 2, 67 => 1],
  sparse![408; 1 => 2, 33 => 2],
  sparse![408; 0 => -1, 1 => 2, 3 => 1, 16 => 1, 33 => 2, 67 => -1],
  sparse![408; 0 => -1, 1 => 5, 3 => -2, 16 => 1, 33 => -1, 67 => 2],
  sparse![408; 0 => -2, 1 => 5, 3 => -1, 16 => 2, 33 => -1, 67 => 1],
  sparse![408; 1 => 2, 3 => -1, 7 => 1, 33 => -2, 67 => 5, 135 => -1],
  sparse![408; 1 => 1, 3 => -1, 7 => 2, 33 => -1, 67 => 5, 135 => -2],
  sparse![408; 3 => 2, 67 => 2],
  sparse![408; 1 => -1, 3 => 2, 7 => 1, 33 => 1, 67 => 2, 135 => -1],
  sparse![408; 2 => 2, 5 => -1, 11 => 1, 50 => -2, 101 => 5, 203 => -1],
  sparse![408; 2 => 1, 5 => -1, 11 => 2, 50 => -1, 101 => 5, 203 => -2],
  sparse![408; 2 => 1, 5 => 2, 11 => -1, 50 => -1, 101 => 2, 203 => 1],
  sparse![408; 5 => 2, 101 => 2],
  sparse![408; 2 => -1, 5 => 2, 11 => 1, 50 => 1, 101 => 2, 203 => -1],
  sparse![408; 2 => -1, 5 => 5, 11 => -2, 50 => 1, 101 => -1, 203 => 2],
  sparse![408; 2 => -2, 5 => 5, 11 => -1, 50 => 2, 101 => -1, 203 => 1],
  sparse![408; 5 => 2, 11 => -1, 23 => 1, 101 => -2, 203 => 5, 407 => -1],
  sparse![408; 5 => 1, 11 => -1, 23 => 2, 101 => -1, 203 => 5, 407 => -2],
  sparse![408; 11 => 2, 203 => 2],
  sparse![408; 5 => -1, 11 => 2, 23 => 1, 101 => 1, 203 => 2, 407 => -1],
  sparse![408; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 16 => 1, 101 => 1],
  sparse![408; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 33 => 1, 50 => 1],
  sparse![408; 1 => 2, 2 => 1, 5 => -1, 16 => -1, 33 => 1, 50 => 2],
  sparse![408; 0 => 2, 2 => -1, 5 => 1, 16 => 1, 33 => -1, 101 => 2],
  sparse![408; 0 => -1, 1 => 3, 2 => 1, 5 => -1, 16 => 1, 33 => -1, 50 => -1, 101 => 3],
  sparse![408; 0 => 3, 1 => -1, 2 => -1, 5 => 1, 16 => -1, 33 => 1, 50 => 3, 101 => -1],
  sparse![408; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 16 => 3, 33 => -1, 50 => -1, 101 => 1],
  sparse![408; 1 => -2, 3 => 3, 5 => 3, 11 => -2, 33 => 1, 203 => 1],
  sparse![408; 1 => 3, 3 => -2, 5 => -2, 11 => 3, 67 => 1, 101 => 1],
  sparse![408; 3 => 2, 5 => 1, 11 => -1, 33 => -1, 67 => 1, 101 => 2],
  sparse![408; 1 => 2, 5 => -1, 11 => 1, 33 => 1, 67 => -1, 203 => 2],
  sparse![408; 1 => 3, 3 => -1, 5 => -1, 11 => 1, 33 => -1, 67 => 1, 101 => 3, 203 => -1],
  sparse![408; 3 => -2, 7 => 3, 11 => 3, 23 => -2, 67 => 1, 407 => 1],
  sparse![408; 3 => 3, 7 => -2, 11 => -2, 23 => 3, 135 => 1, 203 => 1],
  sparse![408; 7 => 2, 11 => 1, 23 => -1, 67 => -1, 135 => 1, 203 => 2],
  sparse![408; 3 => 2, 11 => -1, 23 => 1, 67 => 1, 135 => -1, 407 => 2],
  sparse![408; 3 => 3, 7 => -1, 11 => -1, 23 => 1, 67 => -1, 135 => 1, 203 => 3, 407 => -1],
  sparse![408; 0 => -1, 1 => 1, 3 => 3, 7 => -1, 16 => 1, 33 => -1, 67 => 1, 135 => 1],
  sparse![408; 0 => -1, 1 => 3, 3 => 1, 7 => -1, 16 => 1, 33 => 1, 67 => -1, 135 => 1],
  sparse![408; 2 => -1, 5 => 1, 11 => 3, 23 => -1, 50 => 1, 101 => -1, 203 => 1, 407 => 1],
  sparse![408; 2 => -1, 5 => 3, 11 => 1, 23 => -1, 50 => 1, 101 => 1, 203 => -1, 407 => 1],
  sparse![408; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 5 => -3, 11 => 1, 16 => -1, 33 => 3, 50 => 1, 67 => -1],
  sparse![408; 0 => -3, 1 => 8, 2 => 1, 3 => -3, 5 => -2, 11 => 1, 16 => -3, 33 => 8, 50 => 1, 67 => -3, 101 => -2, 203 => 1],
  sparse![408; 1 => -3, 3 => 6, 5 => 3, 7 => -2, 11 => -3, 23 => 1, 33 => -1, 67 => 3, 101 => 1, 135 => -1],
  sparse![408; 1 => -3, 3 => 8, 5 => 1, 7 => -3, 11 => -2, 23 => 1, 33 => -3, 67 => 8, 101 => 1, 135 => -3, 203 => -2, 407 => 1],
  sparse![408; 1 => -2, 3 => 4, 5 => 2, 11 => -2, 203 => 2],
  sparse![408; 1 => 2, 3 => -2, 5 => -2, 11 => 4, 67 => 2],
  sparse![408; 1 => 4, 3 => -2, 5 => -2, 11 => 2, 101 => 2],
  sparse![408; 11 => 2, 33 => -2, 67 => 4, 101 => 2, 203 => -2],
  sparse![408; 3 => -1, 5 => 1, 7 => 2, 33 => -2, 67 => 5, 101 => 1, 135 => -2],
  sparse![408; 0 => 2, 1 => -1, 11 => 1, 16 => -2, 33 => 5, 67 => -2, 203 => 1],
  sparse![408; 1 => 1, 3 => -2, 5 => -2, 7 => 1, 11 => 4, 33 => 1, 67 => 2, 135 => -1],
  sparse![408; 1 => -2, 3 => 4, 5 => 1, 11 => -2, 23 => 1, 101 => 1, 203 => 2, 407 => -1],
  sparse![408; 1 => 1, 3 => 1, 101 => 1, 203 => 1],
  sparse![408; 0 => 1, 1 => 1, 3 => -1, 5 => -1, 11 => 1, 23 => 1, 50 => 1, 135 => 1],
  sparse![408; 0 => 1, 1 => -1, 5 => 1, 7 => 1, 50 => 1, 67 => 1, 203 => -1, 407 => 1],
  sparse![408; 0 => 1, 3 => -1, 7 => 1, 11 => 1, 33 => 1, 50 => 1, 101 => -1, 407 => 1],
]
```

### Level 409

dim S₂ = **33**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **68**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 410

dim S₂ = **59**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **126**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 411

dim S₂ = **45**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **92**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![411; 0 => 1, 2 => 1, 136 => 1, 410 => 1],
]
```

### Level 412

dim S₂ = **50**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **104**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![412; 0 => 1, 1 => 1, 102 => 1, 205 => 1],
  sparse![412; 1 => 1, 3 => 1, 205 => 1, 411 => 1],
  sparse![412; 0 => -1, 1 => 4, 3 => -1, 102 => -1, 205 => 4, 411 => -1],
]
```

### Level 413

dim S₂ = **39**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **80**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![413; 0 => 2, 58 => 2],
  sparse![413; 6 => 2, 412 => 2],
  sparse![413; 0 => 1, 6 => 1, 58 => 1, 412 => 1],
]
```

### Level 414

dim S₂ = **65**; eta rank = **56**; full eta basis = **NO**; Sturm bound B = **144**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![414; 0 => 2, 22 => 2],
  sparse![414; 1 => 2, 45 => 2],
  sparse![414; 2 => 2, 68 => 2],
  sparse![414; 5 => 2, 137 => 2],
  sparse![414; 8 => 2, 206 => 2],
  sparse![414; 17 => 2, 413 => 2],
  sparse![414; 0 => -1, 1 => 3, 22 => -1, 45 => 3],
  sparse![414; 0 => 1, 1 => 1, 22 => 1, 45 => 1],
  sparse![414; 0 => 3, 1 => -1, 22 => 3, 45 => -1],
  sparse![414; 2 => -1, 5 => 3, 68 => -1, 137 => 3],
  sparse![414; 2 => 1, 5 => 1, 68 => 1, 137 => 1],
  sparse![414; 2 => 3, 5 => -1, 68 => 3, 137 => -1],
  sparse![414; 8 => -1, 17 => 3, 206 => -1, 413 => 3],
  sparse![414; 8 => 1, 17 => 1, 206 => 1, 413 => 1],
  sparse![414; 8 => 3, 17 => -1, 206 => 3, 413 => -1],
  sparse![414; 0 => 1, 2 => 1, 22 => 1, 68 => 1],
  sparse![414; 1 => 1, 5 => 1, 45 => 1, 137 => 1],
  sparse![414; 2 => 1, 8 => 1, 68 => 1, 206 => 1],
  sparse![414; 5 => 1, 17 => 1, 137 => 1, 413 => 1],
  sparse![414; 0 => 1, 1 => -1, 2 => -2, 5 => 4, 22 => 1, 45 => -1, 68 => -2, 137 => 4],
  sparse![414; 0 => 1, 1 => -1, 2 => -1, 5 => 3, 22 => 1, 45 => -1, 68 => -1, 137 => 3],
  sparse![414; 0 => -1, 1 => 1, 2 => 2, 22 => -1, 45 => 1, 68 => 2],
  sparse![414; 0 => 1, 1 => -1, 5 => 2, 22 => 1, 45 => -1, 137 => 2],
  sparse![414; 2 => 1, 5 => -1, 8 => -2, 17 => 4, 68 => 1, 137 => -1, 206 => -2, 413 => 4],
  sparse![414; 2 => 1, 5 => -1, 8 => -1, 17 => 3, 68 => 1, 137 => -1, 206 => -1, 413 => 3],
  sparse![414; 2 => -1, 5 => 1, 8 => 2, 68 => -1, 137 => 1, 206 => 2],
  sparse![414; 2 => 1, 5 => -1, 17 => 2, 68 => 1, 137 => -1, 413 => 2],
  sparse![414; 0 => 1, 8 => 1, 22 => 1, 206 => 1],
  sparse![414; 1 => 1, 17 => 1, 45 => 1, 413 => 1],
  sparse![414; 0 => 1, 1 => -2, 2 => -3, 5 => 7, 8 => 1, 17 => -2, 22 => -2, 45 => 1, 68 => 7, 137 => -3, 206 => -2, 413 => 1],
  sparse![414; 0 => 1, 1 => -2, 2 => -3, 5 => 7, 8 => 1, 17 => -2, 22 => 4, 45 => -2, 68 => -1, 137 => 1],
  sparse![414; 0 => 1, 1 => -2, 2 => -3, 5 => 7, 8 => 1, 17 => -2, 22 => 2, 45 => -1, 206 => -1, 413 => 2],
  sparse![414; 2 => -1, 5 => 1, 8 => 4, 17 => -2, 22 => -2, 45 => 1, 68 => 7, 137 => -3, 206 => -2, 413 => 1],
  sparse![414; 2 => -1, 5 => 1, 8 => 2, 22 => 2, 45 => -1, 68 => -1, 137 => 1, 413 => 1],
  sparse![414; 8 => 2, 22 => 2, 45 => -1, 413 => 1],
  sparse![414; 2 => -1, 5 => 1, 8 => 3, 17 => -1, 22 => 2, 45 => -1, 68 => -1, 137 => 1, 206 => 1],
  sparse![414; 8 => 3, 17 => -1, 22 => 2, 45 => -1, 206 => 1],
  sparse![414; 2 => 1, 8 => 1, 22 => 2, 45 => -1, 68 => 1, 206 => -1, 413 => 1],
  sparse![414; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 8 => 1, 22 => 1, 68 => 2, 137 => -1, 206 => -1, 413 => 1],
  sparse![414; 0 => 1, 1 => -1, 2 => -2, 5 => 3, 8 => 2, 17 => -1, 22 => 3, 45 => -2, 68 => -2, 137 => 3],
  sparse![414; 0 => -1, 1 => 1, 2 => 1, 8 => 2, 17 => -1, 22 => 1, 68 => 1],
  sparse![414; 0 => -1, 1 => 2, 17 => 1, 22 => 2, 45 => -1, 68 => -1, 137 => 1, 413 => 1],
  sparse![414; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 17 => 1, 22 => 2, 45 => -1, 413 => 1],
  sparse![414; 0 => -1, 1 => 2, 8 => 1, 22 => 2, 45 => -1, 68 => -1, 137 => 1, 206 => 1],
  sparse![414; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 8 => 1, 22 => 2, 45 => -1, 206 => 1],
  sparse![414; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 8 => -1, 17 => 1, 22 => 1, 68 => 2, 137 => -1, 206 => -1, 413 => 1],
  sparse![414; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 8 => 1, 22 => -1, 45 => 1, 68 => 3, 137 => -2, 206 => -2, 413 => 3],
  sparse![414; 0 => 1, 1 => -2, 2 => -2, 5 => 6, 8 => 1, 17 => -2, 22 => -1, 45 => 2, 68 => 2, 137 => -2, 206 => -1, 413 => 2],
  sparse![414; 0 => 2, 1 => -1, 2 => -2, 5 => 2, 8 => 2, 17 => -1, 22 => -2, 45 => 1, 68 => 6, 137 => -2, 206 => -2, 413 => 1],
  sparse![414; 2 => 2, 5 => -1, 8 => 1, 22 => 2, 45 => -1, 68 => 2, 137 => -1, 206 => -1, 413 => 1],
  sparse![414; 5 => 1, 8 => 2, 17 => -1, 22 => 2, 45 => -1, 137 => 1],
  sparse![414; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 8 => 2, 17 => -1, 22 => 1, 68 => 2, 137 => -1],
  sparse![414; 0 => 1, 1 => -1, 2 => -2, 5 => 3, 8 => 3, 17 => -2, 22 => 3, 45 => -2, 68 => -2, 137 => 3, 206 => 1, 413 => -1],
  sparse![414; 1 => 1, 5 => 1, 22 => 3, 45 => -2, 68 => -1, 137 => 2],
  sparse![414; 5 => 1, 17 => 1, 22 => 2, 45 => -1, 68 => -1, 137 => 2, 206 => 1, 413 => -1],
  sparse![414; 0 => 1, 1 => -1, 2 => -2, 5 => 3, 8 => 2, 17 => -1, 22 => 1, 45 => -1, 68 => -1, 137 => 2, 206 => -1, 413 => 2],
]
```

### Level 415

dim S₂ = **41**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **84**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![415; 0 => 2, 82 => 2],
  sparse![415; 4 => 2, 414 => 2],
  sparse![415; 0 => 1, 4 => 1, 82 => 1, 414 => 1],
]
```

### Level 416

dim S₂ = **49**; eta rank = **49**; full eta basis = **YES**; Sturm bound B = **112**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![416; 3 => 2, 7 => 2],
  sparse![416; 51 => 2, 103 => 2],
  sparse![416; 0 => 1, 3 => 2, 7 => -1, 12 => -1, 25 => 2, 103 => 1],
  sparse![416; 0 => -1, 1 => 1, 3 => 3, 7 => -1, 12 => 1, 25 => 1, 51 => -1, 103 => 1],
  sparse![416; 0 => -1, 1 => 2, 7 => 1, 12 => 1, 51 => 2, 103 => -1],
  sparse![416; 0 => -1, 1 => 2, 3 => 2, 7 => -1, 12 => 1, 103 => 1],
  sparse![416; 0 => -1, 1 => 3, 3 => -1, 7 => 1, 12 => 1, 25 => -1, 51 => 3, 103 => -1],
  sparse![416; 0 => -1, 1 => 3, 3 => 1, 7 => -1, 12 => 1, 25 => -1, 51 => 1, 103 => 1],
  sparse![416; 0 => -1, 1 => 4, 3 => -2, 7 => 1, 12 => 1, 25 => -2, 51 => 4, 103 => -1],
  sparse![416; 0 => 1, 1 => -2, 3 => 4, 7 => -1, 12 => -1, 25 => 4, 51 => -2, 103 => 1],
  sparse![416; 0 => 1, 1 => -1, 3 => 1, 7 => 1, 12 => -1, 25 => 3, 51 => 1, 103 => -1],
  sparse![416; 0 => 1, 1 => -1, 3 => 3, 7 => -1, 12 => -1, 25 => 3, 51 => -1, 103 => 1],
  sparse![416; 0 => 1, 7 => 1, 12 => -1, 25 => 2, 51 => 2, 103 => -1],
  sparse![416; 1 => 1, 7 => 2, 15 => -1, 25 => -1, 51 => 2, 207 => 1],
  sparse![416; 1 => -1, 3 => 1, 7 => 3, 15 => -1, 25 => 1, 51 => 1, 103 => -1, 207 => 1],
  sparse![416; 1 => -1, 3 => 2, 7 => 2, 15 => -1, 25 => 1, 207 => 1],
  sparse![416; 1 => -1, 3 => 3, 7 => 1, 15 => -1, 25 => 1, 51 => -1, 103 => 1, 207 => 1],
  sparse![416; 1 => 1, 3 => -2, 7 => 4, 15 => -1, 25 => -1, 51 => 4, 103 => -2, 207 => 1],
  sparse![416; 1 => 1, 3 => -1, 7 => 3, 15 => -1, 25 => -1, 51 => 3, 103 => -1, 207 => 1],
  sparse![416; 3 => 1, 15 => 2, 31 => -1, 51 => -1, 103 => 2, 415 => 1],
  sparse![416; 3 => -1, 7 => 1, 15 => 3, 31 => -1, 51 => 1, 103 => 1, 207 => -1, 415 => 1],
  sparse![416; 3 => -1, 7 => 2, 15 => 2, 31 => -1, 51 => 1, 415 => 1],
  sparse![416; 3 => -1, 7 => 3, 15 => 1, 31 => -1, 51 => 1, 103 => -1, 207 => 1, 415 => 1],
  sparse![416; 3 => 1, 7 => -2, 15 => 4, 31 => -1, 51 => -1, 103 => 4, 207 => -2, 415 => 1],
  sparse![416; 3 => 1, 7 => -1, 15 => 3, 31 => -1, 51 => -1, 103 => 3, 207 => -1, 415 => 1],
  sparse![416; 0 => -1, 1 => 1, 3 => 2, 12 => 1, 25 => 1],
  sparse![416; 0 => -1, 1 => 2, 3 => 1, 12 => 1, 51 => 1],
  sparse![416; 0 => -1, 1 => 3, 12 => 1, 25 => -1, 51 => 2],
  sparse![416; 0 => -1, 1 => 4, 3 => -1, 12 => 1, 25 => -2, 51 => 3],
  sparse![416; 3 => -1, 7 => 4, 15 => -1, 51 => 3, 103 => -2, 207 => 1],
  sparse![416; 3 => 2, 7 => 1, 15 => -1, 103 => 1, 207 => 1],
  sparse![416; 1 => -1, 3 => 1, 7 => 2, 25 => 1, 51 => 1],
  sparse![416; 1 => -1, 3 => 2, 7 => 1, 25 => 1, 103 => 1],
  sparse![416; 1 => -1, 3 => 3, 25 => 1, 51 => -1, 103 => 2],
  sparse![416; 1 => -1, 3 => 4, 7 => -1, 25 => 1, 51 => -2, 103 => 3],
  sparse![416; 7 => -1, 15 => 4, 31 => -1, 103 => 3, 207 => -2, 415 => 1],
  sparse![416; 7 => 2, 15 => 1, 31 => -1, 207 => 1, 415 => 1],
  sparse![416; 0 => 1, 1 => -1, 3 => 2, 7 => -1, 12 => -1, 25 => 3, 31 => 1, 51 => -2, 103 => 1, 207 => 2, 415 => -1],
  sparse![416; 3 => -1, 7 => 3, 51 => 3, 103 => -1],
  sparse![416; 3 => 3, 7 => -1, 51 => -1, 103 => 3],
  sparse![416; 1 => 2, 3 => -2, 7 => 2, 25 => -2, 51 => 4],
  sparse![416; 1 => -2, 3 => 4, 25 => 2, 51 => -2, 103 => 2],
  sparse![416; 3 => 2, 7 => -2, 15 => 2, 103 => 4, 207 => -2],
  sparse![416; 7 => 2, 51 => 2],
  sparse![416; 3 => 2, 103 => 2],
  sparse![416; 0 => -1, 1 => 3, 3 => -2, 7 => 1, 12 => 1, 15 => 2, 25 => -1, 31 => -1, 51 => 2, 103 => -1, 415 => 1],
  sparse![416; 3 => 1, 7 => 1, 51 => 1, 103 => 1],
  sparse![416; 0 => -2, 1 => 5, 3 => -2, 15 => 2, 31 => -1, 103 => 3, 207 => -2, 415 => 1],
  sparse![416; 0 => -1, 3 => 5, 7 => -2, 12 => 1, 25 => -2, 51 => 3],
]
```

### Level 417

dim S₂ = **45**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **93**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 418

dim S₂ = **57**; eta rank = **18**; full eta basis = **NO**; Sturm bound B = **120**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![418; 0 => 2, 10 => 2],
  sparse![418; 1 => 2, 21 => 2],
  sparse![418; 18 => 2, 208 => 2],
  sparse![418; 37 => 2, 417 => 2],
  sparse![418; 0 => 3, 1 => -1, 18 => -1, 37 => 3],
  sparse![418; 0 => -1, 1 => 3, 18 => 3, 37 => -1],
  sparse![418; 10 => 3, 21 => -1, 208 => -1, 417 => 3],
  sparse![418; 10 => -1, 21 => 3, 208 => 3, 417 => -1],
  sparse![418; 0 => 1, 10 => 1, 18 => 1, 208 => 1],
  sparse![418; 1 => 1, 21 => 1, 37 => 1, 417 => 1],
  sparse![418; 0 => -1, 1 => 2, 10 => -1, 18 => 1, 21 => 2, 208 => 1],
  sparse![418; 0 => 1, 10 => 1, 18 => -1, 37 => 2, 208 => -1, 417 => 2],
  sparse![418; 0 => 1, 10 => -1, 21 => 2, 37 => 1, 208 => 2, 417 => -1],
  sparse![418; 0 => 2, 1 => -1, 18 => -1, 21 => 1, 37 => 2, 208 => 1],
  sparse![418; 0 => -1, 1 => 2, 10 => 1, 18 => 2, 37 => -1, 417 => 1],
  sparse![418; 1 => 1, 10 => 2, 18 => 1, 21 => -1, 208 => -1, 417 => 2],
  sparse![418; 1 => 1, 18 => 2, 21 => 1, 37 => -1, 208 => 2, 417 => -1],
  sparse![418; 0 => 2, 1 => -1, 10 => 2, 21 => -1, 37 => 1, 417 => 1],
]
```

### Level 419

dim S₂ = **35**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **70**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![419; 0 => 2, 418 => 2],
]
```

### Level 420

dim S₂ = **85**; eta rank = **85**; full eta basis = **YES**; Sturm bound B = **192**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![420; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![420; 1 => 1, 3 => 1, 13 => 1, 27 => 1],
  sparse![420; 2 => 1, 5 => 1, 20 => 1, 41 => 1],
  sparse![420; 4 => 1, 9 => 1, 34 => 1, 69 => 1],
  sparse![420; 5 => 1, 11 => 1, 41 => 1, 83 => 1],
  sparse![420; 9 => 1, 19 => 1, 69 => 1, 139 => 1],
  sparse![420; 14 => 1, 29 => 1, 104 => 1, 209 => 1],
  sparse![420; 29 => 1, 59 => 1, 209 => 1, 419 => 1],
  sparse![420; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![420; 1 => 1, 5 => 1, 9 => 1, 29 => 1],
  sparse![420; 3 => 1, 11 => 1, 19 => 1, 59 => 1],
  sparse![420; 6 => 1, 20 => 1, 34 => 1, 104 => 1],
  sparse![420; 13 => 1, 41 => 1, 69 => 1, 209 => 1],
  sparse![420; 27 => 1, 83 => 1, 139 => 1, 419 => 1],
  sparse![420; 1 => 2, 9 => 2],
  sparse![420; 5 => 2, 29 => 2],
  sparse![420; 13 => 2, 69 => 2],
  sparse![420; 41 => 2, 209 => 2],
  sparse![420; 0 => 1, 1 => 1, 14 => 1, 29 => 1],
  sparse![420; 1 => 1, 3 => 1, 29 => 1, 59 => 1],
  sparse![420; 6 => 1, 13 => 1, 104 => 1, 209 => 1],
  sparse![420; 13 => 1, 27 => 1, 209 => 1, 419 => 1],
  sparse![420; 0 => 2, 34 => 2],
  sparse![420; 0 => 1, 4 => 1, 6 => 1, 34 => 1],
  sparse![420; 4 => 2, 6 => 2],
  sparse![420; 1 => 2, 69 => 2],
  sparse![420; 1 => 1, 9 => 1, 13 => 1, 69 => 1],
  sparse![420; 9 => 2, 13 => 2],
  sparse![420; 2 => 2, 104 => 2],
  sparse![420; 2 => 1, 14 => 1, 20 => 1, 104 => 1],
  sparse![420; 14 => 2, 20 => 2],
  sparse![420; 3 => 2, 139 => 2],
  sparse![420; 3 => 1, 19 => 1, 27 => 1, 139 => 1],
  sparse![420; 19 => 2, 27 => 2],
  sparse![420; 5 => 2, 209 => 2],
  sparse![420; 5 => 1, 29 => 1, 41 => 1, 209 => 1],
  sparse![420; 29 => 2, 41 => 2],
  sparse![420; 11 => 2, 419 => 2],
  sparse![420; 11 => 1, 59 => 1, 83 => 1, 419 => 1],
  sparse![420; 59 => 2, 83 => 2],
  sparse![420; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 6 => 4, 13 => -2, 20 => -1, 41 => 1],
  sparse![420; 0 => -1, 1 => 1, 2 => 4, 5 => -2, 6 => 1, 13 => -1, 20 => -2, 41 => 4],
  sparse![420; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 6 => -1, 13 => 2, 20 => 2, 41 => -1],
  sparse![420; 1 => -2, 3 => 4, 5 => 1, 11 => -1, 13 => 4, 27 => -2, 41 => -1, 83 => 1],
  sparse![420; 1 => -1, 3 => 1, 5 => 4, 11 => -2, 13 => 1, 27 => -1, 41 => -2, 83 => 4],
  sparse![420; 4 => -2, 9 => 4, 14 => 1, 29 => -1, 34 => 4, 69 => -2, 104 => -1, 209 => 1],
  sparse![420; 4 => -1, 9 => 1, 14 => 4, 29 => -2, 34 => 1, 69 => -1, 104 => -2, 209 => 4],
  sparse![420; 4 => -1, 9 => 2, 14 => 2, 29 => -1, 34 => -1, 69 => 2, 104 => 2, 209 => -1],
  sparse![420; 9 => -2, 19 => 4, 29 => 1, 59 => -1, 69 => 4, 139 => -2, 209 => -1, 419 => 1],
  sparse![420; 9 => -1, 19 => 1, 29 => 4, 59 => -2, 69 => 1, 139 => -1, 209 => -2, 419 => 4],
  sparse![420; 0 => 1, 4 => 2, 9 => -1, 13 => 1, 34 => -1, 69 => 2],
  sparse![420; 1 => 1, 9 => 2, 19 => -1, 27 => 1, 69 => -1, 139 => 2],
  sparse![420; 2 => 1, 14 => 2, 29 => -1, 41 => 1, 104 => -1, 209 => 2],
  sparse![420; 5 => 1, 29 => 2, 59 => -1, 83 => 1, 209 => -1, 419 => 2],
  sparse![420; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -2, 11 => 1, 13 => 4, 27 => -2, 41 => -1, 83 => 1],
  sparse![420; 0 => -3, 1 => 7, 2 => 2, 3 => -2, 5 => -3, 6 => 1, 11 => 1, 13 => -3, 20 => -2, 27 => 2, 41 => 7, 83 => -3],
  sparse![420; 4 => -3, 9 => 7, 14 => 1, 19 => -2, 29 => -2, 59 => 1, 69 => 4, 139 => -2, 209 => -1, 419 => 1],
  sparse![420; 4 => -3, 9 => 7, 14 => 2, 19 => -2, 29 => -3, 34 => 1, 59 => 1, 69 => -3, 104 => -2, 139 => 2, 209 => 7, 419 => -3],
  sparse![420; 0 => 1, 14 => 1, 20 => 1, 34 => 1],
  sparse![420; 0 => 1, 2 => 1, 34 => 1, 104 => 1],
  sparse![420; 1 => 1, 29 => 1, 41 => 1, 69 => 1],
  sparse![420; 1 => 1, 5 => 1, 69 => 1, 209 => 1],
  sparse![420; 3 => 1, 59 => 1, 83 => 1, 139 => 1],
  sparse![420; 3 => 1, 11 => 1, 139 => 1, 419 => 1],
  sparse![420; 0 => 1, 6 => 1, 19 => 1, 139 => 1],
  sparse![420; 0 => -2, 1 => 4, 3 => -1, 4 => 2, 9 => -1, 13 => 2, 27 => -1, 69 => 1],
  sparse![420; 2 => 1, 20 => 1, 59 => 1, 419 => 1],
  sparse![420; 2 => -2, 5 => 4, 11 => -1, 14 => 2, 29 => -1, 41 => 2, 83 => -1, 209 => 1],
  sparse![420; 0 => -3, 1 => 4, 2 => 4, 4 => 1, 5 => -3, 6 => 2, 9 => -1, 13 => -1, 14 => -1, 20 => -1, 29 => 1, 41 => 2],
  sparse![420; 0 => -3, 1 => 5, 2 => 2, 4 => 2, 5 => -2, 6 => 2, 9 => -2, 13 => -2, 14 => -1, 20 => -1, 29 => 1, 34 => -3, 41 => 1, 69 => 5, 104 => 2, 209 => -2],
  sparse![420; 0 => -2, 1 => 1, 2 => 4, 4 => 4, 5 => -2, 6 => 1, 9 => -2, 14 => -2, 20 => -1, 29 => 1, 34 => -1, 41 => 1, 69 => 1, 104 => 1],
  sparse![420; 0 => -2, 1 => 2, 2 => 1, 4 => 5, 5 => -1, 6 => 5, 9 => -3, 13 => -3, 14 => -2, 20 => -2, 29 => 2, 34 => -2, 41 => 2, 69 => 2, 104 => 1, 209 => -1],
  sparse![420; 0 => -2, 1 => 2, 2 => 3, 4 => 3, 5 => -2, 6 => 1, 9 => -2, 13 => -1, 14 => -2, 29 => 2, 41 => 1, 69 => 1, 104 => 1, 209 => -1],
  sparse![420; 0 => -2, 1 => 3, 2 => 1, 4 => 2, 5 => -1, 6 => 3, 9 => -1, 13 => -2, 20 => -1, 34 => -1, 41 => 1, 69 => 2],
  sparse![420; 0 => -2, 1 => 3, 2 => 2, 4 => 1, 5 => -1, 9 => -1, 69 => 1, 104 => -1, 209 => 2],
  sparse![420; 1 => -3, 3 => 4, 5 => 4, 9 => 1, 11 => -3, 13 => 2, 19 => -1, 27 => -1, 29 => -1, 41 => -1, 59 => 1, 83 => 2],
  sparse![420; 1 => -3, 3 => 5, 5 => 2, 9 => 2, 11 => -2, 13 => 2, 19 => -2, 27 => -2, 29 => -1, 41 => -1, 59 => 1, 69 => -3, 83 => 1, 139 => 5, 209 => 2, 419 => -2],
  sparse![420; 1 => -2, 3 => 1, 5 => 4, 9 => 4, 11 => -2, 13 => 1, 19 => -2, 29 => -2, 41 => -1, 59 => 1, 69 => -1, 83 => 1, 139 => 1, 209 => 1],
  sparse![420; 1 => -2, 3 => 2, 5 => 1, 9 => 5, 11 => -1, 13 => 5, 19 => -3, 27 => -3, 29 => -2, 41 => -2, 59 => 2, 69 => -2, 83 => 2, 139 => 2, 209 => 1, 419 => -1],
  sparse![420; 1 => -2, 3 => 2, 5 => 3, 9 => 3, 11 => -2, 13 => 1, 19 => -2, 27 => -1, 29 => -2, 59 => 2, 83 => 1, 139 => 1, 209 => 1, 419 => -1],
  sparse![420; 1 => -2, 3 => 3, 5 => 1, 9 => 2, 11 => -1, 13 => 3, 19 => -1, 27 => -2, 41 => -1, 69 => -1, 83 => 1, 139 => 2],
  sparse![420; 2 => 1, 4 => 1, 27 => 1, 419 => 1],
  sparse![420; 0 => 1, 4 => -1, 6 => -1, 9 => 2, 13 => 2, 19 => -1, 27 => -1, 34 => 1, 59 => 1, 83 => 1],
  sparse![420; 0 => 1, 2 => -1, 4 => 1, 5 => 1, 20 => 1, 209 => 1],
  sparse![420; 0 => -1, 1 => 1, 2 => 1, 6 => 1, 14 => 1, 69 => 1],
]
```

### Level 421

dim S₂ = **34**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **70**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 422

dim S₂ = **52**; eta rank = **2**; full eta basis = **NO**; Sturm bound B = **106**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![422; 0 => 3, 1 => -1, 210 => -1, 421 => 3],
  sparse![422; 0 => -1, 1 => 3, 210 => 3, 421 => -1],
]
```

### Level 423

dim S₂ = **45**; eta rank = **7**; full eta basis = **NO**; Sturm bound B = **96**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![423; 0 => 2, 46 => 2],
  sparse![423; 2 => 2, 140 => 2],
  sparse![423; 8 => 2, 422 => 2],
  sparse![423; 0 => 1, 2 => 1, 46 => 1, 140 => 1],
  sparse![423; 2 => 1, 8 => 1, 140 => 1, 422 => 1],
  sparse![423; 0 => 1, 8 => 1, 46 => 1, 422 => 1],
  sparse![423; 0 => -1, 2 => 4, 8 => -1, 46 => -1, 140 => 4, 422 => -1],
]
```

### Level 424

dim S₂ = **51**; eta rank = **10**; full eta basis = **NO**; Sturm bound B = **108**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![424; 1 => 2, 105 => 2],
  sparse![424; 3 => 2, 211 => 2],
  sparse![424; 1 => -1, 3 => 5, 7 => -2, 105 => 1, 211 => -1, 423 => 2],
  sparse![424; 0 => 1, 1 => -1, 3 => 3, 7 => -1, 52 => -1, 105 => 3, 211 => -1, 423 => 1],
  sparse![424; 0 => 2, 1 => -1, 3 => 1, 52 => -2, 105 => 5, 211 => -1],
  sparse![424; 0 => -1, 1 => 2, 3 => 2, 7 => -1, 52 => 1, 423 => 1],
  sparse![424; 0 => 1, 7 => 1, 52 => -1, 105 => 2, 211 => 2, 423 => -1],
  sparse![424; 1 => 1, 3 => -1, 7 => 2, 105 => -1, 211 => 5, 423 => -2],
  sparse![424; 0 => -1, 1 => 3, 3 => -1, 7 => 1, 52 => 1, 105 => -1, 211 => 3, 423 => -1],
  sparse![424; 0 => -2, 1 => 5, 3 => -1, 52 => 2, 105 => -1, 211 => 1],
]
```

### Level 425

dim S₂ = **39**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **90**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 426

dim S₂ = **69**; eta rank = **38**; full eta basis = **NO**; Sturm bound B = **144**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![426; 0 => 2, 70 => 2],
  sparse![426; 1 => 2, 141 => 2],
  sparse![426; 2 => 2, 212 => 2],
  sparse![426; 5 => 2, 425 => 2],
  sparse![426; 0 => -1, 1 => 3, 70 => -1, 141 => 3],
  sparse![426; 0 => 1, 1 => 1, 70 => 1, 141 => 1],
  sparse![426; 0 => 3, 1 => -1, 70 => 3, 141 => -1],
  sparse![426; 2 => -1, 5 => 3, 212 => -1, 425 => 3],
  sparse![426; 2 => 1, 5 => 1, 212 => 1, 425 => 1],
  sparse![426; 2 => 3, 5 => -1, 212 => 3, 425 => -1],
  sparse![426; 0 => 1, 2 => 1, 70 => 1, 212 => 1],
  sparse![426; 1 => 1, 5 => 1, 141 => 1, 425 => 1],
  sparse![426; 0 => 1, 1 => -1, 2 => -2, 5 => 4, 70 => 1, 141 => -1, 212 => -2, 425 => 4],
  sparse![426; 0 => 1, 1 => -1, 2 => -1, 5 => 3, 70 => 1, 141 => -1, 212 => -1, 425 => 3],
  sparse![426; 0 => -1, 1 => 1, 2 => 2, 70 => -1, 141 => 1, 212 => 2],
  sparse![426; 0 => 1, 1 => -1, 5 => 2, 70 => 1, 141 => -1, 425 => 2],
  sparse![426; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 70 => -1, 141 => 1, 212 => 3, 425 => -1],
  sparse![426; 0 => -1, 1 => 1, 2 => 4, 5 => -2, 70 => -1, 141 => 1, 212 => 4, 425 => -2],
  sparse![426; 0 => -1, 1 => 2, 5 => 1, 70 => -1, 141 => 2, 425 => 1],
  sparse![426; 1 => 1, 2 => -1, 5 => 2, 141 => 1, 212 => -1, 425 => 2],
  sparse![426; 0 => -1, 1 => 2, 2 => 1, 70 => -1, 141 => 2, 212 => 1],
  sparse![426; 0 => 1, 2 => -1, 5 => 2, 70 => 1, 212 => -1, 425 => 2],
  sparse![426; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 70 => -2, 141 => 3, 212 => 3, 425 => -2],
  sparse![426; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 70 => -1, 141 => 2, 212 => 2, 425 => -1],
  sparse![426; 1 => 1, 2 => 1, 141 => 1, 212 => 1],
  sparse![426; 0 => 1, 5 => 1, 70 => 1, 425 => 1],
  sparse![426; 0 => 2, 1 => -1, 2 => -1, 5 => 2, 70 => 2, 141 => -1, 212 => -1, 425 => 2],
  sparse![426; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 70 => 3, 141 => -2, 212 => -2, 425 => 3],
  sparse![426; 1 => 1, 2 => 2, 5 => -1, 141 => 1, 212 => 2, 425 => -1],
  sparse![426; 0 => 2, 1 => -1, 5 => 1, 70 => 2, 141 => -1, 425 => 1],
  sparse![426; 0 => 1, 2 => 2, 5 => -1, 70 => 1, 212 => 2, 425 => -1],
  sparse![426; 0 => 2, 1 => -1, 2 => 1, 70 => 2, 141 => -1, 212 => 1],
  sparse![426; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 70 => -2, 141 => 4, 212 => 1, 425 => -1],
  sparse![426; 0 => -1, 1 => 3, 2 => 1, 5 => -1, 70 => -1, 141 => 3, 212 => 1, 425 => -1],
  sparse![426; 1 => 2, 2 => 1, 5 => -1, 141 => 2, 212 => 1, 425 => -1],
  sparse![426; 0 => 2, 2 => -1, 5 => 1, 70 => 2, 212 => -1, 425 => 1],
  sparse![426; 0 => 3, 1 => -1, 2 => -1, 5 => 1, 70 => 3, 141 => -1, 212 => -1, 425 => 1],
  sparse![426; 0 => 4, 1 => -2, 2 => -1, 5 => 1, 70 => 4, 141 => -2, 212 => -1, 425 => 1],
]
```

### Level 427

dim S₂ = **39**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **82**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 428

dim S₂ = **52**; eta rank = **4**; full eta basis = **NO**; Sturm bound B = **108**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![428; 0 => 2, 106 => 2],
  sparse![428; 1 => 2, 213 => 2],
  sparse![428; 3 => 2, 427 => 2],
  sparse![428; 0 => -2, 1 => 6, 3 => -2, 106 => -2, 213 => 6, 427 => -2],
]
```

### Level 429

dim S₂ = **53**; eta rank = **18**; full eta basis = **NO**; Sturm bound B = **112**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![429; 0 => 2, 10 => 2],
  sparse![429; 2 => 2, 32 => 2],
  sparse![429; 12 => 2, 142 => 2],
  sparse![429; 38 => 2, 428 => 2],
  sparse![429; 0 => 1, 2 => 1, 10 => 1, 32 => 1],
  sparse![429; 12 => 1, 38 => 1, 142 => 1, 428 => 1],
  sparse![429; 0 => 2, 142 => 2],
  sparse![429; 0 => 1, 10 => 1, 12 => 1, 142 => 1],
  sparse![429; 10 => 2, 12 => 2],
  sparse![429; 2 => 2, 428 => 2],
  sparse![429; 2 => 1, 32 => 1, 38 => 1, 428 => 1],
  sparse![429; 32 => 2, 38 => 2],
  sparse![429; 0 => 1, 2 => 1, 142 => 1, 428 => 1],
  sparse![429; 0 => 1, 10 => 1, 38 => 1, 428 => 1],
  sparse![429; 2 => 1, 10 => 1, 12 => 1, 428 => 1],
  sparse![429; 0 => 1, 32 => 1, 38 => 1, 142 => 1],
  sparse![429; 2 => 1, 12 => 1, 32 => 1, 142 => 1],
  sparse![429; 10 => 1, 12 => 1, 32 => 1, 38 => 1],
]
```

### Level 430

dim S₂ = **63**; eta rank = **32**; full eta basis = **NO**; Sturm bound B = **132**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![430; 0 => 3, 1 => -1, 42 => -1, 85 => 3],
  sparse![430; 0 => -1, 1 => 3, 42 => 3, 85 => -1],
  sparse![430; 4 => 3, 9 => -1, 214 => -1, 429 => 3],
  sparse![430; 4 => -1, 9 => 3, 214 => 3, 429 => -1],
  sparse![430; 0 => 2, 214 => 2],
  sparse![430; 0 => 1, 4 => 1, 42 => 1, 214 => 1],
  sparse![430; 4 => 2, 42 => 2],
  sparse![430; 1 => 2, 429 => 2],
  sparse![430; 1 => 1, 9 => 1, 85 => 1, 429 => 1],
  sparse![430; 9 => 2, 85 => 2],
  sparse![430; 0 => 3, 1 => -1, 42 => 4, 85 => -2, 214 => -1, 429 => 1],
  sparse![430; 0 => 4, 1 => -2, 4 => -1, 9 => 1, 42 => 3, 85 => -1],
  sparse![430; 0 => -2, 1 => 4, 4 => 1, 9 => -1, 42 => 4, 85 => -2, 214 => -1, 429 => 1],
  sparse![430; 0 => 4, 1 => -2, 4 => -1, 9 => 1, 42 => -2, 85 => 4, 214 => 1, 429 => -1],
  sparse![430; 0 => 1, 1 => 1, 214 => 1, 429 => 1],
  sparse![430; 0 => -1, 1 => 2, 4 => 2, 9 => -1, 42 => 2, 85 => -1, 214 => -1, 429 => 2],
  sparse![430; 1 => 1, 4 => 2, 9 => -1, 42 => 2, 85 => -1, 429 => 1],
  sparse![430; 0 => 1, 4 => 2, 9 => -1, 42 => 2, 85 => -1, 214 => 1],
  sparse![430; 0 => -1, 1 => 2, 4 => 1, 42 => 1, 214 => -1, 429 => 2],
  sparse![430; 1 => 1, 4 => 1, 42 => 1, 429 => 1],
  sparse![430; 0 => 2, 1 => -1, 4 => 1, 42 => 1, 214 => 2, 429 => -1],
  sparse![430; 0 => -1, 1 => 2, 9 => 1, 85 => 1, 214 => -1, 429 => 2],
  sparse![430; 0 => 1, 9 => 1, 85 => 1, 214 => 1],
  sparse![430; 0 => 2, 1 => -1, 9 => 1, 85 => 1, 214 => 2, 429 => -1],
  sparse![430; 1 => 1, 4 => -1, 9 => 2, 42 => -1, 85 => 2, 429 => 1],
  sparse![430; 0 => 1, 4 => -1, 9 => 2, 42 => -1, 85 => 2, 214 => 1],
  sparse![430; 0 => 2, 1 => -1, 4 => -1, 9 => 2, 42 => -1, 85 => 2, 214 => 2, 429 => -1],
  sparse![430; 4 => 1, 9 => 1, 42 => 1, 85 => 1],
  sparse![430; 0 => -1, 1 => 3, 4 => 1, 9 => -1, 42 => 1, 85 => -1, 214 => -1, 429 => 3],
  sparse![430; 0 => 3, 1 => -1, 4 => -1, 9 => 1, 42 => -1, 85 => 1, 214 => 3, 429 => -1],
  sparse![430; 0 => -1, 1 => 1, 4 => 3, 9 => -1, 42 => 3, 85 => -1, 214 => -1, 429 => 1],
  sparse![430; 0 => 1, 1 => -1, 4 => -1, 9 => 3, 42 => -1, 85 => 3, 214 => 1, 429 => -1],
]
```

### Level 431

dim S₂ = **36**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **72**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![431; 0 => 2, 430 => 2],
]
```

### Level 432

dim S₂ = **55**; eta rank = **55**; full eta basis = **YES**; Sturm bound B = **144**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![432; 1 => 1, 3 => 1, 5 => 1, 11 => 1],
  sparse![432; 3 => 1, 7 => 1, 11 => 1, 23 => 1],
  sparse![432; 5 => 1, 11 => 1, 17 => 1, 35 => 1],
  sparse![432; 11 => 1, 23 => 1, 35 => 1, 71 => 1],
  sparse![432; 17 => 1, 35 => 1, 53 => 1, 107 => 1],
  sparse![432; 35 => 1, 71 => 1, 107 => 1, 215 => 1],
  sparse![432; 2 => 2, 8 => 2],
  sparse![432; 5 => 2, 17 => 2],
  sparse![432; 11 => 2, 35 => 2],
  sparse![432; 23 => 2, 71 => 2],
  sparse![432; 47 => 2, 143 => 2],
  sparse![432; 5 => 4],
  sparse![432; 11 => 4],
  sparse![432; 17 => 4],
  sparse![432; 23 => 4],
  sparse![432; 35 => 4],
  sparse![432; 71 => 4],
  sparse![432; 0 => -2, 1 => 4, 2 => 2, 5 => -2, 11 => 2],
  sparse![432; 2 => -2, 5 => 4, 8 => 2, 17 => -2, 35 => 2],
  sparse![432; 8 => -2, 17 => 4, 26 => 2, 53 => -2, 107 => 2],
  sparse![432; 0 => -1, 1 => 2, 5 => 2, 8 => 1],
  sparse![432; 0 => -1, 1 => 2, 2 => 1, 17 => 1, 26 => 2, 53 => -1],
  sparse![432; 1 => -1, 3 => 2, 11 => 2, 17 => 1],
  sparse![432; 1 => -1, 3 => 2, 5 => 1, 35 => 1, 53 => 2, 107 => -1],
  sparse![432; 3 => -1, 7 => 2, 23 => 2, 35 => 1],
  sparse![432; 3 => -1, 7 => 2, 11 => 1, 71 => 1, 107 => 2, 215 => -1],
  sparse![432; 7 => -1, 15 => 2, 47 => 2, 71 => 1],
  sparse![432; 7 => -1, 15 => 2, 23 => 1, 143 => 1, 215 => 2, 431 => -1],
  sparse![432; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -1, 11 => 2],
  sparse![432; 1 => -3, 3 => 7, 5 => 1, 7 => -2, 11 => -1, 23 => 2],
  sparse![432; 2 => -3, 5 => 7, 8 => 1, 11 => -2, 17 => -1, 35 => 2],
  sparse![432; 5 => -3, 11 => 7, 17 => 1, 23 => -2, 35 => -1, 71 => 2],
  sparse![432; 1 => 3, 17 => 1],
  sparse![432; 3 => 3, 35 => 1],
  sparse![432; 7 => 3, 71 => 1],
  sparse![432; 0 => -4, 1 => 10, 3 => -4, 11 => 2],
  sparse![432; 0 => -3, 1 => 6, 2 => 1, 3 => 1, 5 => -2, 7 => -2, 11 => 1, 23 => 2],
  sparse![432; 2 => -4, 5 => 10, 11 => -4, 35 => 2],
  sparse![432; 2 => -3, 5 => 6, 8 => 1, 11 => 1, 17 => -2, 23 => -2, 35 => 1, 71 => 2],
  sparse![432; 0 => -6, 1 => 13, 2 => 5, 3 => -5, 5 => -6, 8 => -1, 11 => 3, 17 => 1],
  sparse![432; 0 => -6, 1 => 15, 2 => 2, 3 => -6, 5 => -5, 11 => 3, 35 => 1],
  sparse![432; 0 => -3, 1 => 5, 2 => 1, 3 => 3, 7 => -2, 11 => -2, 17 => -1, 23 => 1, 35 => 3, 71 => -1],
  sparse![432; 0 => -3, 1 => 6, 2 => 2, 3 => -1, 5 => -1, 7 => -1, 8 => 1, 11 => -1, 17 => -1, 23 => 2, 35 => 2, 71 => -1],
  sparse![432; 1 => -6, 3 => 13, 5 => 5, 7 => -5, 11 => -6, 17 => -1, 23 => 3, 35 => 1],
  sparse![432; 1 => -6, 3 => 15, 5 => 2, 7 => -6, 11 => -5, 23 => 3, 71 => 1],
  sparse![432; 1 => -3, 3 => 5, 5 => 1, 7 => 3, 15 => -2, 23 => -2, 35 => -1, 47 => 1, 71 => 3, 143 => -1],
  sparse![432; 1 => -3, 3 => 6, 5 => 2, 7 => -1, 11 => -1, 15 => -1, 17 => 1, 23 => -1, 35 => -1, 47 => 2, 71 => 2, 143 => -1],
  sparse![432; 1 => 2, 3 => -1, 5 => -1, 11 => 2, 17 => 3, 23 => -1, 35 => -2, 47 => 1, 53 => -2, 107 => 3, 215 => 1, 431 => -1],
  sparse![432; 2 => 1, 3 => -1, 5 => -1, 7 => 2, 11 => 2, 23 => -1, 26 => -1, 35 => -2, 53 => 1, 71 => 3, 107 => 3, 215 => -2],
  sparse![432; 2 => 1, 5 => -1, 8 => 1, 17 => 1, 35 => 2],
  sparse![432; 5 => 1, 17 => 1, 23 => 1, 71 => 1],
  sparse![432; 0 => 3, 2 => -1, 23 => 1, 71 => 1],
  sparse![432; 0 => 2, 1 => -1, 47 => 2, 71 => 1],
  sparse![432; 0 => 1, 1 => 1, 2 => 1, 5 => -1, 35 => 2],
  sparse![432; 0 => 1, 1 => 1, 2 => 1, 53 => -1, 107 => 2],
]
```

### Level 433

dim S₂ = **35**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **72**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 434

dim S₂ = **61**; eta rank = **20**; full eta basis = **NO**; Sturm bound B = **128**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![434; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![434; 30 => 1, 61 => 1, 216 => 1, 433 => 1],
  sparse![434; 0 => 1, 1 => 1, 30 => 1, 61 => 1],
  sparse![434; 6 => 1, 13 => 1, 216 => 1, 433 => 1],
  sparse![434; 0 => -1, 1 => 2, 6 => 2, 13 => -1, 30 => -1, 61 => 2, 216 => 2, 433 => -1],
  sparse![434; 0 => -1, 1 => 2, 6 => 1, 61 => 1, 216 => 2, 433 => -1],
  sparse![434; 0 => -1, 1 => 2, 13 => 1, 30 => 1, 216 => 2, 433 => -1],
  sparse![434; 0 => -1, 1 => 2, 6 => -1, 13 => 2, 30 => 2, 61 => -1, 216 => 2, 433 => -1],
  sparse![434; 1 => 1, 6 => 2, 13 => -1, 30 => -1, 61 => 2, 216 => 1],
  sparse![434; 1 => 1, 6 => 1, 61 => 1, 216 => 1],
  sparse![434; 1 => 1, 13 => 1, 30 => 1, 216 => 1],
  sparse![434; 1 => 1, 6 => -1, 13 => 2, 30 => 2, 61 => -1, 216 => 1],
  sparse![434; 0 => 1, 6 => 2, 13 => -1, 30 => -1, 61 => 2, 433 => 1],
  sparse![434; 0 => 1, 6 => 1, 61 => 1, 433 => 1],
  sparse![434; 0 => 1, 13 => 1, 30 => 1, 433 => 1],
  sparse![434; 0 => 1, 6 => -1, 13 => 2, 30 => 2, 61 => -1, 433 => 1],
  sparse![434; 0 => 2, 1 => -1, 6 => 2, 13 => -1, 30 => -1, 61 => 2, 216 => -1, 433 => 2],
  sparse![434; 0 => 2, 1 => -1, 6 => 1, 61 => 1, 216 => -1, 433 => 2],
  sparse![434; 0 => 2, 1 => -1, 13 => 1, 30 => 1, 216 => -1, 433 => 2],
  sparse![434; 0 => 2, 1 => -1, 6 => -1, 13 => 2, 30 => 2, 61 => -1, 216 => -1, 433 => 2],
]
```

### Level 435

dim S₂ = **57**; eta rank = **10**; full eta basis = **NO**; Sturm bound B = **120**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![435; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![435; 28 => 1, 86 => 1, 144 => 1, 434 => 1],
  sparse![435; 0 => 1, 2 => 1, 28 => 1, 86 => 1],
  sparse![435; 4 => 1, 14 => 1, 144 => 1, 434 => 1],
  sparse![435; 0 => -1, 2 => 2, 4 => 2, 14 => -1, 28 => 2, 86 => -1, 144 => -1, 434 => 2],
  sparse![435; 2 => 1, 4 => 1, 86 => 1, 144 => 1],
  sparse![435; 2 => 1, 14 => 1, 28 => 1, 144 => 1],
  sparse![435; 0 => 1, 4 => 1, 86 => 1, 434 => 1],
  sparse![435; 0 => 1, 14 => 1, 28 => 1, 434 => 1],
  sparse![435; 0 => 2, 2 => -1, 4 => -1, 14 => 2, 28 => -1, 86 => 2, 144 => 2, 434 => -1],
]
```

### Level 436

dim S₂ = **53**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **110**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 437

dim S₂ = **39**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **80**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![437; 0 => 2, 22 => 2],
  sparse![437; 18 => 2, 436 => 2],
  sparse![437; 0 => 1, 18 => 1, 22 => 1, 436 => 1],
]
```

### Level 438

dim S₂ = **71**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **148**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 439

dim S₂ = **36**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **73**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 440

dim S₂ = **65**; eta rank = **65**; full eta basis = **YES**; Sturm bound B = **144**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![440; 0 => 2, 10 => 2],
  sparse![440; 1 => 2, 21 => 2],
  sparse![440; 3 => 2, 43 => 2],
  sparse![440; 4 => 2, 54 => 2],
  sparse![440; 7 => 2, 87 => 2],
  sparse![440; 9 => 2, 109 => 2],
  sparse![440; 19 => 2, 219 => 2],
  sparse![440; 39 => 2, 439 => 2],
  sparse![440; 1 => 2, 9 => 2],
  sparse![440; 3 => 2, 19 => 2],
  sparse![440; 21 => 2, 109 => 2],
  sparse![440; 43 => 2, 219 => 2],
  sparse![440; 0 => -2, 1 => 5, 3 => -1, 4 => 2, 9 => -1, 19 => 1],
  sparse![440; 10 => -2, 21 => 5, 43 => -1, 54 => 2, 109 => -1, 219 => 1],
  sparse![440; 0 => 1, 4 => 1, 10 => 1, 54 => 1],
  sparse![440; 1 => 1, 9 => 1, 21 => 1, 109 => 1],
  sparse![440; 3 => 1, 19 => 1, 43 => 1, 219 => 1],
  sparse![440; 7 => 1, 39 => 1, 87 => 1, 439 => 1],
  sparse![440; 0 => 1, 3 => -1, 7 => 2, 10 => 1, 21 => -2, 43 => 5, 87 => -2],
  sparse![440; 1 => 1, 3 => 1, 21 => 1, 43 => 1],
  sparse![440; 0 => -2, 1 => 4, 3 => 1, 7 => -1, 10 => 2, 21 => -2, 43 => 3, 87 => -1],
  sparse![440; 0 => -2, 1 => 5, 3 => -2, 7 => 1, 10 => 2, 21 => -1, 87 => 1],
  sparse![440; 0 => -2, 1 => 5, 3 => -1, 10 => -2, 21 => 5, 43 => -1],
  sparse![440; 4 => 1, 19 => -1, 39 => 2, 54 => 1, 109 => -2, 219 => 5, 439 => -2],
  sparse![440; 9 => 1, 19 => 1, 109 => 1, 219 => 1],
  sparse![440; 4 => -2, 9 => 4, 19 => 1, 39 => -1, 54 => 2, 109 => -2, 219 => 3, 439 => -1],
  sparse![440; 4 => -2, 9 => 5, 19 => -2, 39 => 1, 54 => 2, 109 => -1, 439 => 1],
  sparse![440; 4 => -2, 9 => 5, 19 => -1, 54 => -2, 109 => 5, 219 => -1],
  sparse![440; 0 => 2, 1 => -1, 4 => -1, 9 => 2, 10 => -1, 21 => 2, 54 => 2, 109 => -1],
  sparse![440; 0 => -1, 1 => 2, 9 => 1, 10 => 1, 54 => 2, 109 => -1],
  sparse![440; 1 => 1, 4 => -1, 9 => 2, 10 => 2, 21 => -1, 54 => 1],
  sparse![440; 0 => -1, 1 => 2, 4 => 1, 10 => -1, 21 => 2, 54 => 1],
  sparse![440; 0 => 1, 4 => -1, 9 => 2, 10 => 1, 54 => -1, 109 => 2],
  sparse![440; 0 => 1, 1 => 1, 54 => 1, 109 => 1],
  sparse![440; 4 => 1, 9 => 1, 10 => 1, 21 => 1],
  sparse![440; 0 => 1, 1 => -1, 4 => -1, 9 => 3, 10 => -1, 21 => 3, 54 => 1, 109 => -1],
  sparse![440; 0 => 3, 1 => -1, 4 => -1, 9 => 1, 10 => -1, 21 => 1, 54 => 3, 109 => -1],
  sparse![440; 1 => 2, 3 => -1, 9 => -1, 19 => 2, 21 => -1, 43 => 2, 109 => 2, 219 => -1],
  sparse![440; 1 => -1, 3 => 2, 19 => 1, 21 => 1, 109 => 2, 219 => -1],
  sparse![440; 3 => 1, 9 => -1, 19 => 2, 21 => 2, 43 => -1, 109 => 1],
  sparse![440; 1 => -1, 3 => 2, 9 => 1, 21 => -1, 43 => 2, 109 => 1],
  sparse![440; 1 => 1, 9 => -1, 19 => 2, 21 => 1, 109 => -1, 219 => 2],
  sparse![440; 1 => 1, 3 => 1, 109 => 1, 219 => 1],
  sparse![440; 9 => 1, 19 => 1, 21 => 1, 43 => 1],
  sparse![440; 3 => 2, 7 => -1, 19 => -1, 39 => 2, 43 => -1, 87 => 2, 219 => 2, 439 => -1],
  sparse![440; 3 => -1, 7 => 2, 39 => 1, 43 => 1, 219 => 2, 439 => -1],
  sparse![440; 7 => 1, 19 => -1, 39 => 2, 43 => 2, 87 => -1, 219 => 1],
  sparse![440; 3 => -1, 7 => 2, 19 => 1, 43 => -1, 87 => 2, 219 => 1],
  sparse![440; 3 => 1, 19 => -1, 39 => 2, 43 => 1, 219 => -1, 439 => 2],
  sparse![440; 3 => 1, 7 => 1, 219 => 1, 439 => 1],
  sparse![440; 19 => 1, 39 => 1, 43 => 1, 87 => 1],
  sparse![440; 0 => 1, 1 => 1, 3 => -1, 9 => -1, 19 => 2, 21 => 1, 54 => 1, 109 => -1, 219 => 1],
  sparse![440; 0 => 1, 19 => 1, 43 => 1, 54 => 1],
  sparse![440; 1 => 1, 3 => 1, 7 => -1, 19 => -1, 39 => 2, 43 => 1, 109 => 1, 219 => -1, 439 => 1],
  sparse![440; 1 => 1, 39 => 1, 87 => 1, 109 => 1],
  sparse![440; 3 => 1, 9 => -1, 19 => 2, 43 => 1, 109 => -1, 219 => 2],
  sparse![440; 1 => -1, 3 => 2, 19 => 1, 21 => -1, 43 => 2, 219 => 1],
  sparse![440; 0 => -1, 1 => 2, 3 => -1, 4 => 1, 7 => 1, 9 => -2, 19 => 3, 21 => 1, 39 => -1, 109 => 1],
  sparse![440; 1 => 1, 9 => 2, 19 => -1, 21 => 1, 109 => 2, 219 => -1],
  sparse![440; 0 => 1, 1 => -1, 3 => 2, 4 => -1, 7 => -1, 9 => 3, 19 => -2, 39 => 1, 43 => 1, 219 => 1],
  sparse![440; 3 => 1, 9 => 1, 43 => 1, 109 => 1],
  sparse![440; 1 => -1, 3 => 1, 9 => 4, 19 => -2, 21 => 3, 43 => -1],
  sparse![440; 1 => 4, 3 => -2, 9 => -1, 19 => 1, 109 => 3, 219 => -1],
  sparse![440; 1 => 1, 3 => -1, 9 => -2, 19 => 4, 21 => -1, 43 => 3],
  sparse![440; 0 => -1, 1 => 2, 3 => 1, 4 => 1, 7 => -1, 43 => -1, 87 => 2, 439 => 1],
]
```

### Level 441

dim S₂ = **41**; eta rank = **13**; full eta basis = **NO**; Sturm bound B = **112**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![441; 2 => 2, 20 => 2],
  sparse![441; 0 => -1, 2 => 4, 6 => 1, 8 => -1, 62 => 1],
  sparse![441; 0 => 1, 6 => -1, 8 => 1, 20 => 4, 62 => -1],
  sparse![441; 20 => 2, 146 => 2],
  sparse![441; 6 => -1, 20 => 4, 48 => 1, 62 => -1, 440 => 1],
  sparse![441; 6 => 1, 48 => -1, 62 => 1, 146 => 4, 440 => -1],
  sparse![441; 0 => 1, 2 => -1, 6 => -1, 8 => 1, 20 => 4, 62 => -1, 146 => 1],
  sparse![441; 6 => -1, 8 => 1, 20 => 4, 48 => 1, 62 => -1],
  sparse![441; 0 => 1, 6 => -1, 20 => 4, 62 => -1, 440 => 1],
  sparse![441; 2 => 1, 6 => -1, 20 => 4, 48 => 1, 62 => -1, 146 => -1, 440 => 1],
  sparse![441; 2 => 1, 20 => 2, 146 => 1],
  sparse![441; 2 => 1, 6 => 1, 48 => -1, 62 => 1, 146 => 3, 440 => -1],
  sparse![441; 0 => -1, 2 => 3, 6 => 1, 8 => -1, 62 => 1, 146 => 1],
]
```

### Level 442

dim S₂ = **59**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **126**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 443

dim S₂ = **37**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **74**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![443; 0 => 2, 442 => 2],
]
```

### Level 444

dim S₂ = **71**; eta rank = **52**; full eta basis = **NO**; Sturm bound B = **152**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![444; 0 => 1, 2 => 2, 5 => -1, 73 => 1, 110 => -1, 221 => 2],
  sparse![444; 0 => 2, 1 => -1, 2 => 1, 36 => -1, 73 => 2, 221 => 1],
  sparse![444; 1 => 2, 2 => 1, 5 => -1, 36 => 1, 73 => -1, 221 => 2],
  sparse![444; 0 => 1, 1 => 1, 110 => 1, 221 => 1],
  sparse![444; 0 => 2, 2 => -1, 5 => 1, 36 => -1, 73 => 1, 110 => 2],
  sparse![444; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 36 => 3, 73 => -2, 110 => -2, 221 => 3],
  sparse![444; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 36 => 2, 73 => -1, 110 => -1, 221 => 2],
  sparse![444; 1 => 1, 2 => 1, 36 => 1, 221 => 1],
  sparse![444; 0 => 1, 5 => 1, 73 => 1, 110 => 1],
  sparse![444; 0 => 2, 1 => -1, 2 => -1, 5 => 2, 36 => -1, 73 => 2, 110 => 2, 221 => -1],
  sparse![444; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 36 => -2, 73 => 3, 110 => 3, 221 => -2],
  sparse![444; 0 => -1, 1 => 1, 2 => 2, 36 => 2, 110 => -1, 221 => 1],
  sparse![444; 2 => 1, 5 => 1, 36 => 1, 73 => 1],
  sparse![444; 0 => 1, 1 => -1, 5 => 2, 73 => 2, 110 => 1, 221 => -1],
  sparse![444; 1 => 1, 5 => 2, 11 => -1, 147 => 1, 221 => -1, 443 => 2],
  sparse![444; 1 => 2, 3 => -1, 5 => 1, 73 => -1, 147 => 2, 443 => 1],
  sparse![444; 3 => 2, 5 => 1, 11 => -1, 73 => 1, 147 => -1, 443 => 2],
  sparse![444; 1 => 1, 3 => 1, 221 => 1, 443 => 1],
  sparse![444; 1 => 2, 5 => -1, 11 => 1, 73 => -1, 147 => 1, 221 => 2],
  sparse![444; 1 => -2, 3 => 3, 5 => 3, 11 => -2, 73 => 3, 147 => -2, 221 => -2, 443 => 3],
  sparse![444; 1 => -1, 3 => 2, 5 => 2, 11 => -1, 73 => 2, 147 => -1, 221 => -1, 443 => 2],
  sparse![444; 3 => 1, 5 => 1, 73 => 1, 443 => 1],
  sparse![444; 1 => 1, 11 => 1, 147 => 1, 221 => 1],
  sparse![444; 1 => 2, 3 => -1, 5 => -1, 11 => 2, 73 => -1, 147 => 2, 221 => 2, 443 => -1],
  sparse![444; 1 => 3, 3 => -2, 5 => -2, 11 => 3, 73 => -2, 147 => 3, 221 => 3, 443 => -2],
  sparse![444; 1 => -1, 3 => 1, 5 => 2, 73 => 2, 221 => -1, 443 => 1],
  sparse![444; 5 => 1, 11 => 1, 73 => 1, 147 => 1],
  sparse![444; 1 => 1, 3 => -1, 11 => 2, 147 => 2, 221 => 1, 443 => -1],
  sparse![444; 0 => 1, 1 => -1, 3 => 1, 5 => 1, 36 => -2, 73 => 5, 110 => -1, 147 => -2, 221 => 3, 443 => -1],
  sparse![444; 1 => 1, 2 => 1, 5 => -1, 11 => 1, 36 => -1, 73 => 3, 110 => -2, 147 => -1, 221 => 5, 443 => -2],
  sparse![444; 0 => 1, 1 => -2, 2 => -1, 3 => 3, 5 => 3, 11 => -2, 36 => -1, 73 => 3, 110 => 1, 147 => -2, 221 => -2, 443 => 3],
  sparse![444; 0 => 1, 1 => -1, 2 => -1, 3 => 2, 5 => 2, 11 => -1, 36 => -1, 73 => 2, 110 => 1, 147 => -1, 221 => -1, 443 => 2],
  sparse![444; 0 => -1, 1 => 1, 2 => 1, 3 => 2, 11 => -1, 36 => 1, 110 => -1, 147 => -1, 221 => 1, 443 => 2],
  sparse![444; 0 => -1, 1 => 2, 2 => 1, 3 => 1, 5 => -1, 36 => 1, 73 => -1, 110 => -1, 221 => 2, 443 => 1],
  sparse![444; 0 => 1, 1 => -2, 2 => -1, 3 => 2, 5 => 3, 11 => -1, 36 => -1, 73 => 3, 110 => 1, 147 => -1, 221 => -2, 443 => 2],
  sparse![444; 0 => 1, 1 => -1, 2 => -1, 3 => 1, 5 => 2, 36 => -1, 73 => 2, 110 => 1, 221 => -1, 443 => 1],
  sparse![444; 0 => 1, 2 => -1, 5 => 1, 11 => 1, 36 => -1, 73 => 1, 110 => 1, 147 => 1],
  sparse![444; 0 => -1, 1 => 1, 2 => 1, 3 => 1, 36 => 1, 110 => -1, 221 => 1, 443 => 1],
  sparse![444; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 11 => 1, 36 => 1, 73 => -1, 110 => -1, 147 => 1, 221 => 2],
  sparse![444; 0 => -1, 1 => 3, 2 => 1, 3 => -1, 5 => -2, 11 => 2, 36 => 1, 73 => -2, 110 => -1, 147 => 2, 221 => 3, 443 => -1],
  sparse![444; 0 => 1, 1 => -1, 2 => -1, 5 => 2, 11 => 1, 36 => -1, 73 => 2, 110 => 1, 147 => 1, 221 => -1],
  sparse![444; 0 => 1, 2 => -1, 3 => -1, 5 => 1, 11 => 2, 36 => -1, 73 => 1, 110 => 1, 147 => 2, 443 => -1],
  sparse![444; 0 => 3, 1 => -2, 2 => -2, 3 => 1, 5 => 3, 11 => -1, 36 => -2, 73 => 3, 110 => 3, 147 => -1, 221 => -2, 443 => 1],
  sparse![444; 0 => 2, 1 => -1, 2 => -1, 3 => 1, 5 => 2, 11 => -1, 36 => -1, 73 => 2, 110 => 2, 147 => -1, 221 => -1, 443 => 1],
  sparse![444; 0 => 2, 1 => 1, 2 => -1, 3 => -1, 11 => 1, 36 => -1, 110 => 2, 147 => 1, 221 => 1, 443 => -1],
  sparse![444; 0 => 1, 1 => 2, 3 => -1, 5 => -1, 11 => 1, 73 => -1, 110 => 1, 147 => 1, 221 => 2, 443 => -1],
  sparse![444; 0 => 2, 1 => -2, 2 => -1, 3 => 1, 5 => 3, 11 => -1, 36 => -1, 73 => 3, 110 => 2, 147 => -1, 221 => -2, 443 => 1],
  sparse![444; 0 => 1, 1 => -1, 3 => 1, 5 => 2, 11 => -1, 73 => 2, 110 => 1, 147 => -1, 221 => -1, 443 => 1],
  sparse![444; 0 => -1, 2 => 2, 3 => 1, 5 => 1, 11 => -1, 36 => 2, 73 => 1, 110 => -1, 147 => -1, 443 => 1],
  sparse![444; 0 => -1, 1 => 5, 3 => -2, 5 => -1, 11 => 1, 73 => -1, 110 => -1, 147 => 1, 221 => 5, 443 => -2],
  sparse![444; 0 => -2, 1 => 7, 2 => 1, 3 => -3, 5 => -3, 11 => 2, 36 => 1, 73 => -3, 110 => -2, 147 => 2, 221 => 7, 443 => -3],
  sparse![444; 0 => 2, 1 => -3, 2 => -3, 3 => 1, 5 => 7, 11 => -2, 36 => -3, 73 => 7, 110 => 2, 147 => -2, 221 => -3, 443 => 1],
]
```

### Level 445

dim S₂ = **43**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **90**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 446

dim S₂ = **55**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **112**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![446; 0 => 1, 1 => 1, 222 => 1, 445 => 1],
]
```

### Level 447

dim S₂ = **49**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **100**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![447; 0 => 1, 2 => 1, 148 => 1, 446 => 1],
]
```

### Level 448

dim S₂ = **53**; eta rank = **53**; full eta basis = **YES**; Sturm bound B = **128**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![448; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![448; 1 => 1, 3 => 1, 13 => 1, 27 => 1],
  sparse![448; 3 => 1, 7 => 1, 27 => 1, 55 => 1],
  sparse![448; 7 => 1, 15 => 1, 55 => 1, 111 => 1],
  sparse![448; 15 => 1, 31 => 1, 111 => 1, 223 => 1],
  sparse![448; 31 => 1, 63 => 1, 223 => 1, 447 => 1],
  sparse![448; 3 => 2, 7 => 2],
  sparse![448; 7 => 2, 15 => 2],
  sparse![448; 27 => 2, 55 => 2],
  sparse![448; 55 => 2, 111 => 2],
  sparse![448; 0 => 1, 6 => 1, 7 => 1, 55 => 1],
  sparse![448; 1 => -1, 3 => 3, 13 => 3, 27 => -1],
  sparse![448; 1 => 1, 13 => 1, 15 => 1, 111 => 1],
  sparse![448; 3 => -1, 7 => 3, 27 => 3, 55 => -1],
  sparse![448; 3 => 1, 27 => 1, 31 => 1, 223 => 1],
  sparse![448; 7 => -1, 15 => 3, 55 => 3, 111 => -1],
  sparse![448; 7 => 1, 55 => 1, 63 => 1, 447 => 1],
  sparse![448; 15 => -1, 31 => 3, 111 => 3, 223 => -1],
  sparse![448; 0 => -2, 1 => 5, 3 => -2, 7 => 3],
  sparse![448; 6 => -2, 13 => 5, 27 => -2, 55 => 3],
  sparse![448; 0 => -3, 1 => 7, 3 => -2, 6 => 1, 13 => 1],
  sparse![448; 0 => -2, 1 => 4, 6 => 2, 13 => -2, 27 => 2],
  sparse![448; 0 => -2, 1 => 5, 3 => -2, 7 => 2, 15 => -1, 55 => 1, 111 => 1],
  sparse![448; 1 => -3, 3 => 7, 7 => -2, 13 => 1, 27 => 1],
  sparse![448; 1 => -2, 3 => 4, 13 => 2, 27 => -2, 55 => 2],
  sparse![448; 1 => -2, 3 => 5, 7 => -2, 15 => 2, 31 => -1, 111 => 1, 223 => 1],
  sparse![448; 3 => -3, 7 => 7, 15 => -2, 27 => 1, 55 => 1],
  sparse![448; 3 => -2, 7 => 4, 27 => 2, 55 => -2, 111 => 2],
  sparse![448; 3 => -2, 7 => 5, 15 => -2, 31 => 2, 63 => -1, 223 => 1, 447 => 1],
  sparse![448; 0 => -1, 3 => 5, 6 => 1, 7 => -2, 13 => -1, 27 => 1, 55 => -1, 111 => 2],
  sparse![448; 0 => 1, 1 => -1, 3 => 1, 6 => -1, 7 => -1, 15 => 2, 27 => 5, 55 => -2],
  sparse![448; 3 => -2, 7 => 5, 13 => 2, 27 => -1, 31 => -1, 55 => 1, 111 => -1, 223 => 1],
  sparse![448; 0 => 1, 6 => 1, 31 => 1, 223 => 1],
  sparse![448; 3 => 2, 55 => 2],
  sparse![448; 0 => -3, 1 => 7, 3 => -2, 6 => 1, 13 => -3, 27 => 6, 55 => -2],
  sparse![448; 1 => -1, 7 => 5, 13 => 1, 15 => -2, 27 => -1, 55 => 1, 111 => -1, 223 => 2],
  sparse![448; 1 => 1, 3 => -1, 7 => 1, 13 => -1, 15 => -1, 31 => 2, 55 => 5, 111 => -2],
  sparse![448; 7 => -2, 15 => 5, 27 => 2, 55 => -1, 63 => -1, 111 => 1, 223 => -1, 447 => 1],
  sparse![448; 1 => 1, 13 => 1, 63 => 1, 447 => 1],
  sparse![448; 7 => 2, 111 => 2],
  sparse![448; 1 => -3, 3 => 7, 7 => -2, 13 => 1, 27 => -3, 55 => 6, 111 => -2],
  sparse![448; 7 => 1, 15 => 1, 31 => 1, 63 => -1, 111 => 1, 447 => 1],
  sparse![448; 15 => 1, 55 => 1, 63 => 1, 111 => 1, 223 => 1, 447 => -1],
  sparse![448; 0 => -1, 1 => 1, 3 => 1, 6 => 1, 7 => 1, 27 => 1],
  sparse![448; 0 => 1, 3 => 1, 6 => -1, 13 => 1, 27 => 1, 55 => 1],
  sparse![448; 0 => 2, 13 => 1, 55 => 1],
  sparse![448; 1 => 1, 6 => 2, 7 => 1],
  sparse![448; 7 => 1, 31 => 1, 447 => 2],
  sparse![448; 55 => 1, 63 => 2, 223 => 1],
  sparse![448; 0 => 2, 3 => -1, 7 => 1, 13 => 1, 27 => 1],
  sparse![448; 0 => 2, 1 => -1, 7 => 1, 55 => 2],
  sparse![448; 0 => 1, 6 => 1, 7 => 2, 15 => -1, 111 => 1],
  sparse![448; 0 => 1, 6 => 1, 15 => 1, 55 => 2, 111 => -1],
]
```

### Level 449

dim S₂ = **37**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **75**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 450

dim S₂ = **67**; eta rank = **67**; full eta basis = **YES**; Sturm bound B = **180**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![450; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![450; 1 => 1, 5 => 1, 9 => 1, 29 => 1],
  sparse![450; 2 => 1, 8 => 1, 14 => 1, 44 => 1],
  sparse![450; 4 => 1, 14 => 1, 24 => 1, 74 => 1],
  sparse![450; 5 => 1, 17 => 1, 29 => 1, 89 => 1],
  sparse![450; 9 => 1, 29 => 1, 49 => 1, 149 => 1],
  sparse![450; 14 => 1, 44 => 1, 74 => 1, 224 => 1],
  sparse![450; 29 => 1, 89 => 1, 149 => 1, 449 => 1],
  sparse![450; 0 => 1, 1 => 1, 14 => 1, 29 => 1],
  sparse![450; 2 => 1, 5 => 1, 44 => 1, 89 => 1],
  sparse![450; 4 => 1, 9 => 1, 74 => 1, 149 => 1],
  sparse![450; 14 => 1, 29 => 1, 224 => 1, 449 => 1],
  sparse![450; 0 => 1, 4 => 1, 14 => 1, 74 => 1],
  sparse![450; 2 => 1, 4 => 1, 14 => 1, 24 => 1],
  sparse![450; 1 => 1, 9 => 1, 29 => 1, 149 => 1],
  sparse![450; 5 => 1, 9 => 1, 29 => 1, 49 => 1],
  sparse![450; 2 => 1, 14 => 1, 44 => 1, 224 => 1],
  sparse![450; 8 => 1, 14 => 1, 44 => 1, 74 => 1],
  sparse![450; 5 => 1, 29 => 1, 89 => 1, 449 => 1],
  sparse![450; 17 => 1, 29 => 1, 89 => 1, 149 => 1],
  sparse![450; 0 => -2, 1 => 1, 2 => 7, 5 => -3, 8 => -2, 14 => 1, 17 => 1, 29 => 1],
  sparse![450; 0 => -2, 1 => 3, 2 => 2, 4 => 1, 5 => -1, 14 => 1],
  sparse![450; 0 => -1, 1 => 1, 2 => 1, 4 => 1, 5 => 1, 8 => 1, 17 => -1, 89 => 1],
  sparse![450; 0 => -1, 1 => 2, 8 => 1, 14 => 3, 29 => -1, 44 => -1, 89 => 1],
  sparse![450; 0 => -1, 1 => 2, 5 => 1, 8 => 1, 17 => -1, 29 => 1, 89 => 1],
  sparse![450; 4 => -2, 9 => 1, 14 => 7, 29 => -3, 44 => -2, 74 => 1, 89 => 1, 149 => 1],
  sparse![450; 4 => -2, 9 => 3, 14 => 2, 24 => 1, 29 => -1, 74 => 1],
  sparse![450; 4 => -1, 9 => 1, 14 => 1, 24 => 1, 29 => 1, 44 => 1, 89 => -1, 449 => 1],
  sparse![450; 4 => -1, 9 => 2, 44 => 1, 74 => 3, 149 => -1, 224 => -1, 449 => 1],
  sparse![450; 4 => -1, 9 => 2, 29 => 1, 44 => 1, 89 => -1, 149 => 1, 449 => 1],
  sparse![450; 0 => 1, 14 => 1, 29 => 1, 49 => 1],
  sparse![450; 1 => 1, 14 => 1, 24 => 1, 29 => 1],
  sparse![450; 2 => 1, 4 => 1, 9 => 1, 149 => 1],
  sparse![450; 4 => 1, 5 => 1, 9 => 1, 74 => 1],
  sparse![450; 0 => -1, 1 => 1, 4 => 3, 9 => -1, 14 => 3, 29 => -1, 74 => -1, 149 => 1],
  sparse![450; 0 => -1, 1 => 1, 2 => 1, 4 => 1, 14 => 1, 24 => 2, 49 => -1],
  sparse![450; 0 => -1, 1 => 1, 2 => 1, 4 => 1, 9 => 1, 24 => 1, 49 => -1, 149 => 1],
  sparse![450; 0 => -1, 1 => 2, 14 => 1, 24 => 2, 29 => 1, 49 => -1],
  sparse![450; 0 => -1, 1 => 2, 9 => 1, 24 => 1, 29 => 1, 49 => -1, 149 => 1],
  sparse![450; 2 => 1, 44 => 1, 89 => 1, 149 => 1],
  sparse![450; 5 => 1, 44 => 1, 74 => 1, 89 => 1],
  sparse![450; 8 => 1, 14 => 1, 29 => 1, 449 => 1],
  sparse![450; 2 => -1, 5 => 1, 14 => 3, 29 => -1, 44 => 3, 89 => -1, 224 => -1, 449 => 1],
  sparse![450; 2 => -1, 5 => 1, 8 => 1, 14 => 1, 44 => 1, 74 => 2, 149 => -1],
  sparse![450; 2 => -1, 5 => 1, 8 => 1, 14 => 1, 29 => 1, 74 => 1, 149 => -1, 449 => 1],
  sparse![450; 2 => -1, 5 => 2, 44 => 1, 74 => 2, 89 => 1, 149 => -1],
  sparse![450; 0 => -1, 2 => 1, 4 => 4, 24 => -1, 74 => 1],
  sparse![450; 2 => 1, 8 => -1, 44 => 4, 74 => 1, 224 => -1],
  sparse![450; 0 => 1, 2 => -1, 4 => -1, 8 => 1, 14 => 4, 24 => 1, 44 => -1, 74 => -1, 224 => 1],
  sparse![450; 1 => -1, 5 => 1, 9 => 4, 49 => -1, 149 => 1],
  sparse![450; 5 => 1, 17 => -1, 89 => 4, 149 => 1, 449 => -1],
  sparse![450; 1 => 1, 5 => -1, 9 => -1, 17 => 1, 29 => 4, 49 => 1, 89 => -1, 149 => -1, 449 => 1],
  sparse![450; 0 => 1, 1 => -1, 5 => 1, 9 => 1, 14 => 2, 29 => -1, 44 => -1, 74 => -1, 89 => 1, 149 => 1, 224 => 1],
  sparse![450; 0 => -1, 1 => 1, 2 => 1, 4 => 1, 14 => -1, 29 => 2, 44 => 1, 74 => 1, 89 => -1, 149 => -1, 449 => 1],
  sparse![450; 4 => -1, 5 => 1, 8 => 1, 9 => 1, 14 => 2, 17 => -1, 24 => 1, 29 => -1, 74 => -1, 89 => 1, 149 => 1],
  sparse![450; 2 => -1, 5 => 1, 8 => 1, 9 => 1, 14 => 2, 24 => 1, 29 => -1, 44 => -1, 49 => -1, 89 => 1, 149 => 1],
  sparse![450; 0 => 2, 1 => -1, 14 => 3, 29 => -1, 44 => -1, 74 => -1, 89 => 1, 149 => 1, 224 => 1],
  sparse![450; 0 => -1, 1 => 2, 14 => -1, 29 => 3, 44 => 1, 74 => 1, 89 => -1, 149 => -1, 449 => 1],
  sparse![450; 4 => -1, 8 => 2, 9 => 1, 14 => 3, 17 => -1, 24 => 1, 29 => -1, 74 => -1, 149 => 1],
  sparse![450; 0 => 2, 1 => -1, 4 => -1, 9 => 2, 29 => 1, 74 => 1],
  sparse![450; 0 => 2, 1 => -1, 14 => 1, 29 => 1, 224 => -1, 449 => 2],
  sparse![450; 0 => 2, 1 => -1, 29 => 1, 44 => -1, 74 => 1, 89 => 2],
  sparse![450; 0 => 1, 1 => -1, 2 => 1, 4 => -1, 9 => 2, 24 => 1, 29 => 1],
  sparse![450; 0 => 1, 1 => -1, 2 => 1, 9 => 2, 24 => 1, 49 => -1, 74 => 1],
  sparse![450; 0 => 1, 1 => -1, 2 => -1, 4 => 2, 5 => 2, 149 => 1],
  sparse![450; 0 => 1, 4 => 2, 49 => -1, 74 => -1, 149 => 3],
  sparse![450; 0 => -1, 1 => 1, 4 => 2, 5 => 1, 9 => -1, 14 => 1, 49 => 1],
]
```

### Level 451

dim S₂ = **41**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **84**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![451; 0 => 2, 10 => 2],
  sparse![451; 40 => 2, 450 => 2],
  sparse![451; 0 => 1, 10 => 1, 40 => 1, 450 => 1],
]
```

### Level 452

dim S₂ = **55**; eta rank = **7**; full eta basis = **NO**; Sturm bound B = **114**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![452; 0 => 2, 1 => -1, 3 => 1, 112 => -2, 225 => 5, 451 => -1],
  sparse![452; 0 => 1, 1 => -1, 3 => 2, 112 => -1, 225 => 5, 451 => -2],
  sparse![452; 0 => 1, 1 => 2, 3 => -1, 112 => -1, 225 => 2, 451 => 1],
  sparse![452; 1 => 2, 225 => 2],
  sparse![452; 0 => -1, 1 => 2, 3 => 1, 112 => 1, 225 => 2, 451 => -1],
  sparse![452; 0 => -1, 1 => 5, 3 => -2, 112 => 1, 225 => -1, 451 => 2],
  sparse![452; 0 => -2, 1 => 5, 3 => -1, 112 => 2, 225 => -1, 451 => 1],
]
```

### Level 453

dim S₂ = **49**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **101**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 454

dim S₂ = **56**; eta rank = **2**; full eta basis = **NO**; Sturm bound B = **114**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![454; 0 => 2, 226 => 2],
  sparse![454; 1 => 2, 453 => 2],
]
```

### Level 455

dim S₂ = **53**; eta rank = **18**; full eta basis = **NO**; Sturm bound B = **112**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![455; 0 => 2, 34 => 2],
  sparse![455; 0 => 1, 4 => 1, 6 => 1, 34 => 1],
  sparse![455; 4 => 2, 6 => 2],
  sparse![455; 12 => 2, 454 => 2],
  sparse![455; 12 => 1, 64 => 1, 90 => 1, 454 => 1],
  sparse![455; 64 => 2, 90 => 2],
  sparse![455; 0 => 2, 454 => 2],
  sparse![455; 0 => 1, 4 => 1, 90 => 1, 454 => 1],
  sparse![455; 4 => 2, 90 => 2],
  sparse![455; 0 => 1, 6 => 1, 64 => 1, 454 => 1],
  sparse![455; 0 => 1, 12 => 1, 34 => 1, 454 => 1],
  sparse![455; 4 => 1, 6 => 1, 12 => 1, 454 => 1],
  sparse![455; 0 => 1, 34 => 1, 64 => 1, 90 => 1],
  sparse![455; 4 => 1, 6 => 1, 64 => 1, 90 => 1],
  sparse![455; 4 => 1, 12 => 1, 34 => 1, 90 => 1],
  sparse![455; 6 => 2, 64 => 2],
  sparse![455; 6 => 1, 12 => 1, 34 => 1, 64 => 1],
  sparse![455; 12 => 2, 34 => 2],
]
```

### Level 456

dim S₂ = **73**; eta rank = **73**; full eta basis = **YES**; Sturm bound B = **160**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![456; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 11 => 1, 56 => 1, 227 => 1],
  sparse![456; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -2, 11 => 1, 37 => -2, 75 => 7, 113 => 1, 151 => -3, 227 => -2, 455 => 1],
  sparse![456; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -2, 11 => 1, 113 => 3, 227 => -1],
  sparse![456; 0 => -3, 1 => 7, 2 => 2, 3 => -3, 5 => -4, 11 => 4, 23 => -1, 56 => 1, 75 => -2, 113 => -1, 151 => 3, 227 => 3, 455 => -2],
  sparse![456; 0 => -3, 1 => 7, 2 => 2, 3 => -3, 5 => -3, 11 => 1, 23 => 1, 37 => -3, 56 => 1, 75 => 7, 113 => 1, 151 => -3, 227 => -3, 455 => 2],
  sparse![456; 0 => -3, 1 => 7, 2 => 2, 3 => -3, 5 => -3, 11 => 2, 18 => -1, 37 => 3, 75 => -1, 113 => 1],
  sparse![456; 0 => -3, 1 => 8, 3 => -3, 18 => 1, 75 => 1],
  sparse![456; 0 => -3, 1 => 8, 2 => 1, 3 => -3, 5 => -3, 11 => 2, 37 => -3, 75 => 8, 113 => 2, 151 => -3, 227 => -3, 455 => 1],
  sparse![456; 0 => -3, 1 => 8, 2 => 1, 3 => -3, 5 => -3, 11 => 2, 37 => -1, 75 => 1, 113 => 4, 227 => -2],
  sparse![456; 0 => -3, 1 => 8, 2 => 2, 3 => -3, 5 => -3, 11 => 1, 18 => -1, 37 => 3],
  sparse![456; 0 => -2, 1 => 2, 2 => 3, 3 => 2, 5 => -2, 7 => -1, 18 => -1, 37 => 2, 75 => 2, 151 => -2, 227 => -2, 455 => 3],
  sparse![456; 0 => -2, 1 => 3, 2 => 1, 3 => 2, 5 => -1, 7 => -1, 18 => -2, 37 => 4, 56 => 1, 75 => 1, 113 => -2, 151 => -1, 227 => 1],
  sparse![456; 0 => -2, 1 => 3, 2 => 1, 3 => 2, 5 => -1, 7 => -1, 18 => -1, 37 => 2, 56 => 2, 75 => -1, 113 => -2, 227 => 1, 455 => 1],
  sparse![456; 0 => -2, 1 => 3, 2 => 2, 3 => 1, 5 => -3, 7 => -1, 11 => 3, 18 => 2, 23 => -1, 37 => -2, 56 => -2, 113 => 4, 151 => 1, 227 => -2, 455 => 1],
  sparse![456; 0 => -2, 1 => 3, 2 => 2, 3 => 1, 5 => -2, 7 => -1, 18 => 2, 23 => 1, 37 => -3, 56 => -2, 75 => 3, 113 => 4, 151 => -1, 227 => -2, 455 => 1],
  sparse![456; 0 => -2, 1 => 3, 2 => 2, 3 => 1, 5 => -2, 7 => -1, 11 => 1, 75 => -1, 113 => 1, 151 => 2, 227 => 1, 455 => -1],
  sparse![456; 0 => -2, 1 => 3, 2 => 2, 3 => 1, 5 => -1, 7 => -1, 11 => -1, 23 => 1, 37 => 1, 75 => -1, 113 => -1, 151 => 1, 227 => 3, 455 => -1],
  sparse![456; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -2, 7 => 1, 18 => -1, 37 => 4, 75 => -4, 113 => -3, 151 => 2, 227 => 7, 455 => -3],
  sparse![456; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -1, 56 => 1, 227 => 1],
  sparse![456; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 37 => 1, 56 => 1],
  sparse![456; 0 => -2, 1 => 4, 3 => -1, 5 => 2, 11 => -1, 18 => 1, 56 => -1, 113 => 2],
  sparse![456; 0 => -2, 1 => 4, 3 => 1, 7 => -1, 18 => 1, 56 => -1, 75 => -2, 151 => 1, 227 => 5, 455 => -2],
  sparse![456; 0 => -2, 1 => 4, 2 => 1, 3 => -1, 5 => -1, 7 => 1, 18 => -2, 37 => 5, 56 => 1, 75 => -2, 113 => -2, 151 => 1, 227 => 1],
  sparse![456; 0 => -2, 1 => 4, 2 => 1, 3 => -1, 5 => -1, 7 => 1, 18 => -1, 37 => 2, 56 => 2, 75 => -1, 113 => -3, 227 => 4, 455 => -1],
  sparse![456; 0 => -2, 1 => 4, 2 => 1, 3 => -1, 56 => -1, 75 => 1, 113 => 4, 227 => -2],
  sparse![456; 0 => -2, 1 => 4, 2 => 1, 5 => -2, 7 => -1, 11 => 1, 18 => 1, 23 => 1, 75 => -1, 151 => 1, 227 => 2, 455 => -1],
  sparse![456; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 7 => -1, 11 => -1, 18 => -2, 23 => 2, 37 => 5, 56 => 1, 75 => -1, 113 => -2, 151 => -1, 455 => 2],
  sparse![456; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 7 => -1, 11 => -1, 18 => -1, 23 => 2, 56 => 2, 75 => 4, 113 => -1, 151 => -2, 227 => -1, 455 => 1],
  sparse![456; 0 => -2, 1 => 4, 2 => 1, 3 => 1, 5 => -2, 7 => -1, 11 => 1, 18 => -2, 37 => 3, 56 => 1, 75 => 2, 113 => -1, 151 => -1],
  sparse![456; 0 => -2, 1 => 4, 2 => 1, 3 => 1, 5 => -2, 7 => -1, 11 => 1, 18 => -1, 37 => 1, 56 => 2, 113 => -1, 455 => 1],
  sparse![456; 0 => -2, 1 => 4, 2 => 2, 3 => -2, 5 => -3, 7 => 1, 11 => 3, 18 => 2, 23 => -1, 37 => -2, 56 => -2, 113 => 3, 151 => 1, 227 => 1, 455 => -1],
  sparse![456; 0 => -2, 1 => 4, 2 => 2, 3 => -2, 5 => -2, 7 => 1, 18 => 2, 23 => 1, 37 => -3, 56 => -2, 75 => 3, 113 => 3, 151 => -1, 227 => 1, 455 => -1],
  sparse![456; 0 => -2, 1 => 4, 2 => 2, 3 => -2, 5 => -2, 7 => 1, 11 => 1, 37 => -2, 75 => 5, 113 => 2, 151 => -2, 227 => -2, 455 => 1],
  sparse![456; 0 => -2, 1 => 4, 2 => 2, 3 => -2, 5 => -2, 7 => 1, 11 => 2, 23 => -1, 75 => 2, 151 => -1, 455 => 1],
  sparse![456; 0 => -2, 1 => 4, 2 => 2, 3 => -1, 5 => -3, 11 => 3, 23 => -1, 37 => 1, 75 => 1, 151 => -1, 227 => -1, 455 => 2],
  sparse![456; 0 => -2, 1 => 4, 2 => 2, 3 => -1, 5 => -2, 23 => 1, 37 => 2, 75 => -2, 113 => -2, 151 => 1, 227 => 5, 455 => -2],
  sparse![456; 0 => -2, 1 => 4, 2 => 2, 3 => -1, 5 => -1, 18 => -1, 37 => 3, 56 => -1, 75 => -1, 113 => 2],
  sparse![456; 0 => -2, 1 => 4, 2 => 2, 3 => -1, 5 => -1, 37 => -1, 75 => 4, 151 => -2, 227 => -1, 455 => 2],
  sparse![456; 0 => -2, 1 => 4, 2 => 2, 5 => -2, 7 => -1, 23 => 1, 151 => 1, 227 => 2, 455 => -1],
  sparse![456; 0 => -2, 1 => 5, 2 => -1, 3 => -2, 5 => 3, 11 => -1, 18 => 2, 37 => -1, 56 => -1, 113 => 1, 227 => 1],
  sparse![456; 0 => -2, 1 => 5, 3 => -2, 5 => -1, 11 => 3, 18 => -1, 23 => -1, 37 => 2, 56 => 1, 113 => -2, 227 => 3, 455 => -1],
  sparse![456; 0 => -2, 1 => 5, 3 => -2, 18 => -1, 23 => 1, 37 => 2, 56 => 1, 113 => -1, 455 => 1],
  sparse![456; 0 => -2, 1 => 5, 3 => -2, 7 => 1, 18 => 1, 37 => -1, 56 => -1, 75 => 1, 113 => 2, 151 => -1, 227 => -1, 455 => 2],
  sparse![456; 0 => -2, 1 => 5, 3 => -2, 5 => 1, 18 => 1, 37 => -1, 56 => -1, 75 => 1, 113 => 3, 227 => -1],
  sparse![456; 0 => -2, 1 => 5, 3 => -1, 7 => -1, 11 => -1, 18 => 1, 23 => 2, 37 => -1, 56 => -1, 113 => 2, 151 => 1],
  sparse![456; 0 => -2, 1 => 5, 2 => 1, 3 => -3, 5 => -3, 7 => 1, 11 => 4, 18 => 1, 23 => -1, 37 => -1, 75 => 2, 113 => 1, 151 => -1, 227 => -1, 455 => 1],
  sparse![456; 0 => -2, 1 => 5, 2 => 1, 3 => -3, 5 => -3, 7 => 1, 11 => 5, 18 => -2, 23 => -2, 37 => 6, 56 => 1, 75 => -4, 113 => -4, 151 => 1, 227 => 6, 455 => -2],
  sparse![456; 0 => -2, 1 => 5, 2 => 1, 3 => -3, 5 => -3, 7 => 1, 11 => 5, 18 => -1, 23 => -2, 37 => 2, 56 => 2, 75 => -2, 113 => -2, 151 => 2, 227 => 2, 455 => -1],
  sparse![456; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 5 => -4, 11 => 6, 23 => -2, 56 => -1, 75 => 2, 113 => 3, 151 => -1, 227 => -2, 455 => 1],
  sparse![456; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 5 => -2, 23 => 2, 37 => 1, 56 => -1, 75 => -1, 113 => 2, 151 => 1, 227 => 1, 455 => -1],
  sparse![456; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 5 => -2, 11 => 2, 18 => 1, 37 => -2, 75 => 4, 113 => 1, 151 => -2, 227 => -2, 455 => 2],
  sparse![456; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 5 => -2, 11 => 3, 23 => -1, 37 => -2, 56 => -1, 75 => 5, 113 => 3, 151 => -2, 227 => -2, 455 => 1],
  sparse![456; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 5 => -2, 7 => 1, 11 => 1, 18 => -2, 37 => 4, 56 => 1, 75 => -1, 113 => -1, 151 => 1],
  sparse![456; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 37 => 2, 56 => -1, 75 => -1, 113 => 1, 227 => 1],
  sparse![456; 0 => -2, 1 => 5, 2 => 1, 3 => -1, 5 => -2, 7 => -1, 18 => -2, 23 => 2, 37 => 4, 56 => 1, 113 => -1, 151 => -1, 227 => -1, 455 => 2],
  sparse![456; 0 => -2, 1 => 5, 2 => 1, 3 => -1, 5 => -2, 7 => -1, 18 => -1, 23 => 2, 37 => -1, 56 => 2, 75 => 5, 151 => -2, 227 => -2, 455 => 1],
  sparse![456; 0 => -2, 1 => 5, 2 => 1, 5 => -2, 7 => -1, 23 => 1, 56 => -1, 113 => 1, 227 => 4, 455 => -2],
  sparse![456; 0 => -2, 1 => 5, 2 => 2, 3 => -2, 5 => -2, 11 => 1, 37 => -2, 75 => 5, 113 => 1, 151 => -2, 227 => -2, 455 => 2],
  sparse![456; 0 => -1, 1 => -1, 2 => 2, 3 => 5, 5 => -1, 7 => -2, 18 => 1, 75 => -1, 151 => 1, 227 => 2, 455 => -1],
  sparse![456; 0 => -1, 1 => -1, 2 => 2, 3 => 5, 7 => -2, 11 => -2, 18 => -2, 23 => 1, 37 => 5, 56 => 1, 75 => -1, 113 => -2, 151 => -1, 455 => 2],
  sparse![456; 0 => -1, 1 => -1, 2 => 2, 3 => 5, 7 => -2, 11 => -2, 18 => -1, 23 => 1, 56 => 2, 75 => 4, 113 => -1, 151 => -2, 227 => -1, 455 => 1],
  sparse![456; 0 => -1, 2 => 1, 3 => 3, 5 => 1, 7 => -1, 11 => -2, 18 => 1, 23 => 1, 37 => 1, 56 => -1, 75 => -2, 151 => 1, 227 => 3, 455 => -1],
  sparse![456; 0 => -1, 2 => 1, 3 => 3, 5 => 1, 7 => -1, 11 => -1, 18 => -1, 37 => 2, 56 => 1, 113 => -1, 455 => 1],
  sparse![456; 0 => -1, 2 => 1, 3 => 4, 7 => -2, 11 => -2, 18 => 1, 23 => 2, 56 => -1, 113 => 2],
  sparse![456; 0 => -1, 2 => 1, 3 => 4, 5 => 1, 7 => -2, 11 => -2, 18 => 1, 23 => 1, 37 => -1, 56 => -1, 113 => 2, 151 => 1],
  sparse![456; 0 => -1, 2 => 1, 3 => 5, 7 => -2, 11 => -2, 23 => 1, 56 => -2, 113 => 4, 227 => 1, 455 => -1],
  sparse![456; 0 => -1, 2 => 2, 3 => 2, 7 => -1, 11 => -1, 18 => 1, 23 => 1, 75 => -1, 151 => 2],
  sparse![456; 0 => -1, 2 => 2, 3 => 2, 7 => -1, 56 => -1, 113 => 2, 151 => 2, 455 => -1],
  sparse![456; 0 => -1, 2 => 2, 3 => 3, 5 => -1, 7 => -1, 11 => -1, 23 => 1, 37 => 1, 56 => -1, 75 => -1, 113 => 2, 151 => 1, 227 => 1, 455 => -1],
  sparse![456; 0 => -1, 2 => 3, 3 => 1, 5 => -1, 37 => -2, 75 => 7, 113 => 1, 151 => -3, 227 => -2, 455 => 1],
  sparse![456; 0 => -1, 2 => 3, 3 => 1, 5 => -1, 113 => 3, 227 => -1],
  sparse![456; 1 => -4, 3 => 10, 5 => 1, 7 => -4, 11 => -2, 23 => 1, 113 => 1, 455 => 1],
  sparse![456; 1 => -3, 2 => -1, 3 => 7, 5 => 4, 7 => -3, 11 => -4, 18 => 3, 23 => 2, 37 => -2, 56 => -2, 113 => 3, 227 => -1, 455 => 1],
]
```

### Level 457

dim S₂ = **37**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **76**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 458

dim S₂ = **56**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **115**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 459

dim S₂ = **49**; eta rank = **14**; full eta basis = **NO**; Sturm bound B = **108**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![459; 2 => 2, 8 => 2],
  sparse![459; 50 => 2, 152 => 2],
  sparse![459; 0 => 1, 2 => 1, 16 => 1, 50 => 1],
  sparse![459; 2 => 1, 8 => 1, 50 => 1, 152 => 1],
  sparse![459; 8 => 1, 26 => 1, 152 => 1, 458 => 1],
  sparse![459; 0 => -1, 2 => 3, 16 => 2, 50 => -1, 152 => 1],
  sparse![459; 2 => 1, 8 => -1, 26 => 2, 152 => 3, 458 => -1],
  sparse![459; 0 => 1, 16 => 1, 26 => 1, 458 => 1],
  sparse![459; 2 => -1, 8 => 3, 50 => 3, 152 => -1],
  sparse![459; 8 => 2, 50 => 2],
  sparse![459; 2 => 2, 152 => 2],
  sparse![459; 2 => 3, 8 => -1, 50 => -1, 152 => 3],
  sparse![459; 8 => 3, 26 => -1, 50 => 1, 152 => -1, 458 => 2],
  sparse![459; 0 => 2, 2 => -1, 8 => 1, 16 => -1, 50 => 3],
]
```

### Level 460

dim S₂ = **67**; eta rank = **66**; full eta basis = **NO**; Sturm bound B = **144**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![460; 1 => 2, 9 => 2],
  sparse![460; 45 => 2, 229 => 2],
  sparse![460; 0 => 2, 22 => 2],
  sparse![460; 1 => 2, 45 => 2],
  sparse![460; 3 => 2, 91 => 2],
  sparse![460; 4 => 2, 114 => 2],
  sparse![460; 9 => 2, 229 => 2],
  sparse![460; 19 => 2, 459 => 2],
  sparse![460; 0 => -1, 1 => 3, 22 => -1, 45 => 3],
  sparse![460; 0 => 1, 1 => 1, 22 => 1, 45 => 1],
  sparse![460; 0 => 3, 1 => -1, 22 => 3, 45 => -1],
  sparse![460; 1 => -1, 3 => 3, 45 => -1, 91 => 3],
  sparse![460; 1 => 1, 3 => 1, 45 => 1, 91 => 1],
  sparse![460; 4 => -1, 9 => 3, 114 => -1, 229 => 3],
  sparse![460; 4 => 1, 9 => 1, 114 => 1, 229 => 1],
  sparse![460; 4 => 3, 9 => -1, 114 => 3, 229 => -1],
  sparse![460; 9 => -1, 19 => 3, 229 => -1, 459 => 3],
  sparse![460; 9 => 1, 19 => 1, 229 => 1, 459 => 1],
  sparse![460; 0 => 1, 1 => -1, 3 => 2, 22 => 1, 45 => -1, 91 => 2],
  sparse![460; 4 => 1, 9 => -1, 19 => 2, 114 => 1, 229 => -1, 459 => 2],
  sparse![460; 0 => 1, 4 => 1, 22 => 1, 114 => 1],
  sparse![460; 1 => 1, 9 => 1, 45 => 1, 229 => 1],
  sparse![460; 3 => 1, 19 => 1, 91 => 1, 459 => 1],
  sparse![460; 0 => -2, 1 => 4, 4 => 1, 9 => -1, 22 => 3, 45 => -1],
  sparse![460; 0 => -1, 1 => 3, 22 => 4, 45 => -2, 114 => -1, 229 => 1],
  sparse![460; 0 => -1, 1 => 1, 4 => 3, 9 => -1, 22 => 3, 45 => -1, 114 => -1, 229 => 1],
  sparse![460; 4 => 3, 9 => -1, 22 => 4, 45 => -2, 114 => -1, 229 => 1],
  sparse![460; 0 => -2, 1 => 4, 4 => 1, 9 => -1, 114 => -1, 229 => 3],
  sparse![460; 0 => -1, 1 => 3, 4 => 1, 9 => -1, 22 => 1, 45 => -1, 114 => -1, 229 => 3],
  sparse![460; 0 => -1, 1 => 2, 9 => 1, 22 => -1, 45 => 2, 229 => 1],
  sparse![460; 0 => -1, 1 => 2, 4 => 1, 22 => -1, 45 => 2, 114 => 1],
  sparse![460; 0 => -1, 1 => 2, 4 => 2, 9 => -1, 22 => -1, 45 => 2, 114 => 2, 229 => -1],
  sparse![460; 1 => 1, 4 => -1, 9 => 2, 45 => 1, 114 => -1, 229 => 2],
  sparse![460; 1 => 1, 4 => 1, 45 => 1, 114 => 1],
  sparse![460; 1 => 1, 4 => 2, 9 => -1, 45 => 1, 114 => 2, 229 => -1],
  sparse![460; 0 => 1, 4 => -1, 9 => 2, 22 => 1, 114 => -1, 229 => 2],
  sparse![460; 0 => 1, 9 => 1, 22 => 1, 229 => 1],
  sparse![460; 0 => 1, 4 => 2, 9 => -1, 22 => 1, 114 => 2, 229 => -1],
  sparse![460; 0 => 2, 1 => -1, 4 => -1, 9 => 2, 22 => 2, 45 => -1, 114 => -1, 229 => 2],
  sparse![460; 0 => 2, 1 => -1, 9 => 1, 22 => 2, 45 => -1, 229 => 1],
  sparse![460; 0 => 2, 1 => -1, 4 => 1, 22 => 2, 45 => -1, 114 => 1],
  sparse![460; 0 => 1, 1 => -1, 4 => -1, 9 => 3, 22 => -1, 45 => 3, 114 => 1, 229 => -1],
  sparse![460; 1 => -2, 3 => 4, 9 => 1, 19 => -1, 45 => 3, 91 => -1],
  sparse![460; 1 => -1, 3 => 3, 45 => 4, 91 => -2, 229 => -1, 459 => 1],
  sparse![460; 1 => -1, 3 => 1, 9 => 3, 19 => -1, 45 => 3, 91 => -1, 229 => -1, 459 => 1],
  sparse![460; 9 => 3, 19 => -1, 45 => 4, 91 => -2, 229 => -1, 459 => 1],
  sparse![460; 1 => -2, 3 => 4, 9 => 1, 19 => -1, 229 => -1, 459 => 3],
  sparse![460; 1 => -1, 3 => 3, 9 => 1, 19 => -1, 45 => 1, 91 => -1, 229 => -1, 459 => 3],
  sparse![460; 1 => -1, 3 => 2, 19 => 1, 45 => -1, 91 => 2, 459 => 1],
  sparse![460; 1 => -1, 3 => 2, 9 => 1, 45 => -1, 91 => 2, 229 => 1],
  sparse![460; 1 => -1, 3 => 2, 9 => 2, 19 => -1, 45 => -1, 91 => 2, 229 => 2, 459 => -1],
  sparse![460; 3 => 1, 9 => -1, 19 => 2, 91 => 1, 229 => -1, 459 => 2],
  sparse![460; 3 => 1, 9 => 1, 91 => 1, 229 => 1],
  sparse![460; 3 => 1, 9 => 2, 19 => -1, 91 => 1, 229 => 2, 459 => -1],
  sparse![460; 1 => 1, 9 => -1, 19 => 2, 45 => 1, 229 => -1, 459 => 2],
  sparse![460; 1 => 2, 3 => -1, 9 => -1, 19 => 2, 45 => 2, 91 => -1, 229 => -1, 459 => 2],
  sparse![460; 0 => -1, 1 => 1, 3 => 1, 4 => 2, 9 => -1, 22 => 1, 45 => 1, 91 => -1, 229 => -1, 459 => 2],
  sparse![460; 0 => -1, 1 => 1, 3 => 1, 4 => 1, 9 => 1, 19 => -1, 22 => 1, 45 => 1, 91 => -1, 114 => -1, 229 => 1, 459 => 1],
  sparse![460; 0 => -1, 1 => 1, 3 => 1, 4 => 2, 9 => -1, 22 => -2, 45 => 5, 91 => -2, 114 => -1, 229 => 3, 459 => -1],
  sparse![460; 1 => -1, 3 => 2, 4 => 2, 9 => -1, 22 => -1, 45 => 3, 91 => -1, 114 => -1, 229 => 3, 459 => -1],
  sparse![460; 1 => -1, 3 => 2, 4 => 1, 9 => 1, 19 => -1, 22 => -1, 45 => 3, 91 => -1, 114 => -2, 229 => 5, 459 => -2],
  sparse![460; 3 => 1, 9 => -1, 19 => 2, 22 => 2, 45 => -1, 114 => -2, 229 => 4, 459 => -1],
  sparse![460; 1 => -1, 3 => 2, 19 => 1, 22 => 2, 45 => -2, 91 => 1, 114 => -2, 229 => 5, 459 => -2],
  sparse![460; 1 => -1, 3 => 2, 4 => -1, 9 => 4, 19 => -2, 22 => -2, 45 => 5, 91 => -2, 114 => 1, 229 => -2, 459 => 2],
  sparse![460; 0 => -2, 1 => 5, 3 => -2, 19 => 1, 22 => -2, 45 => 5, 91 => -2, 459 => 1],
  sparse![460; 0 => 1, 19 => 1, 22 => 1, 459 => 1],
]
```

### Level 461

dim S₂ = **38**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **77**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 462

dim S₂ = **89**; eta rank = **89**; full eta basis = **YES**; Sturm bound B = **192**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![462; 0 => -2, 1 => 3, 2 => 1, 5 => -1, 6 => 3, 10 => 2, 13 => -2, 20 => -1, 21 => -1, 32 => -1, 41 => 1, 65 => 1, 76 => -1, 153 => 2, 230 => 1, 461 => -1],
  sparse![462; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 6 => 4, 13 => -2, 20 => -1, 41 => 1],
  sparse![462; 0 => -1, 1 => 1, 2 => 1, 10 => 2, 20 => 2, 21 => -1, 41 => -1, 76 => 1, 230 => -1, 461 => 1],
  sparse![462; 0 => -1, 1 => 1, 2 => 1, 6 => 1, 10 => 2, 13 => -1, 21 => -1, 32 => -1, 41 => 1, 65 => 1, 76 => -1, 153 => 2, 230 => 1, 461 => -1],
  sparse![462; 0 => -1, 1 => 1, 2 => 1, 6 => 2, 10 => -1, 13 => -1, 21 => 1, 32 => 1, 76 => 2, 153 => -1],
  sparse![462; 0 => -1, 1 => 1, 2 => 1, 6 => 2, 13 => -1, 20 => -1, 41 => 1, 65 => 1, 76 => 1],
  sparse![462; 0 => -1, 1 => 1, 2 => 1, 6 => 2, 13 => -1, 32 => 2, 65 => -1, 76 => 1, 230 => -1, 461 => 1],
  sparse![462; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 6 => -1, 13 => 1, 20 => 2, 32 => 2, 41 => -1, 65 => -1, 76 => 1, 153 => -1, 230 => -1, 461 => 2],
  sparse![462; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 6 => -1, 13 => 2, 20 => 1, 41 => -1, 65 => 1, 76 => 1],
  sparse![462; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 6 => -1, 10 => 1, 13 => 1, 20 => 2, 21 => -1, 32 => -1, 41 => -1, 65 => 2, 230 => 2, 461 => -1],
  sparse![462; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 6 => -1, 10 => 1, 13 => 2, 21 => -1, 32 => -1, 65 => 2, 153 => 1],
  sparse![462; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 10 => -1, 21 => 2, 32 => 1, 41 => 1, 65 => -1, 76 => 1],
  sparse![462; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 10 => -1, 20 => 1, 21 => 1, 32 => 2, 65 => -1, 230 => 1],
  sparse![462; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 20 => -1, 21 => 1, 41 => 2, 153 => 1],
  sparse![462; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 13 => 1, 65 => 1, 76 => 2, 153 => -1, 230 => -1, 461 => 1],
  sparse![462; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 13 => 1, 32 => 1, 76 => -1, 153 => 2, 230 => 1, 461 => -1],
  sparse![462; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 10 => 1, 20 => -1, 21 => -1, 32 => -1, 41 => 2, 65 => 2, 76 => 1, 153 => -1, 230 => -1, 461 => 2],
  sparse![462; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 10 => 1, 20 => 1, 76 => 2, 153 => -1, 230 => -1, 461 => 1],
  sparse![462; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 6 => 1, 10 => -1, 13 => -1, 20 => -1, 21 => 2, 32 => 1, 41 => 2, 65 => -1, 76 => 2, 153 => -1, 230 => -1, 461 => 1],
  sparse![462; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 6 => 1, 10 => -1, 21 => 1, 32 => 2, 65 => -1, 76 => 1],
  sparse![462; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 6 => 1, 13 => -1, 20 => -1, 32 => 1, 41 => 2, 461 => 1],
  sparse![462; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 6 => 1, 20 => -1, 32 => 1, 41 => 1, 153 => 1],
  sparse![462; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 6 => 1, 10 => 1, 13 => -1, 20 => -1, 21 => -1, 32 => -2, 41 => 2, 65 => 3, 76 => -1, 153 => 1, 230 => 3, 461 => -2],
  sparse![462; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 6 => 2, 10 => -1, 13 => -1, 20 => -1, 21 => 1, 32 => 2, 41 => 1, 65 => -1, 76 => 2, 153 => -1, 230 => -1, 461 => 1],
  sparse![462; 0 => -1, 1 => 1, 2 => 3, 5 => -2, 6 => 1, 10 => 1, 13 => -1, 20 => -2, 21 => -1, 32 => -1, 41 => 3, 65 => 2, 76 => -1, 153 => 1, 230 => 2, 461 => -1],
  sparse![462; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 10 => -1, 21 => 1, 32 => 3, 65 => -1],
  sparse![462; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 76 => 3, 153 => -1, 230 => -1, 461 => 1],
  sparse![462; 0 => -1, 1 => 1, 2 => 4, 5 => -2, 6 => 1, 13 => -1, 20 => -2, 41 => 4],
  sparse![462; 0 => -1, 1 => 2, 6 => -1, 13 => 1, 20 => 2, 21 => 1, 41 => -1, 76 => 1, 153 => -1, 230 => -1, 461 => 2],
  sparse![462; 0 => -1, 1 => 2, 6 => -1, 13 => 2, 32 => 2, 65 => -1, 230 => 2, 461 => -1],
  sparse![462; 0 => -1, 1 => 2, 6 => -1, 10 => 2, 13 => 2, 21 => -1, 76 => 2, 153 => -1],
  sparse![462; 0 => -1, 1 => 2, 10 => -1, 20 => 1, 21 => 2, 230 => 1],
  sparse![462; 0 => -1, 1 => 2, 10 => 1, 13 => 1, 20 => 1, 21 => -1, 41 => -1, 65 => 1, 230 => -1, 461 => 2],
  sparse![462; 0 => -1, 1 => 2, 10 => 2, 20 => 2, 21 => -1, 41 => -1, 230 => -1, 461 => 2],
  sparse![462; 0 => -1, 1 => 2, 6 => 1, 10 => -1, 13 => -1, 21 => 2, 41 => 1, 76 => 1, 153 => -1, 461 => 1],
  sparse![462; 0 => -1, 1 => 2, 6 => 1, 10 => -1, 21 => 2, 76 => 1],
  sparse![462; 0 => -1, 1 => 2, 6 => 1, 13 => -1, 21 => 1, 32 => 1, 41 => 1, 65 => -1, 230 => -1, 461 => 2],
  sparse![462; 0 => -1, 1 => 2, 6 => 2, 10 => -1, 13 => -1, 20 => -1, 21 => 2, 32 => 1, 41 => 1, 65 => -1, 76 => -1, 153 => 2, 230 => 1, 461 => -1],
  sparse![462; 0 => -1, 1 => 2, 6 => 2, 13 => -1, 20 => -1, 41 => 1, 65 => 1, 461 => 1],
  sparse![462; 0 => -1, 1 => 2, 6 => 2, 13 => -1, 32 => 2, 65 => -1, 230 => -1, 461 => 2],
  sparse![462; 0 => -1, 1 => 2, 6 => 2, 10 => 1, 13 => -1, 21 => -1, 32 => -1, 65 => 2, 76 => -1, 153 => 1, 230 => 2, 461 => -1],
  sparse![462; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 6 => -1, 10 => -1, 13 => 2, 20 => 1, 21 => 2, 41 => -1, 76 => 2, 153 => -1, 230 => -1, 461 => 1],
  sparse![462; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 6 => -1, 13 => 2, 20 => 1, 41 => -1, 65 => 1, 461 => 1],
  sparse![462; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 6 => -1, 10 => 1, 13 => 1, 20 => 2, 41 => -1, 461 => 1],
  sparse![462; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 10 => -1, 21 => 2, 32 => 1, 41 => 1, 65 => -1, 461 => 1],
  sparse![462; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 10 => -1, 13 => 1, 21 => 2, 32 => 1, 65 => -1, 153 => 1],
  sparse![462; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 20 => 1, 21 => 1, 76 => -1, 153 => 1, 230 => 2, 461 => -1],
  sparse![462; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 13 => 1, 65 => 1, 76 => 1, 153 => -1, 230 => -1, 461 => 2],
  sparse![462; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 10 => 1, 20 => 1, 76 => 1, 153 => -1, 230 => -1, 461 => 2],
  sparse![462; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 10 => 2, 21 => -1, 32 => -1, 41 => 1, 65 => 1, 230 => -1, 461 => 2],
  sparse![462; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 10 => 2, 20 => 2, 21 => -1, 32 => -1, 41 => -1, 65 => 1, 230 => 1],
  sparse![462; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 6 => 1, 10 => -1, 13 => -1, 20 => -1, 21 => 2, 32 => 1, 41 => 2, 65 => -1, 76 => 1, 153 => -1, 230 => -1, 461 => 2],
  sparse![462; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 6 => 1, 10 => -1, 21 => 1, 32 => 2, 65 => -1, 461 => 1],
  sparse![462; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 6 => 1, 13 => -1, 21 => 1, 41 => 1, 230 => 1],
  sparse![462; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 6 => 2, 10 => -1, 13 => -1, 20 => -1, 21 => 1, 32 => 2, 41 => 1, 65 => -1, 76 => 1, 153 => -1, 230 => -1, 461 => 2],
  sparse![462; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 6 => 2, 13 => -1, 20 => -1, 32 => -1, 41 => 1, 65 => 2, 230 => 2, 461 => -1],
  sparse![462; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 6 => 2, 13 => -1, 32 => 1, 230 => 1],
  sparse![462; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 6 => 2, 10 => 1, 13 => -1, 20 => -1, 21 => -1, 41 => 1, 65 => 1, 76 => -1, 153 => 1, 230 => 1],
  sparse![462; 0 => -1, 1 => 2, 2 => 1, 10 => -1, 21 => 2, 32 => 1],
  sparse![462; 0 => -1, 1 => 2, 2 => 1, 6 => 2, 13 => -1, 41 => 1],
  sparse![462; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 6 => -1, 13 => 2, 20 => 2, 41 => -1],
  sparse![462; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 76 => 2, 153 => -1, 230 => -1, 461 => 2],
  sparse![462; 0 => -1, 1 => 3, 2 => 1, 5 => -1, 10 => -1, 21 => 3, 32 => 1, 65 => -1],
  sparse![462; 0 => -1, 1 => 3, 2 => 1, 5 => -1, 76 => 1, 153 => -1, 230 => -1, 461 => 3],
  sparse![462; 2 => -1, 5 => 2, 6 => -1, 13 => 1, 20 => 2, 21 => 1, 41 => -1, 153 => 1],
  sparse![462; 2 => -1, 5 => 2, 6 => -1, 10 => 1, 13 => 1, 20 => 2, 21 => -1, 32 => -1, 41 => -1, 65 => 2, 76 => 1, 153 => -1, 230 => -1, 461 => 2],
  sparse![462; 2 => -1, 5 => 2, 10 => -1, 20 => 2, 21 => 2, 32 => 1, 41 => -1, 65 => -1, 76 => 2, 153 => -1, 230 => -1, 461 => 1],
  sparse![462; 2 => -1, 5 => 2, 20 => -1, 32 => 2, 41 => 2, 65 => -1, 230 => 2, 461 => -1],
  sparse![462; 2 => -1, 5 => 2, 20 => 1, 32 => -1, 65 => 2, 230 => 1],
  sparse![462; 2 => -1, 5 => 2, 20 => 2, 32 => 1, 41 => -1, 461 => 1],
  sparse![462; 2 => -1, 5 => 2, 13 => 1, 20 => 1, 32 => -1, 41 => -1, 65 => 2, 153 => 1, 230 => 1, 461 => -1],
  sparse![462; 2 => -1, 5 => 2, 10 => 1, 13 => 1, 20 => 1, 21 => -1, 41 => -1, 65 => 1, 76 => -1, 153 => 2],
  sparse![462; 2 => -1, 5 => 2, 10 => 2, 20 => -1, 21 => -1, 41 => 2, 76 => 2, 153 => -1],
  sparse![462; 2 => -1, 5 => 2, 6 => 1, 13 => -1, 21 => 1, 32 => 1, 41 => 1, 65 => -1, 76 => -1, 153 => 2],
  sparse![462; 2 => -1, 5 => 2, 6 => 1, 32 => -1, 65 => 2, 76 => 1],
  sparse![462; 2 => -1, 5 => 2, 6 => 2, 13 => -1, 20 => -1, 41 => 1, 65 => 1, 76 => -1, 153 => 2, 230 => 1, 461 => -1],
  sparse![462; 2 => -1, 5 => 2, 6 => 2, 13 => -1, 32 => 2, 65 => -1, 76 => -1, 153 => 2],
  sparse![462; 6 => -1, 13 => 1, 20 => 3, 41 => -1, 76 => -1, 153 => 1, 230 => 3, 461 => -1],
  sparse![462; 6 => -1, 13 => 2, 20 => 1, 76 => -1, 153 => 2, 230 => 1],
  sparse![462; 6 => -1, 13 => 3, 20 => 1, 41 => -1, 76 => -1, 153 => 3, 230 => 1, 461 => -1],
  sparse![462; 6 => -1, 10 => 1, 13 => 3, 20 => 1, 21 => -1, 32 => -1, 41 => -1, 65 => 3],
  sparse![462; 6 => -1, 10 => 2, 13 => 2, 20 => 2, 21 => -1, 32 => -1, 41 => -1, 65 => 2],
  sparse![462; 6 => -1, 10 => 3, 13 => 1, 20 => 3, 21 => -1, 32 => -1, 41 => -1, 65 => 1],
  sparse![462; 10 => -2, 21 => 4, 32 => 1, 65 => -1, 76 => 4, 153 => -2, 230 => -1, 461 => 1],
  sparse![462; 10 => -1, 21 => 1, 32 => 4, 65 => -2, 76 => 1, 153 => -1, 230 => -2, 461 => 4],
  sparse![462; 10 => -1, 21 => 2, 32 => 1, 76 => 2, 153 => -1, 461 => 1],
  sparse![462; 10 => -1, 21 => 2, 32 => 2, 65 => -1, 76 => -1, 153 => 2, 230 => 2, 461 => -1],
  sparse![462; 41 => 2, 461 => 2],
  sparse![462; 32 => 1, 65 => 1, 230 => 1, 461 => 1],
]
```

### Level 463

dim S₂ = **38**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **77**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 464

dim S₂ = **55**; eta rank = **37**; full eta basis = **NO**; Sturm bound B = **120**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![464; 1 => 2, 57 => 2],
  sparse![464; 3 => 2, 115 => 2],
  sparse![464; 7 => 2, 231 => 2],
  sparse![464; 1 => -1, 3 => 5, 7 => -2, 57 => 1, 115 => -1, 231 => 2],
  sparse![464; 0 => 1, 1 => -1, 3 => 3, 7 => -1, 28 => -1, 57 => 3, 115 => -1, 231 => 1],
  sparse![464; 0 => -1, 1 => 2, 3 => 2, 7 => -1, 28 => 1, 231 => 1],
  sparse![464; 0 => 2, 1 => -1, 3 => 1, 28 => -2, 57 => 5, 115 => -1],
  sparse![464; 0 => 1, 7 => 1, 28 => -1, 57 => 2, 115 => 2, 231 => -1],
  sparse![464; 1 => 1, 3 => -1, 7 => 2, 57 => -1, 115 => 5, 231 => -2],
  sparse![464; 0 => -1, 1 => 3, 3 => -1, 7 => 1, 28 => 1, 57 => -1, 115 => 3, 231 => -1],
  sparse![464; 0 => -2, 1 => 5, 3 => -1, 28 => 2, 57 => -1, 115 => 1],
  sparse![464; 3 => -1, 7 => 5, 15 => -2, 115 => 1, 231 => -1, 463 => 2],
  sparse![464; 1 => 1, 3 => -1, 7 => 3, 15 => -1, 57 => -1, 115 => 3, 231 => -1, 463 => 1],
  sparse![464; 1 => -1, 3 => 2, 7 => 2, 15 => -1, 57 => 1, 463 => 1],
  sparse![464; 1 => 2, 3 => -1, 7 => 1, 57 => -2, 115 => 5, 231 => -1],
  sparse![464; 1 => 1, 15 => 1, 57 => -1, 115 => 2, 231 => 2, 463 => -1],
  sparse![464; 1 => -1, 3 => 3, 7 => -1, 15 => 1, 57 => 1, 115 => -1, 231 => 3, 463 => -1],
  sparse![464; 1 => -2, 3 => 5, 7 => -1, 57 => 2, 115 => -1, 231 => 1],
  sparse![464; 3 => 1, 7 => -1, 15 => 2, 115 => 1, 231 => -1, 463 => 2],
  sparse![464; 0 => -1, 1 => 2, 3 => -1, 7 => 3, 15 => -1, 28 => 1, 115 => 1, 231 => -1, 463 => 1],
  sparse![464; 0 => -1, 1 => 3, 3 => -1, 7 => 2, 15 => -1, 28 => 1, 57 => -1, 115 => 1, 463 => 1],
  sparse![464; 0 => 1, 1 => -1, 7 => 3, 15 => -1, 28 => -1, 57 => 3, 231 => -1, 463 => 1],
  sparse![464; 0 => 1, 7 => 2, 15 => -1, 28 => -1, 57 => 2, 463 => 1],
  sparse![464; 3 => 2, 7 => 1, 15 => -1, 231 => 1, 463 => 1],
  sparse![464; 0 => -1, 1 => 2, 15 => 1, 28 => 1, 231 => 2, 463 => -1],
  sparse![464; 0 => -1, 1 => 3, 7 => -1, 15 => 1, 28 => 1, 57 => -1, 231 => 3, 463 => -1],
  sparse![464; 0 => -1, 1 => 4, 3 => -1, 28 => 1, 57 => -2, 115 => 3],
  sparse![464; 7 => 1, 15 => 1, 115 => 2, 231 => 1, 463 => -1],
  sparse![464; 1 => -1, 3 => 2, 7 => 1, 57 => 1, 115 => 2, 231 => -1],
  sparse![464; 3 => -1, 7 => 4, 15 => -1, 115 => 3, 231 => -2, 463 => 1],
  sparse![464; 0 => -1, 1 => 1, 3 => 2, 28 => 1, 57 => 1],
  sparse![464; 0 => 1, 1 => -1, 3 => 1, 15 => 1, 28 => -1, 57 => 3, 115 => -1, 231 => 2, 463 => -1],
  sparse![464; 0 => 1, 3 => 1, 7 => -1, 15 => 1, 28 => -1, 57 => 2, 115 => -1, 231 => 3, 463 => -1],
  sparse![464; 3 => 3, 7 => -2, 15 => 1, 115 => -1, 231 => 4, 463 => -1],
  sparse![464; 0 => 1, 1 => -2, 3 => 3, 28 => -1, 57 => 4, 115 => -1],
  sparse![464; 0 => 1, 1 => 1, 28 => -1, 57 => 1, 115 => 2],
  sparse![464; 1 => -2, 3 => 6, 7 => -2, 57 => -2, 115 => 6, 231 => -2],
]
```

### Level 465

dim S₂ = **61**; eta rank = **14**; full eta basis = **NO**; Sturm bound B = **128**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![465; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![465; 30 => 1, 92 => 1, 154 => 1, 464 => 1],
  sparse![465; 0 => 2, 154 => 2],
  sparse![465; 0 => 1, 4 => 1, 30 => 1, 154 => 1],
  sparse![465; 4 => 2, 30 => 2],
  sparse![465; 2 => 2, 464 => 2],
  sparse![465; 2 => 1, 14 => 1, 92 => 1, 464 => 1],
  sparse![465; 14 => 2, 92 => 2],
  sparse![465; 0 => 1, 2 => 1, 154 => 1, 464 => 1],
  sparse![465; 0 => -1, 2 => 2, 4 => 2, 14 => -1, 30 => 2, 92 => -1, 154 => -1, 464 => 2],
  sparse![465; 2 => 1, 4 => 1, 30 => 1, 464 => 1],
  sparse![465; 0 => 1, 14 => 1, 92 => 1, 154 => 1],
  sparse![465; 0 => 2, 2 => -1, 4 => -1, 14 => 2, 30 => -1, 92 => 2, 154 => 2, 464 => -1],
  sparse![465; 4 => 1, 14 => 1, 30 => 1, 92 => 1],
]
```

### Level 466

dim S₂ = **57**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **117**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 467

dim S₂ = **39**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **78**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![467; 0 => 2, 466 => 2],
]
```

### Level 468

dim S₂ = **73**; eta rank = **73**; full eta basis = **YES**; Sturm bound B = **168**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![468; 0 => -4, 1 => 8, 2 => 4, 3 => -3, 5 => -4, 8 => -1, 11 => 1, 12 => 2, 17 => 1, 25 => -1, 38 => -2, 77 => 3, 116 => 1, 233 => -1],
  sparse![468; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 11 => 1, 38 => -1, 77 => 4, 155 => -1],
  sparse![468; 0 => -3, 1 => 6, 2 => 2, 3 => -2, 5 => -1, 12 => 1, 25 => -2, 51 => 2, 77 => 1],
  sparse![468; 0 => -3, 1 => 6, 2 => 2, 3 => -2, 5 => -1, 12 => 1, 25 => -1, 155 => 1, 233 => 2, 467 => -1],
  sparse![468; 0 => -3, 1 => 6, 2 => 4, 3 => -2, 5 => -4, 8 => -2, 11 => 1, 12 => 1, 17 => 3, 25 => -1, 35 => -1, 38 => -2, 77 => 3, 116 => 2, 233 => -1],
  sparse![468; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -2, 11 => 1, 77 => 1, 155 => 1],
  sparse![468; 0 => -3, 1 => 7, 2 => 2, 3 => -3, 5 => -3, 11 => 2, 12 => -1, 25 => 3, 38 => -2, 51 => -1, 77 => 5, 155 => -2],
  sparse![468; 0 => -3, 1 => 7, 2 => 2, 3 => -3, 5 => -3, 11 => 2, 12 => 1, 25 => -2, 38 => -3, 51 => 1, 77 => 7, 116 => 1, 155 => -3, 233 => -1, 467 => 1],
  sparse![468; 0 => -3, 1 => 7, 2 => 2, 3 => -2, 5 => -3, 11 => 1, 12 => 2, 25 => -3, 38 => -3, 51 => 1, 77 => 7, 155 => -2],
  sparse![468; 0 => -3, 1 => 8, 3 => -3, 12 => -1, 25 => 2, 51 => -1, 77 => 2],
  sparse![468; 0 => -3, 1 => 8, 2 => 1, 3 => -4, 5 => -4, 11 => 4, 17 => 1, 25 => -1, 35 => -1, 51 => 2, 77 => 3, 155 => -2, 233 => -1, 467 => 1],
  sparse![468; 0 => -3, 1 => 8, 2 => 1, 3 => -3, 5 => -3, 11 => 2, 25 => -1, 51 => 1, 77 => 2],
  sparse![468; 0 => -3, 1 => 8, 2 => 2, 3 => -3, 5 => -3, 11 => 1, 12 => 1, 25 => -1, 77 => 2],
  sparse![468; 0 => -2, 1 => 1, 2 => 6, 5 => -3, 8 => -1, 12 => 2, 17 => 1, 25 => -1, 38 => -2, 77 => 3, 116 => 1, 233 => -1],
  sparse![468; 0 => -2, 1 => 1, 2 => 7, 5 => -3, 8 => -2, 17 => 1, 38 => 1, 77 => 1],
  sparse![468; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -2, 12 => 2, 25 => -1, 35 => 1, 38 => -2, 77 => 3, 116 => 1, 233 => -1],
  sparse![468; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -2, 11 => 1, 38 => 2, 77 => 1, 116 => -1, 155 => -1, 467 => 1],
  sparse![468; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -2, 11 => 1, 25 => 1, 38 => -1, 51 => 1, 77 => 2, 155 => -1],
  sparse![468; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -2, 11 => 1, 25 => 2, 38 => -1, 51 => -1, 77 => 1, 233 => 2, 467 => -1],
  sparse![468; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -1, 8 => -2, 17 => 3, 25 => 2, 35 => -1, 38 => -1, 51 => -1, 116 => 2, 155 => 1, 233 => -1],
  sparse![468; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -1, 8 => -2, 12 => 1, 17 => 3, 25 => -1, 35 => -1, 38 => -1, 51 => 1, 77 => 1, 116 => 1, 233 => -1, 467 => 1],
  sparse![468; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -1, 8 => -1, 17 => 1, 38 => 1, 77 => -1, 116 => -1, 155 => 2, 233 => 2, 467 => -1],
  sparse![468; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 5 => -1, 38 => -1, 77 => 4, 155 => -1],
  sparse![468; 0 => -2, 1 => 3, 2 => 3, 3 => -1, 8 => -1, 11 => -1, 35 => 1, 38 => 1, 77 => -2, 116 => -1, 155 => 3, 233 => 3, 467 => -2],
  sparse![468; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 25 => 1, 38 => -1, 77 => 2],
  sparse![468; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 12 => 1, 25 => -1, 38 => -2, 77 => 3, 116 => 2, 233 => -1],
  sparse![468; 0 => -2, 1 => 3, 2 => 4, 3 => -1, 5 => -4, 8 => -2, 11 => 2, 12 => 2, 17 => 3, 25 => -3, 35 => -1, 38 => -4, 51 => 1, 77 => 8, 116 => 2, 155 => -2, 233 => -3, 467 => 1],
  sparse![468; 0 => -2, 1 => 3, 2 => 4, 3 => -1, 5 => -3, 8 => -2, 11 => 1, 17 => 3, 35 => -1, 77 => 1, 155 => 1],
  sparse![468; 0 => -2, 1 => 3, 2 => 4, 3 => -1, 5 => -3, 8 => -1, 11 => 1, 17 => 1, 38 => 1, 77 => 2, 155 => -1, 233 => -1, 467 => 1],
  sparse![468; 0 => -2, 1 => 3, 2 => 4, 3 => -1, 5 => -3, 8 => -1, 11 => 1, 12 => 1, 25 => -3, 35 => 1, 38 => -2, 51 => 2, 77 => 7, 155 => -3],
  sparse![468; 0 => -2, 1 => 3, 2 => 4, 3 => -1, 5 => -2, 8 => -1, 35 => 1, 38 => 1, 77 => 1],
  sparse![468; 0 => -2, 1 => 3, 2 => 4, 3 => -1, 5 => -2, 8 => -1, 17 => 1, 38 => -2, 77 => 5, 116 => 1, 155 => -1, 233 => -1],
  sparse![468; 0 => -2, 1 => 3, 2 => 5, 3 => -1, 5 => -4, 8 => -2, 11 => 1, 17 => 3, 35 => -1, 38 => -3, 77 => 7, 116 => 2, 155 => -2, 233 => -3, 467 => 1],
  sparse![468; 0 => -2, 1 => 3, 2 => 5, 3 => -1, 5 => -4, 8 => -2, 11 => 1, 12 => 1, 17 => 3, 25 => -3, 35 => -1, 38 => -3, 51 => 2, 77 => 8, 116 => 1, 155 => -3, 233 => -3, 467 => 2],
  sparse![468; 0 => -2, 1 => 4, 3 => -1, 5 => 1, 12 => 2, 51 => -1, 77 => -1, 155 => 2],
  sparse![468; 0 => -2, 1 => 4, 5 => 1, 11 => -1, 12 => -1, 25 => 3, 38 => 1, 51 => -2, 77 => -2, 155 => 3],
  sparse![468; 0 => -2, 1 => 4, 2 => 1, 3 => -1, 5 => -1, 11 => 1, 38 => 1, 51 => 1, 77 => 1, 155 => -1],
  sparse![468; 0 => -2, 1 => 4, 2 => 1, 3 => -1, 5 => -1, 8 => 1, 25 => 1, 38 => -1, 51 => -1, 77 => 1, 116 => 1, 155 => 2, 233 => -1],
  sparse![468; 0 => -2, 1 => 4, 2 => 1, 3 => -1, 12 => 1, 25 => -3, 38 => -2, 51 => 3, 77 => 5, 155 => -2],
  sparse![468; 0 => -2, 1 => 4, 2 => 1, 3 => -1, 12 => 1, 25 => -2, 38 => -2, 51 => 1, 77 => 4, 155 => -1, 233 => 2, 467 => -1],
  sparse![468; 0 => -2, 1 => 4, 2 => 1, 5 => -2, 11 => 1, 12 => 1, 25 => -3, 38 => -2, 51 => 2, 77 => 7, 155 => -3],
  sparse![468; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 38 => 1, 77 => 1],
  sparse![468; 0 => -2, 1 => 4, 2 => 2, 3 => -1, 5 => -3, 8 => -1, 11 => 1, 12 => 1, 17 => 3, 25 => -2, 35 => -1, 38 => -3, 51 => 1, 77 => 7, 116 => 1, 155 => -2, 233 => -1],
  sparse![468; 0 => -2, 1 => 5, 2 => -2, 3 => -2, 5 => 5, 8 => 1, 11 => -2, 12 => -2, 17 => -2, 25 => 5, 35 => 1, 38 => 2, 51 => -2, 77 => -3, 116 => -1, 155 => 2, 233 => 2, 467 => -1],
  sparse![468; 0 => -2, 1 => 5, 2 => -2, 3 => -2, 5 => 5, 8 => 1, 11 => -2, 17 => -2, 35 => 1, 38 => 1, 77 => -1, 155 => 1, 233 => 1],
  sparse![468; 0 => -2, 1 => 5, 2 => -1, 3 => -2, 5 => 1, 8 => 2, 17 => -1, 38 => 3, 77 => -2, 116 => -2, 155 => 1, 233 => 3, 467 => -1],
  sparse![468; 0 => -2, 1 => 5, 2 => -1, 3 => -2, 5 => 3, 11 => -1, 12 => -2, 25 => 5, 38 => 1, 51 => -2, 77 => -1, 155 => 1],
  sparse![468; 0 => -2, 1 => 5, 2 => -1, 3 => -2, 5 => 3, 11 => -1, 77 => 1, 116 => 1, 233 => -1, 467 => 1],
  sparse![468; 0 => -2, 1 => 5, 3 => -2, 5 => -1, 11 => 2, 17 => 1, 35 => -1, 38 => 1, 116 => -1, 233 => 1, 467 => 1],
  sparse![468; 0 => -2, 1 => 5, 3 => -2, 5 => -1, 8 => 1, 11 => 1, 17 => -1, 35 => 1, 38 => 2, 77 => 1, 116 => -1, 155 => -1, 467 => 1],
  sparse![468; 0 => -2, 1 => 5, 3 => -2, 5 => -1, 8 => 1, 11 => 1, 38 => -1, 77 => 5, 155 => -2, 233 => -1, 467 => 1],
  sparse![468; 0 => -2, 1 => 5, 3 => -2, 5 => -1, 8 => 2, 11 => 1, 17 => -1, 77 => 1, 155 => 1],
  sparse![468; 0 => -2, 1 => 5, 3 => -2, 8 => -1, 17 => 3, 35 => -1, 77 => 2, 116 => -1, 233 => 2, 467 => -1],
  sparse![468; 0 => -2, 1 => 5, 3 => -2, 8 => 1, 11 => 1, 17 => -1, 38 => -1, 77 => 4, 155 => -2, 467 => 1],
  sparse![468; 0 => -2, 1 => 5, 3 => -2, 5 => 1, 17 => -1, 35 => 1, 77 => -1, 116 => 2, 155 => 2, 467 => -1],
  sparse![468; 0 => -2, 1 => 5, 3 => -2, 5 => 1, 8 => 1, 17 => -1, 38 => 2, 77 => -1, 116 => -1, 467 => 2],
  sparse![468; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 5 => -3, 8 => -1, 11 => 2, 17 => 3, 35 => -1, 77 => 2, 233 => -1, 467 => 1],
  sparse![468; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 5 => -3, 11 => 2, 17 => 2, 25 => -2, 35 => -1, 38 => 1, 51 => 1, 77 => 6, 155 => -3, 233 => -2, 467 => 1],
  sparse![468; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 5 => -3, 11 => 2, 17 => 2, 35 => -1, 38 => -2, 77 => 7, 116 => 1, 155 => -3, 233 => -3, 467 => 2],
  sparse![468; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 5 => -2, 11 => 1, 35 => 1, 38 => 1, 77 => 2, 155 => -1, 233 => -1, 467 => 1],
  sparse![468; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 5 => -2, 11 => 1, 17 => 1, 38 => -2, 77 => 6, 116 => 1, 155 => -2, 233 => -2, 467 => 1],
  sparse![468; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 5 => -2, 8 => 1, 11 => 1, 38 => -1, 77 => 2, 116 => 1, 155 => 1, 233 => -1],
  sparse![468; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 17 => -1, 35 => 1, 38 => -2, 77 => 4, 116 => 1, 155 => -1],
  sparse![468; 0 => -1, 2 => 2, 3 => 1, 5 => 1, 11 => -1, 12 => -1, 25 => 4, 51 => -1, 77 => -1, 155 => 1],
  sparse![468; 0 => -1, 2 => 2, 3 => 1, 5 => 1, 11 => -1, 38 => 3, 77 => -2, 116 => -2, 155 => 1, 233 => 3, 467 => -1],
  sparse![468; 0 => -1, 2 => 2, 3 => 1, 5 => 1, 11 => -1, 25 => 2, 38 => -1, 51 => -1, 116 => 2, 155 => 1, 233 => -1],
  sparse![468; 0 => -1, 2 => 2, 3 => 1, 5 => 2, 8 => -1, 11 => -2, 12 => 1, 35 => 1, 38 => -2, 51 => -1, 77 => 2, 116 => 1, 155 => 2, 467 => -1],
  sparse![468; 0 => -1, 2 => 2, 3 => 2, 5 => -1, 12 => -1, 25 => 4, 51 => -2, 77 => 1],
  sparse![468; 0 => -1, 2 => 2, 3 => 2, 5 => -1, 12 => 1, 25 => -1, 38 => -1, 77 => 3, 116 => 1, 155 => -1, 233 => -1, 467 => 1],
  sparse![468; 0 => -1, 2 => 3, 5 => 2, 8 => -1, 11 => -1, 38 => -1, 51 => 1, 77 => 2, 155 => -1, 467 => 1],
  sparse![468; 0 => -1, 2 => 3, 3 => 1, 5 => -1, 8 => -1, 25 => 2, 35 => 1, 38 => -1, 51 => -1, 77 => 1, 233 => 2, 467 => -1],
  sparse![468; 0 => -1, 2 => 3, 3 => 1, 5 => -1, 8 => -1, 17 => 1, 38 => -1, 77 => 5, 155 => -2, 233 => -1, 467 => 1],
  sparse![468; 0 => -1, 2 => 3, 3 => 1, 5 => -1, 8 => -1, 12 => 1, 25 => -1, 35 => 1, 38 => -2, 51 => 1, 77 => 3, 116 => 2, 155 => -1, 233 => -1],
]
```

### Level 469

dim S₂ = **43**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **90**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 470

dim S₂ = **69**; eta rank = **32**; full eta basis = **NO**; Sturm bound B = **144**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![470; 0 => 2, 46 => 2],
  sparse![470; 1 => 2, 93 => 2],
  sparse![470; 4 => 2, 234 => 2],
  sparse![470; 9 => 2, 469 => 2],
  sparse![470; 0 => -1, 1 => 3, 46 => -1, 93 => 3],
  sparse![470; 0 => 1, 1 => 1, 46 => 1, 93 => 1],
  sparse![470; 0 => 3, 1 => -1, 46 => 3, 93 => -1],
  sparse![470; 4 => -1, 9 => 3, 234 => -1, 469 => 3],
  sparse![470; 4 => 1, 9 => 1, 234 => 1, 469 => 1],
  sparse![470; 4 => 3, 9 => -1, 234 => 3, 469 => -1],
  sparse![470; 0 => 1, 4 => 1, 46 => 1, 234 => 1],
  sparse![470; 1 => 1, 9 => 1, 93 => 1, 469 => 1],
  sparse![470; 0 => -2, 1 => 4, 4 => 1, 9 => -1, 46 => 3, 93 => -1],
  sparse![470; 0 => -1, 1 => 3, 46 => 4, 93 => -2, 234 => -1, 469 => 1],
  sparse![470; 0 => -1, 1 => 1, 4 => 3, 9 => -1, 46 => 3, 93 => -1, 234 => -1, 469 => 1],
  sparse![470; 4 => 3, 9 => -1, 46 => 4, 93 => -2, 234 => -1, 469 => 1],
  sparse![470; 0 => -2, 1 => 4, 4 => 1, 9 => -1, 234 => -1, 469 => 3],
  sparse![470; 0 => -1, 1 => 3, 4 => 1, 9 => -1, 46 => 1, 93 => -1, 234 => -1, 469 => 3],
  sparse![470; 0 => -1, 1 => 2, 9 => 1, 46 => -1, 93 => 2, 469 => 1],
  sparse![470; 0 => -1, 1 => 2, 4 => 1, 46 => -1, 93 => 2, 234 => 1],
  sparse![470; 0 => -1, 1 => 2, 4 => 2, 9 => -1, 46 => -1, 93 => 2, 234 => 2, 469 => -1],
  sparse![470; 1 => 1, 4 => -1, 9 => 2, 93 => 1, 234 => -1, 469 => 2],
  sparse![470; 1 => 1, 4 => 1, 93 => 1, 234 => 1],
  sparse![470; 1 => 1, 4 => 2, 9 => -1, 93 => 1, 234 => 2, 469 => -1],
  sparse![470; 0 => 1, 4 => -1, 9 => 2, 46 => 1, 234 => -1, 469 => 2],
  sparse![470; 0 => 1, 9 => 1, 46 => 1, 469 => 1],
  sparse![470; 0 => 1, 4 => 2, 9 => -1, 46 => 1, 234 => 2, 469 => -1],
  sparse![470; 0 => 2, 1 => -1, 4 => -1, 9 => 2, 46 => 2, 93 => -1, 234 => -1, 469 => 2],
  sparse![470; 0 => 2, 1 => -1, 9 => 1, 46 => 2, 93 => -1, 469 => 1],
  sparse![470; 0 => 2, 1 => -1, 4 => 1, 46 => 2, 93 => -1, 234 => 1],
  sparse![470; 0 => 1, 1 => -1, 4 => -1, 9 => 3, 46 => -1, 93 => 3, 234 => 1, 469 => -1],
  sparse![470; 0 => 3, 1 => -1, 4 => -1, 9 => 1, 46 => -1, 93 => 1, 234 => 3, 469 => -1],
]
```

### Level 471

dim S₂ = **51**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **105**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 472

dim S₂ = **57**; eta rank = **21**; full eta basis = **NO**; Sturm bound B = **120**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![472; 0 => 2, 58 => 2],
  sparse![472; 1 => 2, 117 => 2],
  sparse![472; 3 => 2, 235 => 2],
  sparse![472; 7 => 2, 471 => 2],
  sparse![472; 0 => -2, 1 => 6, 3 => -2, 58 => -2, 117 => 6, 235 => -2],
  sparse![472; 1 => -2, 3 => 6, 7 => -2, 117 => -2, 235 => 6, 471 => -2],
  sparse![472; 0 => 2, 1 => -2, 3 => 3, 7 => -1, 58 => -2, 117 => 4, 235 => 1, 471 => -1],
  sparse![472; 0 => 2, 1 => -1, 7 => 1, 58 => -2, 117 => 5, 235 => -2, 471 => 1],
  sparse![472; 0 => -1, 1 => 3, 3 => -2, 7 => 2, 58 => -1, 117 => 1, 235 => 4, 471 => -2],
  sparse![472; 0 => -2, 1 => 5, 3 => -1, 58 => -2, 117 => 5, 235 => -1],
  sparse![472; 0 => 1, 3 => -1, 7 => 2, 58 => 1, 117 => -2, 235 => 5, 471 => -2],
  sparse![472; 1 => -1, 3 => 5, 7 => -2, 117 => -1, 235 => 5, 471 => -2],
  sparse![472; 1 => -1, 3 => 3, 117 => -1, 235 => 3],
  sparse![472; 1 => 1, 3 => 1, 117 => 1, 235 => 1],
  sparse![472; 1 => 3, 3 => -1, 117 => 3, 235 => -1],
  sparse![472; 1 => 1, 3 => -1, 7 => 2, 117 => 1, 235 => -1, 471 => 2],
  sparse![472; 0 => -1, 1 => 1, 3 => 4, 7 => -2, 58 => -1, 117 => 3, 235 => -2, 471 => 2],
  sparse![472; 0 => 2, 1 => -1, 3 => 1, 58 => 2, 117 => -1, 235 => 1],
  sparse![472; 0 => 1, 1 => -2, 3 => 5, 7 => -2, 58 => 1, 235 => -1, 471 => 2],
  sparse![472; 0 => -2, 1 => 4, 3 => 1, 7 => -1, 58 => 2, 117 => -2, 235 => 3, 471 => -1],
  sparse![472; 0 => -2, 1 => 5, 3 => -2, 7 => 1, 58 => 2, 117 => -1, 471 => 1],
]
```

### Level 473

dim S₂ = **43**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **88**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![473; 0 => 2, 10 => 2],
  sparse![473; 42 => 2, 472 => 2],
  sparse![473; 0 => 1, 10 => 1, 42 => 1, 472 => 1],
]
```

### Level 474

dim S₂ = **77**; eta rank = **12**; full eta basis = **NO**; Sturm bound B = **160**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![474; 0 => 1, 1 => 1, 78 => 1, 157 => 1],
  sparse![474; 2 => 1, 5 => 1, 236 => 1, 473 => 1],
  sparse![474; 0 => 1, 1 => -1, 2 => -2, 5 => 4, 78 => -1, 157 => 1, 236 => 4, 473 => -2],
  sparse![474; 0 => -1, 1 => 1, 2 => 4, 5 => -2, 78 => 1, 157 => -1, 236 => -2, 473 => 4],
  sparse![474; 0 => 2, 1 => -1, 5 => 1, 78 => -1, 157 => 2, 236 => 1],
  sparse![474; 0 => 1, 2 => -1, 5 => 2, 157 => 1, 236 => 2, 473 => -1],
  sparse![474; 0 => 2, 1 => -1, 2 => -1, 5 => 2, 78 => 2, 157 => -1, 236 => -1, 473 => 2],
  sparse![474; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 78 => -1, 157 => 2, 236 => 2, 473 => -1],
  sparse![474; 1 => 1, 2 => 2, 5 => -1, 78 => 1, 236 => -1, 473 => 2],
  sparse![474; 0 => -1, 1 => 2, 2 => 1, 78 => 2, 157 => -1, 473 => 1],
  sparse![474; 0 => 4, 1 => -2, 2 => -1, 5 => 1, 78 => -2, 157 => 4, 236 => 1, 473 => -1],
  sparse![474; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 78 => 4, 157 => -2, 236 => -1, 473 => 1],
]
```

### Level 475

dim S₂ = **45**; eta rank = **10**; full eta basis = **NO**; Sturm bound B = **100**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![475; 0 => 2, 94 => 2],
  sparse![475; 0 => 1, 4 => 1, 18 => 1, 94 => 1],
  sparse![475; 4 => 2, 18 => 2],
  sparse![475; 4 => 2, 474 => 2],
  sparse![475; 4 => 1, 24 => 1, 94 => 1, 474 => 1],
  sparse![475; 24 => 2, 94 => 2],
  sparse![475; 0 => 1, 4 => 1, 94 => 1, 474 => 1],
  sparse![475; 4 => 2, 18 => 1, 474 => 1],
  sparse![475; 0 => 1, 24 => 1, 94 => 2],
  sparse![475; 4 => 1, 18 => 1, 24 => 1, 94 => 1],
]
```

### Level 476

dim S₂ = **67**; eta rank = **66**; full eta basis = **NO**; Sturm bound B = **144**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![476; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![476; 1 => 1, 3 => 1, 13 => 1, 27 => 1],
  sparse![476; 16 => 1, 33 => 1, 118 => 1, 237 => 1],
  sparse![476; 33 => 1, 67 => 1, 237 => 1, 475 => 1],
  sparse![476; 0 => 2, 1 => -1, 3 => 1, 16 => -2, 33 => 5, 67 => -1],
  sparse![476; 0 => 1, 1 => -1, 3 => 2, 16 => -1, 33 => 5, 67 => -2],
  sparse![476; 0 => 1, 1 => 2, 3 => -1, 16 => -1, 33 => 2, 67 => 1],
  sparse![476; 1 => 2, 33 => 2],
  sparse![476; 0 => -1, 1 => 2, 3 => 1, 16 => 1, 33 => 2, 67 => -1],
  sparse![476; 0 => -1, 1 => 5, 3 => -2, 16 => 1, 33 => -1, 67 => 2],
  sparse![476; 0 => -2, 1 => 5, 3 => -1, 16 => 2, 33 => -1, 67 => 1],
  sparse![476; 6 => 2, 13 => -1, 27 => 1, 118 => -2, 237 => 5, 475 => -1],
  sparse![476; 6 => 1, 13 => -1, 27 => 2, 118 => -1, 237 => 5, 475 => -2],
  sparse![476; 6 => 1, 13 => 2, 27 => -1, 118 => -1, 237 => 2, 475 => 1],
  sparse![476; 13 => 2, 237 => 2],
  sparse![476; 6 => -1, 13 => 2, 27 => 1, 118 => 1, 237 => 2, 475 => -1],
  sparse![476; 6 => -1, 13 => 5, 27 => -2, 118 => 1, 237 => -1, 475 => 2],
  sparse![476; 6 => -2, 13 => 5, 27 => -1, 118 => 2, 237 => -1, 475 => 1],
  sparse![476; 0 => 2, 118 => 2],
  sparse![476; 0 => 1, 6 => 1, 16 => 1, 118 => 1],
  sparse![476; 6 => 2, 16 => 2],
  sparse![476; 1 => 2, 237 => 2],
  sparse![476; 1 => 1, 13 => 1, 33 => 1, 237 => 1],
  sparse![476; 13 => 2, 33 => 2],
  sparse![476; 3 => 2, 475 => 2],
  sparse![476; 3 => 1, 27 => 1, 67 => 1, 475 => 1],
  sparse![476; 27 => 2, 67 => 2],
  sparse![476; 0 => 2, 1 => -1, 6 => 2, 13 => -1, 16 => -1, 33 => 2, 118 => -1, 237 => 2],
  sparse![476; 0 => -2, 1 => 4, 6 => 1, 13 => -1, 16 => 1, 33 => -1, 118 => -2, 237 => 4],
  sparse![476; 0 => -1, 1 => 3, 118 => -1, 237 => 3],
  sparse![476; 0 => 1, 1 => 1, 118 => 1, 237 => 1],
  sparse![476; 0 => 3, 1 => -1, 118 => 3, 237 => -1],
  sparse![476; 0 => 4, 1 => -2, 6 => -1, 13 => 1, 16 => -1, 33 => 1, 118 => 4, 237 => -2],
  sparse![476; 0 => -1, 1 => 2, 6 => 2, 13 => -1, 16 => 2, 33 => -1, 118 => -1, 237 => 2],
  sparse![476; 1 => 1, 6 => 2, 13 => -1, 16 => 2, 33 => -1, 237 => 1],
  sparse![476; 0 => 1, 6 => 2, 13 => -1, 16 => 2, 33 => -1, 118 => 1],
  sparse![476; 0 => -1, 1 => 2, 6 => 1, 16 => 1, 118 => -1, 237 => 2],
  sparse![476; 1 => 1, 6 => 1, 16 => 1, 237 => 1],
  sparse![476; 0 => 2, 1 => -1, 6 => 1, 16 => 1, 118 => 2, 237 => -1],
  sparse![476; 0 => -1, 1 => 2, 13 => 1, 33 => 1, 118 => -1, 237 => 2],
  sparse![476; 0 => 1, 13 => 1, 33 => 1, 118 => 1],
  sparse![476; 0 => 2, 1 => -1, 13 => 1, 33 => 1, 118 => 2, 237 => -1],
  sparse![476; 0 => 1, 6 => -1, 13 => 2, 16 => -1, 33 => 2, 118 => 1],
  sparse![476; 0 => 2, 1 => -1, 6 => -1, 13 => 2, 16 => -1, 33 => 2, 118 => 2, 237 => -1],
  sparse![476; 1 => 2, 3 => -1, 13 => 2, 27 => -1, 33 => -1, 67 => 2, 237 => -1, 475 => 2],
  sparse![476; 1 => -2, 3 => 4, 13 => 1, 27 => -1, 33 => 1, 67 => -1, 237 => -2, 475 => 4],
  sparse![476; 1 => -1, 3 => 3, 237 => -1, 475 => 3],
  sparse![476; 1 => 1, 3 => 1, 237 => 1, 475 => 1],
  sparse![476; 1 => 3, 3 => -1, 237 => 3, 475 => -1],
  sparse![476; 1 => 4, 3 => -2, 13 => -1, 27 => 1, 33 => -1, 67 => 1, 237 => 4, 475 => -2],
  sparse![476; 1 => -1, 3 => 2, 13 => 2, 27 => -1, 33 => 2, 67 => -1, 237 => -1, 475 => 2],
  sparse![476; 3 => 1, 13 => 2, 27 => -1, 33 => 2, 67 => -1, 475 => 1],
  sparse![476; 1 => 1, 13 => 2, 27 => -1, 33 => 2, 67 => -1, 237 => 1],
  sparse![476; 1 => -1, 3 => 2, 13 => 1, 33 => 1, 237 => -1, 475 => 2],
  sparse![476; 3 => 1, 13 => 1, 33 => 1, 475 => 1],
  sparse![476; 6 => -2, 13 => 5, 16 => -2, 27 => -1, 33 => 5, 67 => -1],
  sparse![476; 0 => 1, 1 => -1, 3 => 1, 13 => 2, 16 => -2, 27 => -1, 33 => 5, 67 => -2, 118 => -1, 237 => 2],
  sparse![476; 0 => 1, 13 => 2, 16 => -2, 27 => -1, 33 => 5, 67 => -2, 118 => -1, 237 => 3, 475 => -1],
  sparse![476; 0 => 1, 1 => -1, 3 => 1, 6 => 1, 16 => -1, 33 => 3, 67 => -1, 118 => -1, 237 => 2],
  sparse![476; 0 => 1, 6 => 1, 16 => -1, 33 => 3, 67 => -1, 118 => -1, 237 => 3, 475 => -1],
  sparse![476; 0 => 2, 1 => -1, 6 => 1, 16 => -1, 33 => 3, 67 => -1, 237 => 2, 475 => -1],
  sparse![476; 1 => 2, 3 => -1, 6 => 1, 16 => -1, 33 => 3, 67 => -1, 118 => -2, 237 => 5, 475 => -2],
  sparse![476; 0 => 1, 1 => -1, 3 => 1, 6 => 1, 13 => -1, 16 => -1, 27 => 1, 33 => 2, 118 => -1, 237 => 2],
  sparse![476; 0 => 1, 6 => 1, 13 => -1, 16 => -1, 27 => 1, 33 => 2, 118 => -1, 237 => 3, 475 => -1],
  sparse![476; 0 => 2, 1 => -1, 6 => 1, 13 => -1, 16 => -1, 27 => 1, 33 => 2, 237 => 2, 475 => -1],
  sparse![476; 0 => 1, 27 => 1, 67 => 1, 118 => 1],
]
```

### Level 477

dim S₂ = **51**; eta rank = **2**; full eta basis = **NO**; Sturm bound B = **108**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![477; 0 => 1, 2 => 1, 52 => 1, 158 => 1],
  sparse![477; 2 => 1, 8 => 1, 158 => 1, 476 => 1],
]
```

### Level 478

dim S₂ = **59**; eta rank = **5**; full eta basis = **NO**; Sturm bound B = **120**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![478; 0 => 2, 238 => 2],
  sparse![478; 1 => 2, 477 => 2],
  sparse![478; 0 => -1, 1 => 3, 238 => -1, 477 => 3],
  sparse![478; 0 => 1, 1 => 1, 238 => 1, 477 => 1],
  sparse![478; 0 => 3, 1 => -1, 238 => 3, 477 => -1],
]
```

### Level 479

dim S₂ = **40**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **80**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![479; 0 => 2, 478 => 2],
]
```

### Level 480

dim S₂ = **81**; eta rank = **81**; full eta basis = **YES**; Sturm bound B = **192**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![480; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![480; 1 => 1, 5 => 1, 9 => 1, 29 => 1],
  sparse![480; 3 => 1, 11 => 1, 19 => 1, 59 => 1],
  sparse![480; 7 => 1, 23 => 1, 39 => 1, 119 => 1],
  sparse![480; 15 => 1, 47 => 1, 79 => 1, 239 => 1],
  sparse![480; 31 => 1, 95 => 1, 159 => 1, 479 => 1],
  sparse![480; 1 => 2, 9 => 2],
  sparse![480; 3 => 2, 19 => 2],
  sparse![480; 5 => 2, 29 => 2],
  sparse![480; 7 => 2, 39 => 2],
  sparse![480; 11 => 2, 59 => 2],
  sparse![480; 15 => 2, 79 => 2],
  sparse![480; 23 => 2, 119 => 2],
  sparse![480; 47 => 2, 239 => 2],
  sparse![480; 1 => 1, 3 => 1, 5 => 1, 11 => 1],
  sparse![480; 3 => 1, 7 => 1, 11 => 1, 23 => 1],
  sparse![480; 7 => 1, 15 => 1, 23 => 1, 47 => 1],
  sparse![480; 9 => 1, 19 => 1, 29 => 1, 59 => 1],
  sparse![480; 19 => 1, 39 => 1, 59 => 1, 119 => 1],
  sparse![480; 39 => 1, 79 => 1, 119 => 1, 239 => 1],
  sparse![480; 0 => 1, 1 => 1, 14 => 1, 29 => 1],
  sparse![480; 1 => 1, 3 => 1, 29 => 1, 59 => 1],
  sparse![480; 3 => 1, 7 => 1, 59 => 1, 119 => 1],
  sparse![480; 7 => 1, 15 => 1, 119 => 1, 239 => 1],
  sparse![480; 15 => 1, 31 => 1, 239 => 1, 479 => 1],
  sparse![480; 3 => 2, 7 => 2],
  sparse![480; 11 => 2, 23 => 2],
  sparse![480; 19 => 2, 39 => 2],
  sparse![480; 59 => 2, 119 => 2],
  sparse![480; 0 => -2, 1 => 5, 3 => -1, 4 => 2, 9 => -1, 19 => 1],
  sparse![480; 1 => -2, 3 => 5, 7 => -1, 9 => 2, 19 => -1, 39 => 1],
  sparse![480; 2 => -2, 5 => 5, 11 => -1, 14 => 2, 29 => -1, 59 => 1],
  sparse![480; 3 => -2, 7 => 5, 15 => -1, 19 => 2, 39 => -1, 79 => 1],
  sparse![480; 5 => -2, 11 => 5, 23 => -1, 29 => 2, 59 => -1, 119 => 1],
  sparse![480; 11 => -2, 23 => 5, 47 => -1, 59 => 2, 119 => -1, 239 => 1],
  sparse![480; 0 => -2, 1 => 4, 2 => 2, 5 => -2, 11 => 2],
  sparse![480; 1 => -2, 3 => 4, 5 => 2, 11 => -2, 23 => 2],
  sparse![480; 4 => -2, 9 => 4, 14 => 2, 29 => -2, 59 => 2],
  sparse![480; 9 => -2, 19 => 4, 29 => 2, 59 => -2, 119 => 2],
  sparse![480; 0 => -2, 1 => 5, 3 => -1, 4 => -2, 9 => 5, 19 => -1],
  sparse![480; 0 => -1, 1 => 1, 3 => 2, 4 => 1, 9 => 1],
  sparse![480; 1 => -2, 3 => 5, 7 => -1, 9 => -2, 19 => 5, 39 => -1],
  sparse![480; 1 => -1, 3 => 1, 7 => 2, 9 => 1, 19 => 1],
  sparse![480; 2 => -2, 5 => 5, 11 => -1, 14 => -2, 29 => 5, 59 => -1],
  sparse![480; 2 => -1, 5 => 1, 11 => 2, 14 => 1, 29 => 1],
  sparse![480; 5 => -2, 11 => 5, 23 => -1, 29 => -2, 59 => 5, 119 => -1],
  sparse![480; 5 => -1, 11 => 1, 23 => 2, 29 => 1, 59 => 1],
  sparse![480; 1 => 1, 5 => 1, 15 => 1, 47 => 1],
  sparse![480; 0 => -2, 1 => 2, 2 => 2, 3 => 3, 7 => -1, 11 => -1, 23 => 1],
  sparse![480; 9 => 1, 29 => 1, 79 => 1, 239 => 1],
  sparse![480; 4 => -2, 9 => 2, 14 => 2, 19 => 3, 39 => -1, 59 => -1, 119 => 1],
  sparse![480; 0 => -5, 1 => 11, 2 => 1, 3 => -4, 4 => 5, 5 => -2, 9 => -4, 11 => 1, 14 => -1, 19 => 1, 29 => 1],
  sparse![480; 0 => -4, 1 => 10, 2 => 2, 3 => -4, 4 => 1, 5 => -4, 9 => -3, 11 => 2, 14 => -1, 19 => 2, 29 => 3],
  sparse![480; 1 => -5, 3 => 11, 5 => 1, 7 => -4, 9 => 5, 11 => -2, 19 => -4, 23 => 1, 29 => -1, 39 => 1, 59 => 1],
  sparse![480; 1 => -4, 3 => 10, 5 => 2, 7 => -4, 9 => 1, 11 => -4, 19 => -3, 23 => 2, 29 => -1, 39 => 2, 59 => 3],
  sparse![480; 3 => -5, 7 => 11, 11 => 1, 15 => -4, 19 => 5, 23 => -2, 39 => -4, 47 => 1, 59 => -1, 79 => 1, 119 => 1],
  sparse![480; 3 => -4, 7 => 10, 11 => 2, 15 => -4, 19 => 1, 23 => -4, 39 => -3, 47 => 2, 59 => -1, 79 => 2, 119 => 3],
  sparse![480; 3 => 1, 7 => 1, 19 => 1, 39 => 1],
  sparse![480; 0 => -2, 1 => 3, 3 => 2, 4 => 2, 7 => -1, 9 => -3, 19 => 4, 39 => -1],
  sparse![480; 0 => -2, 1 => 4, 3 => -2, 4 => 2, 7 => 2],
  sparse![480; 0 => -2, 1 => 5, 3 => -3, 7 => 3, 15 => -1, 19 => 1, 39 => 2, 79 => -1],
  sparse![480; 11 => 1, 23 => 1, 59 => 1, 119 => 1],
  sparse![480; 2 => -2, 5 => 3, 11 => 2, 14 => 2, 23 => -1, 29 => -3, 59 => 4, 119 => -1],
  sparse![480; 2 => -2, 5 => 4, 11 => -2, 14 => 2, 23 => 2],
  sparse![480; 2 => -2, 5 => 5, 11 => -3, 23 => 3, 47 => -1, 59 => 1, 119 => 2, 239 => -1],
  sparse![480; 0 => -7, 1 => 14, 2 => 7, 3 => -5, 4 => 1, 5 => -7, 9 => -2, 11 => 2, 14 => -1, 19 => 1, 29 => 1],
  sparse![480; 0 => -5, 1 => 13, 2 => 1, 3 => -5, 4 => -1, 5 => -4, 9 => -1, 11 => 2, 14 => 5, 19 => 1, 29 => -2],
  sparse![480; 0 => -4, 1 => 8, 2 => 2, 3 => -2, 4 => 2, 5 => -3, 9 => -1, 11 => 1, 19 => 1],
  sparse![480; 0 => -3, 1 => 5, 2 => 3, 4 => 1, 5 => -3, 7 => -1, 14 => -1, 19 => -1, 23 => 1, 29 => 2, 39 => 1, 59 => 1, 119 => -1],
  sparse![480; 1 => -7, 3 => 14, 5 => 7, 7 => -5, 9 => 1, 11 => -7, 19 => -2, 23 => 2, 29 => -1, 39 => 1, 59 => 1],
  sparse![480; 1 => -5, 3 => 13, 5 => 1, 7 => -5, 9 => -1, 11 => -4, 19 => -1, 23 => 2, 29 => 5, 39 => 1, 59 => -2],
  sparse![480; 1 => -4, 3 => 8, 5 => 2, 7 => -2, 9 => 2, 11 => -3, 19 => -1, 23 => 1, 39 => 1],
  sparse![480; 1 => -3, 3 => 5, 5 => 3, 9 => 1, 11 => -3, 15 => -1, 29 => -1, 39 => -1, 47 => 1, 59 => 2, 79 => 1, 119 => 1, 239 => -1],
  sparse![480; 3 => -1, 7 => 1, 11 => 1, 23 => 1, 39 => 2],
  sparse![480; 3 => 1, 7 => 1, 11 => -1, 23 => 1, 119 => 2],
  sparse![480; 7 => 2, 19 => -1, 39 => 1, 59 => 1, 119 => 1],
  sparse![480; 0 => 1, 14 => 1, 31 => 1, 479 => 1],
  sparse![480; 2 => 1, 4 => 1, 95 => 1, 159 => 1],
  sparse![480; 0 => 1, 3 => -1, 7 => 1, 11 => 1, 14 => 1, 39 => 1],
  sparse![480; 0 => 1, 14 => 1, 19 => 1, 23 => 1, 59 => -1, 119 => 1],
  sparse![480; 1 => 1, 3 => 1, 7 => -1, 19 => 1, 23 => 1, 29 => 1],
]
```

### Level 481

dim S₂ = **41**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **88**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 482

dim S₂ = **59**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **121**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 483

dim S₂ = **61**; eta rank = **12**; full eta basis = **NO**; Sturm bound B = **128**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![483; 0 => 2, 22 => 2],
  sparse![483; 2 => 2, 68 => 2],
  sparse![483; 6 => 2, 160 => 2],
  sparse![483; 20 => 2, 482 => 2],
  sparse![483; 0 => 1, 2 => 1, 22 => 1, 68 => 1],
  sparse![483; 6 => 1, 20 => 1, 160 => 1, 482 => 1],
  sparse![483; 0 => 1, 6 => 1, 22 => 1, 160 => 1],
  sparse![483; 2 => 1, 20 => 1, 68 => 1, 482 => 1],
  sparse![483; 6 => 1, 20 => 1, 22 => 1, 68 => 1],
  sparse![483; 2 => 1, 6 => 1, 68 => 1, 160 => 1],
  sparse![483; 0 => 1, 20 => 1, 22 => 1, 482 => 1],
  sparse![483; 0 => 1, 2 => 1, 160 => 1, 482 => 1],
]
```

### Level 484

dim S₂ = **49**; eta rank = **20**; full eta basis = **NO**; Sturm bound B = **132**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![484; 0 => 2, 10 => 2],
  sparse![484; 1 => 2, 21 => 2],
  sparse![484; 3 => 2, 43 => 2],
  sparse![484; 10 => 2, 120 => 2],
  sparse![484; 21 => 2, 241 => 2],
  sparse![484; 43 => 2, 483 => 2],
  sparse![484; 0 => 1, 10 => 2, 120 => 1],
  sparse![484; 1 => 1, 21 => 2, 241 => 1],
  sparse![484; 3 => 1, 43 => 2, 483 => 1],
  sparse![484; 0 => 2, 1 => -1, 10 => 2, 241 => 1],
  sparse![484; 1 => 1, 10 => 2, 120 => 2, 241 => -1],
  sparse![484; 0 => 1, 21 => 2, 120 => -1, 241 => 2],
  sparse![484; 0 => -1, 1 => 2, 21 => 2, 120 => 1],
  sparse![484; 1 => 2, 3 => -1, 21 => 2, 483 => 1],
  sparse![484; 3 => 1, 21 => 2, 241 => 2, 483 => -1],
  sparse![484; 1 => 1, 43 => 2, 241 => -1, 483 => 2],
  sparse![484; 1 => -1, 3 => 2, 43 => 2, 241 => 1],
  sparse![484; 0 => -1, 1 => 3, 3 => -1, 10 => -2, 21 => 6, 43 => -2, 120 => -1, 241 => 3, 483 => -1],
  sparse![484; 0 => -1, 1 => 3, 3 => -1, 21 => 2, 120 => 1, 241 => -1, 483 => 1],
  sparse![484; 0 => 1, 1 => -1, 3 => 1, 21 => 2, 120 => -1, 241 => 3, 483 => -1],
]
```

### Level 485

dim S₂ = **47**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **98**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 486

dim S₂ = **64**; eta rank = **64**; full eta basis = **YES**; Sturm bound B = **162**.

`Basis_cuspidal_eta_S2`: **complete cusp-form basis**.

```lean
[
  sparse![486; 2 => 2, 8 => 2],
  sparse![486; 5 => 2, 17 => 2],
  sparse![486; 8 => 2, 26 => 2],
  sparse![486; 17 => 2, 53 => 2],
  sparse![486; 26 => 2, 80 => 2],
  sparse![486; 53 => 2, 161 => 2],
  sparse![486; 0 => -1, 1 => 2, 5 => 2, 8 => 1],
  sparse![486; 0 => -1, 1 => 2, 2 => 1, 17 => 1, 26 => 2, 53 => -1],
  sparse![486; 2 => -1, 5 => 2, 17 => 2, 26 => 1],
  sparse![486; 2 => -1, 5 => 2, 8 => 1, 53 => 1, 80 => 2, 161 => -1],
  sparse![486; 8 => -1, 17 => 2, 53 => 2, 80 => 1],
  sparse![486; 8 => -1, 17 => 2, 26 => 1, 161 => 1, 242 => 2, 485 => -1],
  sparse![486; 2 => -1, 8 => 6, 26 => -1],
  sparse![486; 2 => 1, 8 => 2, 26 => 1],
  sparse![486; 5 => -1, 17 => 6, 53 => -1],
  sparse![486; 5 => 1, 17 => 2, 53 => 1],
  sparse![486; 8 => -1, 26 => 6, 80 => -1],
  sparse![486; 8 => 1, 26 => 2, 80 => 1],
  sparse![486; 17 => -1, 53 => 6, 161 => -1],
  sparse![486; 17 => 1, 53 => 2, 161 => 1],
  sparse![486; 0 => -1, 1 => 2, 2 => -1, 5 => 2, 8 => 1, 26 => 1],
  sparse![486; 0 => -1, 1 => 2, 5 => -1, 8 => 1, 17 => 4, 53 => -1],
  sparse![486; 0 => -1, 1 => 2, 5 => -1, 8 => 2, 17 => 2, 26 => -1, 80 => 2, 161 => -1],
  sparse![486; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 17 => 1, 26 => 2],
  sparse![486; 2 => -1, 5 => 2, 8 => -1, 17 => 2, 26 => 1, 80 => 1],
  sparse![486; 2 => -1, 5 => 2, 17 => -1, 26 => 1, 53 => 4, 161 => -1],
  sparse![486; 2 => -1, 5 => 2, 17 => -1, 26 => 2, 53 => 2, 80 => -1, 242 => 2, 485 => -1],
  sparse![486; 2 => -1, 5 => 2, 8 => 1, 17 => -1, 53 => 1, 80 => 2],
  sparse![486; 2 => 2, 8 => -1, 26 => 4, 80 => -1],
  sparse![486; 2 => 1, 8 => -1, 26 => 5, 80 => -1],
  sparse![486; 2 => 2, 8 => 1, 80 => 1],
  sparse![486; 2 => 1, 8 => 1, 26 => 1, 80 => 1],
  sparse![486; 2 => 2, 80 => 2],
  sparse![486; 2 => 1, 26 => 1, 80 => 2],
  sparse![486; 2 => -1, 8 => 3, 26 => 3, 80 => -1],
  sparse![486; 2 => -1, 8 => 5, 26 => -1, 80 => 1],
  sparse![486; 2 => -1, 8 => 4, 26 => -1, 80 => 2],
  sparse![486; 5 => 2, 17 => -1, 53 => 4, 161 => -1],
  sparse![486; 5 => 1, 17 => -1, 53 => 5, 161 => -1],
  sparse![486; 5 => 2, 17 => 1, 161 => 1],
  sparse![486; 5 => 1, 17 => 1, 53 => 1, 161 => 1],
  sparse![486; 5 => 2, 161 => 2],
  sparse![486; 5 => 1, 53 => 1, 161 => 2],
  sparse![486; 5 => -1, 17 => 3, 53 => 3, 161 => -1],
  sparse![486; 5 => -1, 17 => 5, 53 => -1, 161 => 1],
  sparse![486; 5 => -1, 17 => 4, 53 => -1, 161 => 2],
  sparse![486; 0 => 2, 1 => -1, 2 => -1, 5 => 1, 8 => 1, 26 => 3, 53 => -1, 80 => -1, 161 => 1],
  sparse![486; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 17 => 1, 26 => -1, 53 => 3, 80 => 1, 161 => -1],
  sparse![486; 2 => -1, 5 => 1, 8 => 2, 17 => -1, 26 => 1, 161 => 1, 242 => 2, 485 => -1],
  sparse![486; 2 => 1, 5 => -1, 8 => -1, 17 => 2, 53 => 1, 80 => 1, 242 => -1, 485 => 2],
  sparse![486; 0 => 2, 1 => -1, 5 => 1, 8 => 1, 26 => 2, 53 => -1, 80 => -1, 161 => 1],
  sparse![486; 5 => 1, 8 => 3, 17 => -1, 80 => -1, 161 => 1, 242 => 2, 485 => -1],
  sparse![486; 0 => -2, 1 => 1, 2 => 6, 5 => -2, 8 => -3, 17 => 2, 26 => 4, 53 => -2, 80 => -1, 161 => 1],
  sparse![486; 0 => -2, 1 => 1, 2 => 6, 5 => -2, 8 => -1, 53 => 2, 80 => 1, 161 => -1],
  sparse![486; 0 => -2, 1 => 1, 2 => 7, 5 => -3, 8 => -3, 17 => 2, 26 => 3, 53 => -1, 80 => -1, 161 => 1],
  sparse![486; 0 => -2, 1 => 1, 2 => 7, 5 => -3, 8 => -1, 26 => -1, 53 => 3, 80 => 1, 161 => -1],
  sparse![486; 0 => -2, 1 => 1, 2 => 8, 5 => -4, 8 => -3, 17 => 2, 26 => 2, 80 => -1, 161 => 1],
  sparse![486; 0 => -2, 1 => 1, 2 => 8, 5 => -4, 8 => -1, 26 => -2, 53 => 4, 80 => 1, 161 => -1],
  sparse![486; 0 => -2, 1 => 4, 2 => 2, 5 => -2, 8 => -1, 17 => 1, 26 => 2, 80 => -1, 161 => 1],
  sparse![486; 0 => -1, 1 => 2, 2 => -2, 5 => 3, 8 => 4, 17 => -3, 26 => -2, 53 => 3, 80 => 1, 161 => -1],
  sparse![486; 0 => -1, 1 => 2, 2 => -1, 5 => 1, 8 => 2, 17 => -1, 26 => 2, 53 => -1, 80 => -2, 161 => 2, 242 => 2, 485 => -1],
  sparse![486; 0 => -1, 1 => 2, 2 => -1, 5 => 1, 8 => 3, 17 => -2, 26 => -3, 53 => 5, 80 => 2, 161 => -2],
  sparse![486; 0 => -1, 1 => 2, 2 => -1, 5 => 1, 8 => 3, 17 => -2, 26 => -2, 53 => 3, 80 => 1, 161 => -1, 242 => 2, 485 => -1],
  sparse![486; 0 => -1, 1 => 2, 5 => -1, 17 => 4, 53 => -1, 80 => 1],
]
```

### Level 487

dim S₂ = **40**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **81**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 488

dim S₂ = **59**; eta rank = **12**; full eta basis = **NO**; Sturm bound B = **124**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![488; 0 => -1, 1 => 3, 3 => 1, 7 => -1, 60 => 1, 121 => -1, 243 => 1, 487 => 1],
  sparse![488; 0 => -1, 1 => 2, 3 => 2, 7 => -1, 60 => 1, 487 => 1],
  sparse![488; 0 => -1, 1 => 1, 3 => 3, 7 => -1, 60 => 1, 121 => 1, 243 => -1, 487 => 1],
  sparse![488; 0 => -1, 1 => 4, 3 => -2, 7 => 1, 60 => 1, 121 => -2, 243 => 4, 487 => -1],
  sparse![488; 0 => -1, 1 => 3, 3 => -1, 7 => 1, 60 => 1, 121 => -1, 243 => 3, 487 => -1],
  sparse![488; 0 => -1, 1 => 2, 7 => 1, 60 => 1, 243 => 2, 487 => -1],
  sparse![488; 0 => 1, 3 => 2, 7 => -1, 60 => -1, 121 => 2, 487 => 1],
  sparse![488; 0 => 1, 1 => -1, 3 => 3, 7 => -1, 60 => -1, 121 => 3, 243 => -1, 487 => 1],
  sparse![488; 0 => 1, 1 => -2, 3 => 4, 7 => -1, 60 => -1, 121 => 4, 243 => -2, 487 => 1],
  sparse![488; 0 => 1, 1 => 1, 3 => -1, 7 => 1, 60 => -1, 121 => 1, 243 => 3, 487 => -1],
  sparse![488; 0 => 1, 7 => 1, 60 => -1, 121 => 2, 243 => 2, 487 => -1],
  sparse![488; 0 => 1, 1 => -1, 3 => 1, 7 => 1, 60 => -1, 121 => 3, 243 => 1, 487 => -1],
]
```

### Level 489

dim S₂ = **53**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **109**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 490

dim S₂ = **69**; eta rank = **61**; full eta basis = **NO**; Sturm bound B = **168**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![490; 0 => 1, 1 => 1, 6 => 1, 13 => 1],
  sparse![490; 4 => 1, 9 => 1, 34 => 1, 69 => 1],
  sparse![490; 6 => 1, 13 => 1, 48 => 1, 97 => 1],
  sparse![490; 34 => 1, 69 => 1, 244 => 1, 489 => 1],
  sparse![490; 0 => 2, 34 => 2],
  sparse![490; 0 => 1, 4 => 1, 6 => 1, 34 => 1],
  sparse![490; 4 => 2, 6 => 2],
  sparse![490; 1 => 2, 69 => 2],
  sparse![490; 1 => 1, 9 => 1, 13 => 1, 69 => 1],
  sparse![490; 9 => 2, 13 => 2],
  sparse![490; 6 => 2, 244 => 2],
  sparse![490; 6 => 1, 34 => 1, 48 => 1, 244 => 1],
  sparse![490; 34 => 2, 48 => 2],
  sparse![490; 13 => 2, 489 => 2],
  sparse![490; 13 => 1, 69 => 1, 97 => 1, 489 => 1],
  sparse![490; 69 => 2, 97 => 2],
  sparse![490; 0 => 1, 4 => 2, 9 => -1, 13 => 1, 34 => -1, 69 => 2],
  sparse![490; 6 => 1, 34 => 2, 69 => -1, 97 => 1, 244 => -1, 489 => 2],
  sparse![490; 0 => 2, 1 => -1, 6 => 1, 13 => 1, 48 => -1, 97 => 2],
  sparse![490; 0 => 1, 6 => 1, 13 => 1, 97 => 1],
  sparse![490; 1 => 1, 6 => 1, 13 => 1, 48 => 1],
  sparse![490; 0 => -1, 1 => 2, 6 => 1, 13 => 1, 48 => 2, 97 => -1],
  sparse![490; 4 => 2, 9 => -1, 34 => 1, 69 => 1, 244 => -1, 489 => 2],
  sparse![490; 4 => 1, 34 => 1, 69 => 1, 489 => 1],
  sparse![490; 9 => 1, 34 => 1, 69 => 1, 244 => 1],
  sparse![490; 4 => -1, 9 => 2, 34 => 1, 69 => 1, 244 => 2, 489 => -1],
  sparse![490; 0 => 1, 6 => 1, 34 => 1, 244 => 1],
  sparse![490; 4 => 1, 6 => 2, 244 => 1],
  sparse![490; 0 => 1, 34 => 2, 48 => 1],
  sparse![490; 4 => 1, 6 => 1, 34 => 1, 48 => 1],
  sparse![490; 1 => 1, 13 => 1, 69 => 1, 489 => 1],
  sparse![490; 9 => 1, 13 => 2, 489 => 1],
  sparse![490; 1 => 1, 69 => 2, 97 => 1],
  sparse![490; 9 => 1, 13 => 1, 69 => 1, 97 => 1],
  sparse![490; 0 => 2, 1 => -1, 6 => 2, 13 => -1, 34 => -1, 69 => 2, 244 => -1, 489 => 2],
  sparse![490; 4 => -1, 6 => 2, 9 => 2, 13 => -1, 34 => -1, 48 => 2, 69 => 2, 97 => -1],
  sparse![490; 0 => 1, 48 => -1, 69 => 2, 97 => 2],
  sparse![490; 1 => 1, 4 => 1, 6 => 1, 9 => -1, 13 => -1, 34 => -1, 48 => -1, 69 => 3, 97 => 2],
  sparse![490; 0 => -1, 1 => 2, 4 => 1, 6 => 1, 9 => -1, 13 => -1, 34 => -1, 69 => 3, 97 => 1],
  sparse![490; 1 => 1, 6 => 1, 13 => -1, 34 => -1, 48 => -1, 69 => 3, 97 => 2, 244 => 1, 489 => -1],
  sparse![490; 0 => -1, 1 => 2, 48 => 1, 69 => 2],
  sparse![490; 0 => -1, 1 => 2, 6 => 1, 13 => -1, 34 => -1, 69 => 3, 97 => 1, 244 => 1, 489 => -1],
  sparse![490; 0 => 2, 1 => -1, 6 => -1, 13 => 2, 69 => 1, 244 => 1],
  sparse![490; 0 => 1, 13 => 1, 34 => -1, 69 => 2, 244 => 2, 489 => -1],
  sparse![490; 0 => 1, 6 => -1, 13 => 2, 34 => 1, 244 => -1, 489 => 2],
  sparse![490; 1 => 1, 6 => -1, 13 => 2, 34 => 1, 48 => 1, 97 => -1, 244 => -1, 489 => 2],
  sparse![490; 0 => -1, 1 => 2, 4 => 1, 6 => 1, 9 => -1, 34 => -1, 69 => 2, 489 => 1],
  sparse![490; 4 => 2, 9 => -1, 13 => 1, 34 => -1, 48 => 1, 69 => 2],
  sparse![490; 0 => 1, 1 => -1, 4 => -1, 6 => -1, 9 => 2, 13 => 2, 34 => 1, 97 => 1],
  sparse![490; 4 => -1, 6 => -1, 9 => 2, 13 => 2, 34 => 1, 48 => 1],
  sparse![490; 0 => 1, 1 => -1, 6 => -1, 9 => 1, 13 => 3, 34 => 1, 69 => -1, 244 => -1, 489 => 2],
  sparse![490; 6 => -1, 9 => 1, 13 => 3, 34 => 1, 48 => 1, 69 => -1, 97 => -1, 244 => -1, 489 => 2],
  sparse![490; 0 => 1, 1 => -1, 4 => -1, 6 => -1, 9 => 2, 13 => 3, 34 => 1, 69 => -1, 489 => 1],
  sparse![490; 4 => -1, 6 => -1, 9 => 2, 13 => 3, 34 => 1, 48 => 1, 69 => -1, 97 => -1, 489 => 1],
  sparse![490; 0 => -1, 1 => 2, 6 => 1, 34 => -1, 69 => 2, 244 => 1],
  sparse![490; 4 => 1, 6 => -1, 13 => 2, 48 => 2, 69 => 1, 97 => -1],
  sparse![490; 4 => 1, 6 => 1, 34 => -1, 48 => -1, 69 => 2, 97 => 2],
  sparse![490; 6 => 1, 9 => 1, 34 => -1, 48 => -1, 69 => 2, 97 => 2, 244 => 1, 489 => -1],
  sparse![490; 4 => 1, 13 => 2, 244 => -1, 489 => 2],
  sparse![490; 4 => -1, 9 => 2, 13 => 2, 244 => 1],
  sparse![490; 0 => -1, 1 => 2, 6 => 2, 13 => -1, 34 => 1, 489 => 1],
]
```

### Level 491

dim S₂ = **41**; eta rank = **1**; full eta basis = **NO**; Sturm bound B = **82**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![491; 0 => 2, 490 => 2],
]
```

### Level 492

dim S₂ = **79**; eta rank = **67**; full eta basis = **NO**; Sturm bound B = **168**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![492; 0 => 1, 2 => 1, 40 => 1, 122 => 1],
  sparse![492; 1 => 1, 5 => 1, 81 => 1, 245 => 1],
  sparse![492; 3 => 1, 11 => 1, 163 => 1, 491 => 1],
  sparse![492; 0 => 2, 1 => -1, 3 => 1, 40 => -2, 81 => 5, 163 => -1],
  sparse![492; 0 => 1, 1 => -1, 3 => 2, 40 => -1, 81 => 5, 163 => -2],
  sparse![492; 0 => 1, 1 => 2, 3 => -1, 40 => -1, 81 => 2, 163 => 1],
  sparse![492; 1 => 2, 81 => 2],
  sparse![492; 0 => -1, 1 => 2, 3 => 1, 40 => 1, 81 => 2, 163 => -1],
  sparse![492; 0 => -1, 1 => 5, 3 => -2, 40 => 1, 81 => -1, 163 => 2],
  sparse![492; 0 => -2, 1 => 5, 3 => -1, 40 => 2, 81 => -1, 163 => 1],
  sparse![492; 2 => 2, 5 => -1, 11 => 1, 122 => -2, 245 => 5, 491 => -1],
  sparse![492; 2 => 1, 5 => -1, 11 => 2, 122 => -1, 245 => 5, 491 => -2],
  sparse![492; 2 => 1, 5 => 2, 11 => -1, 122 => -1, 245 => 2, 491 => 1],
  sparse![492; 5 => 2, 245 => 2],
  sparse![492; 2 => -1, 5 => 2, 11 => 1, 122 => 1, 245 => 2, 491 => -1],
  sparse![492; 2 => -1, 5 => 5, 11 => -2, 122 => 1, 245 => -1, 491 => 2],
  sparse![492; 2 => -2, 5 => 5, 11 => -1, 122 => 2, 245 => -1, 491 => 1],
  sparse![492; 0 => 3, 1 => -1, 2 => -1, 5 => 1, 40 => -1, 81 => 1, 122 => 3, 245 => -1],
  sparse![492; 1 => 2, 2 => 1, 5 => -1, 40 => -1, 81 => 1, 122 => 2],
  sparse![492; 0 => 2, 2 => -1, 5 => 1, 40 => 1, 81 => -1, 245 => 2],
  sparse![492; 0 => -1, 1 => 3, 2 => 1, 5 => -1, 40 => 1, 81 => -1, 122 => -1, 245 => 3],
  sparse![492; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 40 => 1, 245 => 1],
  sparse![492; 1 => 1, 2 => 1, 40 => 3, 81 => -2, 122 => -2, 245 => 3],
  sparse![492; 0 => 1, 5 => 1, 40 => -2, 81 => 3, 122 => 3, 245 => -2],
  sparse![492; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 81 => 1, 122 => 1],
  sparse![492; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 40 => 3, 81 => -1, 122 => -1, 245 => 1],
  sparse![492; 0 => -1, 1 => 1, 2 => 2, 81 => 2, 122 => 1, 245 => -1],
  sparse![492; 0 => 1, 1 => -1, 5 => 2, 40 => 2, 122 => -1, 245 => 1],
  sparse![492; 0 => 1, 1 => -1, 2 => -1, 5 => 3, 40 => -1, 81 => 3, 122 => 1, 245 => -1],
  sparse![492; 1 => 3, 3 => -1, 5 => -1, 11 => 1, 81 => -1, 163 => 1, 245 => 3, 491 => -1],
  sparse![492; 3 => 2, 5 => 1, 11 => -1, 81 => -1, 163 => 1, 245 => 2],
  sparse![492; 1 => 2, 5 => -1, 11 => 1, 81 => 1, 163 => -1, 491 => 2],
  sparse![492; 1 => -1, 3 => 3, 5 => 1, 11 => -1, 81 => 1, 163 => -1, 245 => -1, 491 => 3],
  sparse![492; 1 => -2, 3 => 3, 5 => 3, 11 => -2, 81 => 1, 491 => 1],
  sparse![492; 3 => 1, 5 => 1, 81 => 3, 163 => -2, 245 => -2, 491 => 3],
  sparse![492; 1 => 1, 11 => 1, 81 => -2, 163 => 3, 245 => 3, 491 => -2],
  sparse![492; 1 => 3, 3 => -2, 5 => -2, 11 => 3, 163 => 1, 245 => 1],
  sparse![492; 1 => -1, 3 => 1, 5 => 3, 11 => -1, 81 => 3, 163 => -1, 245 => -1, 491 => 1],
  sparse![492; 1 => -1, 3 => 1, 5 => 2, 163 => 2, 245 => 1, 491 => -1],
  sparse![492; 1 => 1, 3 => -1, 11 => 2, 81 => 2, 245 => -1, 491 => 1],
  sparse![492; 0 => 1, 1 => -2, 2 => -3, 3 => 1, 5 => 8, 11 => -3, 40 => 3, 81 => -1, 122 => -1, 245 => 1],
  sparse![492; 0 => 2, 1 => -1, 2 => -1, 3 => 1, 5 => 1, 40 => 1, 81 => -1, 163 => 2, 245 => 1, 491 => -1],
  sparse![492; 0 => 1, 1 => -1, 3 => 2, 5 => 1, 11 => -1, 40 => 2, 81 => -1, 122 => -1, 163 => 1, 245 => 1],
  sparse![492; 2 => -1, 3 => 1, 5 => 3, 11 => -1, 40 => 1, 81 => -3, 122 => -2, 163 => 3, 245 => 6, 491 => -3],
  sparse![492; 2 => 1, 3 => 1, 40 => -1, 122 => 2, 163 => 2, 491 => -1],
  sparse![492; 0 => 1, 1 => -2, 2 => -1, 3 => 2, 5 => 3, 11 => -1, 40 => -1, 81 => 1, 122 => 1, 163 => 1],
  sparse![492; 0 => 1, 1 => -1, 2 => -1, 3 => 2, 5 => 2, 11 => -1, 40 => -1, 81 => 2, 122 => 1, 163 => 1, 245 => -1],
  sparse![492; 0 => 1, 1 => -3, 2 => -2, 3 => 3, 5 => 6, 11 => -3, 122 => -1, 163 => 1, 245 => 3, 491 => -1],
  sparse![492; 0 => -1, 1 => 1, 2 => 1, 3 => 1, 40 => 1, 81 => -2, 122 => -1, 163 => 2, 245 => 3, 491 => -1],
  sparse![492; 0 => -1, 1 => 2, 2 => 1, 3 => 1, 5 => -1, 40 => 1, 81 => -1, 122 => -1, 163 => 2, 245 => 2, 491 => -1],
  sparse![492; 0 => -1, 2 => 2, 3 => 2, 11 => -1, 122 => 1, 163 => 1],
  sparse![492; 0 => 3, 1 => -3, 2 => -3, 3 => 1, 5 => 6, 11 => -2, 40 => 1, 122 => -1, 245 => 3, 491 => -1],
  sparse![492; 0 => 1, 1 => 1, 3 => -1, 11 => 1, 40 => 2, 81 => -2, 122 => -1, 163 => 1, 245 => 3, 491 => -1],
  sparse![492; 0 => 1, 1 => 2, 3 => -1, 5 => -1, 11 => 1, 40 => 2, 81 => -1, 122 => -1, 163 => 1, 245 => 2, 491 => -1],
  sparse![492; 0 => 2, 2 => -1, 3 => -1, 11 => 2, 40 => 1, 491 => 1],
  sparse![492; 0 => 1, 2 => -1, 5 => 3, 11 => -1, 40 => 3, 81 => -3, 122 => -3, 163 => 1, 245 => 6, 491 => -2],
  sparse![492; 0 => 2, 1 => -2, 2 => -1, 3 => 1, 5 => 3, 11 => -1, 40 => 1, 81 => 1, 163 => -1, 491 => 1],
  sparse![492; 0 => 1, 11 => 1, 40 => 2, 122 => -1, 163 => -1, 491 => 2],
  sparse![492; 0 => 1, 1 => -2, 2 => -2, 3 => 1, 5 => 6, 11 => -2, 81 => 2, 122 => -1, 245 => 2, 491 => -1],
  sparse![492; 0 => -1, 1 => 2, 2 => 1, 3 => -1, 11 => 1, 40 => 1, 122 => -1, 163 => 1, 245 => 2, 491 => -1],
  sparse![492; 0 => 1, 1 => 1, 2 => -1, 3 => -1, 5 => 1, 11 => 1, 40 => -1, 81 => 1, 122 => 1, 163 => 1, 245 => 1, 491 => -1],
  sparse![492; 0 => 1, 1 => -1, 2 => -2, 5 => 5, 11 => -1, 81 => -1, 122 => -1, 163 => 1, 245 => 5, 491 => -2],
  sparse![492; 0 => 1, 2 => -2, 5 => 4, 11 => -1, 122 => -1, 163 => 1, 245 => 4, 491 => -2],
  sparse![492; 0 => -1, 1 => 4, 2 => 1, 3 => -2, 5 => -2, 11 => 2, 40 => 1, 81 => -2, 122 => -1, 163 => 2, 245 => 4, 491 => -2],
  sparse![492; 0 => -1, 1 => 3, 3 => -1, 5 => 1, 40 => 2, 81 => -3, 122 => -3, 163 => 2, 245 => 7, 491 => -3],
  sparse![492; 1 => 1, 2 => -1, 3 => -1, 5 => 2, 11 => 1, 40 => 1, 81 => -2, 122 => -2, 163 => 1, 245 => 5, 491 => -1],
  sparse![492; 0 => 1, 1 => -2, 2 => -1, 3 => 1, 5 => 5, 11 => -2, 40 => -1, 81 => 1, 122 => 1, 245 => 2, 491 => -1],
]
```

### Level 493

dim S₂ = **43**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **90**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 494

dim S₂ = **67**; eta rank = **18**; full eta basis = **NO**; Sturm bound B = **140**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![494; 0 => 3, 1 => -1, 18 => -1, 37 => 3],
  sparse![494; 0 => -1, 1 => 3, 18 => 3, 37 => -1],
  sparse![494; 12 => 3, 25 => -1, 246 => -1, 493 => 3],
  sparse![494; 12 => -1, 25 => 3, 246 => 3, 493 => -1],
  sparse![494; 12 => 1, 18 => 1, 25 => 1, 37 => 1],
  sparse![494; 0 => 2, 1 => -1, 12 => 1, 37 => 1, 246 => -1, 493 => 2],
  sparse![494; 0 => 1, 12 => 2, 18 => -1, 25 => -1, 37 => 2, 493 => 1],
  sparse![494; 0 => 1, 18 => 2, 25 => 1, 37 => -1, 246 => -1, 493 => 2],
  sparse![494; 0 => 2, 1 => -1, 12 => -1, 18 => 1, 25 => 2, 493 => 1],
  sparse![494; 0 => -1, 1 => 2, 12 => 2, 18 => 2, 25 => -1, 37 => -1, 246 => -1, 493 => 2],
  sparse![494; 1 => 1, 12 => 1, 18 => 1, 493 => 1],
  sparse![494; 0 => 1, 25 => 1, 37 => 1, 246 => 1],
  sparse![494; 0 => 2, 1 => -1, 12 => -1, 18 => -1, 25 => 2, 37 => 2, 246 => 2, 493 => -1],
  sparse![494; 0 => -1, 1 => 2, 12 => 2, 25 => -1, 37 => 1, 246 => 1],
  sparse![494; 1 => 1, 12 => 1, 18 => -1, 37 => 2, 246 => 2, 493 => -1],
  sparse![494; 1 => 1, 12 => -1, 18 => 2, 25 => 2, 37 => -1, 246 => 1],
  sparse![494; 0 => -1, 1 => 2, 18 => 1, 25 => 1, 246 => 2, 493 => -1],
  sparse![494; 0 => 1, 1 => 1, 246 => 1, 493 => 1],
]
```

### Level 495

dim S₂ = **65**; eta rank = **44**; full eta basis = **NO**; Sturm bound B = **144**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![495; 0 => 2, 10 => 2],
  sparse![495; 2 => 2, 32 => 2],
  sparse![495; 4 => 2, 54 => 2],
  sparse![495; 8 => 2, 98 => 2],
  sparse![495; 14 => 2, 164 => 2],
  sparse![495; 44 => 2, 494 => 2],
  sparse![495; 0 => 1, 2 => 1, 4 => 1, 14 => 1],
  sparse![495; 2 => 1, 8 => 1, 14 => 1, 44 => 1],
  sparse![495; 10 => 1, 32 => 1, 54 => 1, 164 => 1],
  sparse![495; 32 => 1, 98 => 1, 164 => 1, 494 => 1],
  sparse![495; 0 => 1, 2 => 1, 10 => 1, 32 => 1],
  sparse![495; 2 => 1, 8 => 1, 32 => 1, 98 => 1],
  sparse![495; 4 => 1, 14 => 1, 54 => 1, 164 => 1],
  sparse![495; 14 => 1, 44 => 1, 164 => 1, 494 => 1],
  sparse![495; 0 => 1, 4 => 1, 10 => 1, 54 => 1],
  sparse![495; 2 => 1, 14 => 1, 32 => 1, 164 => 1],
  sparse![495; 8 => 1, 44 => 1, 98 => 1, 494 => 1],
  sparse![495; 0 => 1, 8 => 1, 10 => 1, 98 => 1],
  sparse![495; 4 => 1, 44 => 1, 54 => 1, 494 => 1],
  sparse![495; 0 => -1, 2 => 2, 4 => 2, 10 => 2, 14 => -1, 32 => -1, 54 => -1, 164 => 2],
  sparse![495; 2 => 1, 4 => 1, 32 => 1, 54 => 1],
  sparse![495; 0 => 1, 10 => 1, 14 => 1, 164 => 1],
  sparse![495; 0 => 2, 2 => -1, 4 => -1, 10 => -1, 14 => 2, 32 => 2, 54 => 2, 164 => -1],
  sparse![495; 2 => -1, 8 => 2, 14 => 2, 32 => 2, 44 => -1, 98 => -1, 164 => -1, 494 => 2],
  sparse![495; 8 => 1, 14 => 1, 98 => 1, 164 => 1],
  sparse![495; 2 => 1, 32 => 1, 44 => 1, 494 => 1],
  sparse![495; 2 => 2, 8 => -1, 14 => -1, 32 => -1, 44 => 2, 98 => 2, 164 => 2, 494 => -1],
  sparse![495; 2 => -1, 8 => 3, 14 => 1, 44 => -1, 494 => 2],
  sparse![495; 8 => 2, 32 => 1, 98 => -1, 164 => -1, 494 => 3],
  sparse![495; 0 => -1, 2 => 1, 4 => 3, 10 => 2, 14 => -1],
  sparse![495; 4 => 2, 10 => 3, 32 => -1, 54 => -1, 164 => 1],
  sparse![495; 0 => 1, 8 => 1, 54 => -1, 164 => 4, 494 => -1],
  sparse![495; 4 => 1, 10 => -1, 32 => 4, 44 => 1, 98 => -1],
  sparse![495; 8 => 1, 10 => 1, 44 => 1, 54 => 1],
  sparse![495; 4 => 1, 8 => 1, 54 => 1, 98 => 1],
  sparse![495; 0 => 1, 2 => -1, 4 => -1, 8 => 1, 10 => 1, 14 => 3, 32 => -1, 44 => -1, 54 => -1, 98 => 1, 164 => 3, 494 => -1],
  sparse![495; 0 => 1, 10 => 1, 44 => 1, 494 => 1],
  sparse![495; 14 => 2, 32 => 2],
  sparse![495; 2 => 2, 164 => 2],
  sparse![495; 0 => -1, 2 => 3, 4 => 1, 8 => -1, 10 => -1, 14 => -1, 32 => 3, 44 => 1, 54 => 1, 98 => -1, 164 => -1, 494 => 1],
  sparse![495; 0 => 1, 4 => 1, 98 => 1, 494 => 1],
  sparse![495; 4 => -1, 10 => 1, 14 => 4, 44 => -1, 98 => 1],
  sparse![495; 0 => 2, 10 => -1, 32 => 1, 54 => 3, 164 => -1],
  sparse![495; 0 => 3, 2 => -1, 4 => -1, 14 => 1, 54 => 2],
]
```

### Level 496

dim S₂ = **59**; eta rank = **39**; full eta basis = **NO**; Sturm bound B = **128**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![496; 0 => 1, 1 => 1, 30 => 1, 61 => 1],
  sparse![496; 1 => 1, 3 => 1, 61 => 1, 123 => 1],
  sparse![496; 3 => 1, 7 => 1, 123 => 1, 247 => 1],
  sparse![496; 7 => 1, 15 => 1, 247 => 1, 495 => 1],
  sparse![496; 0 => -1, 1 => 4, 3 => -1, 30 => -1, 61 => 4, 123 => -1],
  sparse![496; 1 => -1, 3 => 4, 7 => -1, 61 => -1, 123 => 4, 247 => -1],
  sparse![496; 3 => -1, 7 => 4, 15 => -1, 123 => -1, 247 => 4, 495 => -1],
  sparse![496; 1 => -1, 3 => 3, 61 => 3, 123 => -1],
  sparse![496; 0 => 1, 1 => -1, 3 => 3, 7 => -1, 30 => 1, 61 => -1, 123 => 3, 247 => -1],
  sparse![496; 0 => 1, 7 => 1, 30 => 1, 247 => 1],
  sparse![496; 0 => -1, 1 => 2, 3 => 2, 7 => -1, 30 => -1, 61 => 2, 123 => 2, 247 => -1],
  sparse![496; 0 => -1, 1 => 3, 3 => -1, 7 => 1, 30 => -1, 61 => 3, 123 => -1, 247 => 1],
  sparse![496; 1 => 3, 3 => -1, 61 => -1, 123 => 3],
  sparse![496; 3 => -1, 7 => 3, 123 => 3, 247 => -1],
  sparse![496; 1 => 1, 3 => -1, 7 => 3, 15 => -1, 61 => 1, 123 => -1, 247 => 3, 495 => -1],
  sparse![496; 1 => -1, 3 => 2, 7 => 2, 15 => -1, 61 => -1, 123 => 2, 247 => 2, 495 => -1],
  sparse![496; 1 => -1, 3 => 3, 7 => -1, 15 => 1, 61 => -1, 123 => 3, 247 => -1, 495 => 1],
  sparse![496; 3 => 3, 7 => -1, 123 => -1, 247 => 3],
  sparse![496; 7 => 4, 15 => -2, 123 => 2, 247 => -2, 495 => 2],
  sparse![496; 3 => -2, 7 => 7, 15 => -3, 247 => 1, 495 => 1],
  sparse![496; 0 => -1, 1 => 4, 3 => -1, 30 => 1, 61 => -1, 123 => 1, 247 => -1, 495 => 2],
  sparse![496; 0 => -1, 1 => 3, 3 => -2, 7 => 3, 15 => -1, 30 => 1, 61 => -2, 123 => 4, 247 => -2, 495 => 1],
  sparse![496; 0 => -1, 1 => 1, 3 => 2, 7 => 1, 15 => -1, 30 => 1, 495 => 1],
  sparse![496; 0 => -1, 1 => 2, 3 => -2, 7 => 5, 15 => -2, 30 => 1, 61 => 1],
  sparse![496; 0 => 1, 3 => -1, 7 => 3, 15 => -1, 30 => -1, 61 => 1, 123 => 3, 247 => -2, 495 => 1],
  sparse![496; 0 => 1, 1 => -2, 3 => 3, 7 => 1, 15 => -1, 30 => -1, 61 => 3, 123 => -1, 495 => 1],
  sparse![496; 1 => 1, 7 => 1, 61 => -3, 123 => 8, 247 => -3],
  sparse![496; 0 => 1, 1 => -1, 3 => 1, 7 => 2, 15 => -1, 30 => 1, 61 => -1, 123 => 1, 247 => 2, 495 => -1],
  sparse![496; 1 => -3, 3 => 8, 7 => -3, 61 => 1, 247 => 1],
  sparse![496; 3 => -1, 7 => 4, 15 => -1, 123 => 1, 247 => -2, 495 => 3],
  sparse![496; 0 => -2, 1 => 4, 30 => 2, 61 => -2, 123 => 2],
  sparse![496; 0 => 1, 1 => 1, 30 => -1, 61 => 2, 247 => -1, 495 => 2],
  sparse![496; 0 => 1, 1 => -1, 3 => -1, 7 => 5, 15 => -2, 30 => -1, 61 => 4, 123 => -1],
  sparse![496; 0 => -1, 1 => 2, 7 => 2, 15 => -1, 30 => -1, 61 => 2, 247 => 2, 495 => -1],
  sparse![496; 0 => -2, 1 => 5, 3 => -1, 7 => -1, 15 => 1, 123 => -1, 247 => 4, 495 => -1],
  sparse![496; 0 => -1, 1 => 3, 3 => -1, 15 => 1, 30 => 1, 61 => -2, 123 => 3, 247 => 1, 495 => -1],
  sparse![496; 0 => -1, 1 => 1, 3 => 3, 7 => -2, 15 => 1, 30 => 1, 123 => -1, 247 => 3, 495 => -1],
  sparse![496; 7 => 1, 15 => 1, 30 => 2, 61 => -1, 247 => 2, 495 => -1],
  sparse![496; 0 => 1, 15 => 1, 30 => -1, 61 => 1, 123 => 2, 247 => 1, 495 => -1],
]
```

### Level 497

dim S₂ = **47**; eta rank = **3**; full eta basis = **NO**; Sturm bound B = **96**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![497; 0 => 2, 70 => 2],
  sparse![497; 6 => 2, 496 => 2],
  sparse![497; 0 => 1, 6 => 1, 70 => 1, 496 => 1],
]
```

### Level 498

dim S₂ = **81**; eta rank = **14**; full eta basis = **NO**; Sturm bound B = **168**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![498; 0 => 2, 82 => 2],
  sparse![498; 1 => 2, 165 => 2],
  sparse![498; 2 => 2, 248 => 2],
  sparse![498; 5 => 2, 497 => 2],
  sparse![498; 0 => 1, 2 => 1, 82 => 1, 248 => 1],
  sparse![498; 1 => 1, 5 => 1, 165 => 1, 497 => 1],
  sparse![498; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 82 => -1, 165 => 1, 248 => 3, 497 => -1],
  sparse![498; 1 => 1, 2 => 2, 5 => -1, 165 => 1, 248 => 2, 497 => -1],
  sparse![498; 0 => 2, 1 => -1, 5 => 1, 82 => 2, 165 => -1, 497 => 1],
  sparse![498; 0 => 3, 1 => -1, 2 => -1, 5 => 1, 82 => 3, 165 => -1, 248 => -1, 497 => 1],
  sparse![498; 0 => 1, 1 => -1, 2 => -1, 5 => 3, 82 => 1, 165 => -1, 248 => -1, 497 => 3],
  sparse![498; 0 => -1, 1 => 2, 2 => 1, 82 => -1, 165 => 2, 248 => 1],
  sparse![498; 0 => 1, 2 => -1, 5 => 2, 82 => 1, 248 => -1, 497 => 2],
  sparse![498; 0 => -1, 1 => 3, 2 => 1, 5 => -1, 82 => -1, 165 => 3, 248 => 1, 497 => -1],
]
```

### Level 499

dim S₂ = **41**; eta rank = **0**; full eta basis = **NO**; Sturm bound B = **83**.

Empty cuspidal eta-quotient basis; the ambient cusp-form space is nonzero.

`Basis_cuspidal_eta_S2 = []`.

### Level 500

dim S₂ = **61**; eta rank = **49**; full eta basis = **NO**; Sturm bound B = **150**.

`Basis_cuspidal_eta_S2`: **partial cuspidal eta span; not a full cusp-form basis**.

```lean
[
  sparse![500; 1 => 2, 9 => 2],
  sparse![500; 9 => 2, 49 => 2],
  sparse![500; 49 => 2, 249 => 2],
  sparse![500; 1 => 1, 9 => 2, 49 => 1],
  sparse![500; 0 => -1, 1 => 2, 3 => -1, 4 => 2, 19 => 2, 24 => -1, 49 => 2, 99 => -1],
  sparse![500; 0 => -1, 1 => 2, 9 => 2, 24 => 1],
  sparse![500; 0 => -1, 1 => 3, 3 => -1, 9 => 2, 24 => 1, 49 => -1, 99 => 1],
  sparse![500; 1 => -1, 3 => 1, 9 => 6, 19 => -2, 49 => -1, 99 => 1],
  sparse![500; 9 => 1, 49 => 2, 249 => 1],
  sparse![500; 4 => -1, 9 => 2, 19 => -1, 24 => 2, 99 => 2, 124 => -1, 249 => 2, 499 => -1],
  sparse![500; 4 => -1, 9 => 2, 49 => 2, 124 => 1],
  sparse![500; 4 => -1, 9 => 3, 19 => -1, 49 => 2, 124 => 1, 249 => -1, 499 => 1],
  sparse![500; 9 => -1, 19 => 1, 49 => 6, 99 => -2, 249 => -1, 499 => 1],
  sparse![500; 0 => 1, 24 => -1, 49 => 2, 249 => 2],
  sparse![500; 1 => 2, 3 => -1, 4 => 1, 9 => -1, 19 => 1, 99 => 1, 124 => -1, 249 => 3, 499 => -1],
  sparse![500; 0 => -1, 1 => 2, 4 => 1, 9 => -1, 19 => 1, 24 => 1, 124 => -1, 249 => 3, 499 => -1],
  sparse![500; 0 => -1, 1 => 3, 3 => -1, 19 => 1, 24 => 1, 49 => -1, 99 => 1, 249 => 2, 499 => -1],
  sparse![500; 0 => -1, 1 => 3, 3 => -1, 4 => 1, 24 => 1, 49 => -1, 99 => 1, 124 => -1, 249 => 2],
  sparse![500; 0 => 1, 19 => 1, 24 => -1, 49 => 2, 249 => 2, 499 => -1],
  sparse![500; 3 => 1, 4 => 1, 49 => 2, 99 => -1, 124 => -1, 249 => 2],
  sparse![500; 1 => 2, 3 => -1, 4 => -1, 9 => 2, 99 => 1, 124 => 1],
  sparse![500; 0 => -1, 1 => 2, 9 => 2, 19 => -1, 24 => 1, 499 => 1],
  sparse![500; 1 => 2, 9 => 1, 249 => 1],
  sparse![500; 1 => 2, 249 => 2],
  sparse![500; 1 => 1, 9 => 1, 49 => 1, 249 => 1],
  sparse![500; 1 => 1, 49 => 1, 249 => 2],
  sparse![500; 0 => -1, 1 => 2, 3 => -1, 4 => 1, 19 => 1, 24 => 1, 99 => 1, 124 => -1, 249 => 2, 499 => -1],
  sparse![500; 0 => -1, 1 => 2, 3 => -1, 4 => 1, 19 => 2, 24 => -1, 49 => 2, 99 => -1, 124 => 1],
  sparse![500; 0 => -1, 1 => 2, 3 => -1, 4 => 1, 9 => 1, 19 => 1, 24 => -1, 49 => 2, 99 => -1, 124 => 1, 249 => -1, 499 => 1],
  sparse![500; 0 => -1, 1 => 2, 3 => -1, 4 => 2, 9 => -3, 19 => 3, 24 => -1, 49 => 6, 99 => -3, 249 => -1, 499 => 1],
  sparse![500; 0 => -1, 1 => 2, 3 => -1, 4 => 2, 9 => -2, 19 => 2, 24 => -1, 49 => 2, 99 => -1, 249 => 2],
  sparse![500; 0 => -1, 1 => 2, 3 => -1, 4 => 2, 9 => -2, 19 => 3, 24 => -1, 49 => 2, 99 => -1, 249 => 2, 499 => -1],
  sparse![500; 0 => -1, 1 => 2, 4 => -1, 9 => 2, 19 => -1, 24 => 3, 49 => -2, 99 => 2, 124 => -1, 249 => 2, 499 => -1],
  sparse![500; 0 => -1, 1 => 2, 4 => -1, 9 => 2, 24 => 1, 124 => 1],
  sparse![500; 0 => -1, 1 => 2, 4 => -1, 9 => 3, 19 => -1, 24 => 1, 124 => 1, 249 => -1, 499 => 1],
  sparse![500; 0 => -1, 1 => 2, 9 => -1, 19 => 1, 24 => 1, 49 => 4, 99 => -2, 249 => -1, 499 => 1],
  sparse![500; 0 => -1, 1 => 3, 3 => -1, 4 => -1, 9 => 2, 19 => -1, 24 => 3, 49 => -3, 99 => 3, 124 => -1, 249 => 2, 499 => -1],
  sparse![500; 0 => -1, 1 => 3, 3 => -1, 4 => -1, 9 => 2, 24 => 1, 49 => -1, 99 => 1, 124 => 1],
  sparse![500; 0 => -1, 1 => 3, 3 => -1, 4 => -1, 9 => 3, 19 => -1, 24 => 1, 49 => -1, 99 => 1, 124 => 1, 249 => -1, 499 => 1],
  sparse![500; 0 => -1, 1 => 3, 3 => -1, 9 => -1, 19 => 1, 24 => 1, 49 => 3, 99 => -1, 249 => -1, 499 => 1],
  sparse![500; 1 => -1, 3 => 1, 4 => -1, 9 => 6, 19 => -3, 24 => 2, 49 => -3, 99 => 3, 124 => -1, 249 => 2, 499 => -1],
  sparse![500; 1 => -1, 3 => 1, 4 => -1, 9 => 6, 19 => -2, 49 => -1, 99 => 1, 124 => 1],
  sparse![500; 1 => -1, 3 => 1, 4 => -1, 9 => 7, 19 => -3, 49 => -1, 99 => 1, 124 => 1, 249 => -1, 499 => 1],
  sparse![500; 1 => -1, 3 => 1, 9 => 3, 19 => -1, 49 => 3, 99 => -1, 249 => -1, 499 => 1],
  sparse![500; 1 => -1, 3 => 1, 9 => 4, 19 => -1, 49 => -1, 99 => 1, 249 => 2, 499 => -1],
  sparse![500; 3 => 1, 4 => -1, 9 => 2, 19 => -1, 24 => 2, 99 => 1, 124 => -1, 249 => 2, 499 => -1],
  sparse![500; 3 => 1, 4 => -1, 9 => 2, 49 => 2, 99 => -1, 124 => 1],
  sparse![500; 1 => 1, 4 => -1, 9 => 2, 19 => -1, 24 => 2, 49 => -1, 99 => 2, 124 => -1, 249 => 2, 499 => -1],
  sparse![500; 1 => 1, 9 => -1, 19 => 1, 49 => 5, 99 => -2, 249 => -1, 499 => 1],
]
```
