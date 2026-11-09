module

public import WeightTwoCusps

/-! # Dimension and empty-basis regression coverage for every level 1 through 500

Expected dimensions come from HasEtaQuotientBasis/TABLE.md. Importing the root
also checks all 99 full eta bases and all exported supporting forms. -/

public section
noncomputable section
namespace WeightTwoCusps.LevelRangeTests

theorem level_1_dimension : Module.finrank ℂ (gamma0CuspForms 1) = 0 := by
  cusp_basis

example : Module.Basis (Fin 0) ℂ (gamma0CuspForms 1) := cuspFormBasis ![]

theorem level_2_dimension : Module.finrank ℂ (gamma0CuspForms 2) = 0 := by
  cusp_basis

example : Module.Basis (Fin 0) ℂ (gamma0CuspForms 2) := cuspFormBasis ![]

theorem level_3_dimension : Module.finrank ℂ (gamma0CuspForms 3) = 0 := by
  cusp_basis

example : Module.Basis (Fin 0) ℂ (gamma0CuspForms 3) := cuspFormBasis ![]

theorem level_4_dimension : Module.finrank ℂ (gamma0CuspForms 4) = 0 := by
  cusp_basis

example : Module.Basis (Fin 0) ℂ (gamma0CuspForms 4) := cuspFormBasis ![]

theorem level_5_dimension : Module.finrank ℂ (gamma0CuspForms 5) = 0 := by
  cusp_basis

example : Module.Basis (Fin 0) ℂ (gamma0CuspForms 5) := cuspFormBasis ![]

theorem level_6_dimension : Module.finrank ℂ (gamma0CuspForms 6) = 0 := by
  cusp_basis

example : Module.Basis (Fin 0) ℂ (gamma0CuspForms 6) := cuspFormBasis ![]

theorem level_7_dimension : Module.finrank ℂ (gamma0CuspForms 7) = 0 := by
  cusp_basis

example : Module.Basis (Fin 0) ℂ (gamma0CuspForms 7) := cuspFormBasis ![]

theorem level_8_dimension : Module.finrank ℂ (gamma0CuspForms 8) = 0 := by
  cusp_basis

example : Module.Basis (Fin 0) ℂ (gamma0CuspForms 8) := cuspFormBasis ![]

theorem level_9_dimension : Module.finrank ℂ (gamma0CuspForms 9) = 0 := by
  cusp_basis

example : Module.Basis (Fin 0) ℂ (gamma0CuspForms 9) := cuspFormBasis ![]

theorem level_10_dimension : Module.finrank ℂ (gamma0CuspForms 10) = 0 := by
  cusp_basis

example : Module.Basis (Fin 0) ℂ (gamma0CuspForms 10) := cuspFormBasis ![]

theorem level_11_dimension : Module.finrank ℂ (gamma0CuspForms 11) = 1 := by
  cusp_basis

theorem level_12_dimension : Module.finrank ℂ (gamma0CuspForms 12) = 0 := by
  cusp_basis

example : Module.Basis (Fin 0) ℂ (gamma0CuspForms 12) := cuspFormBasis ![]

theorem level_13_dimension : Module.finrank ℂ (gamma0CuspForms 13) = 0 := by
  cusp_basis

example : Module.Basis (Fin 0) ℂ (gamma0CuspForms 13) := cuspFormBasis ![]

theorem level_14_dimension : Module.finrank ℂ (gamma0CuspForms 14) = 1 := by
  cusp_basis

theorem level_15_dimension : Module.finrank ℂ (gamma0CuspForms 15) = 1 := by
  cusp_basis

theorem level_16_dimension : Module.finrank ℂ (gamma0CuspForms 16) = 0 := by
  cusp_basis

example : Module.Basis (Fin 0) ℂ (gamma0CuspForms 16) := cuspFormBasis ![]

theorem level_17_dimension : Module.finrank ℂ (gamma0CuspForms 17) = 1 := by
  cusp_basis

theorem level_18_dimension : Module.finrank ℂ (gamma0CuspForms 18) = 0 := by
  cusp_basis

example : Module.Basis (Fin 0) ℂ (gamma0CuspForms 18) := cuspFormBasis ![]

theorem level_19_dimension : Module.finrank ℂ (gamma0CuspForms 19) = 1 := by
  cusp_basis

theorem level_20_dimension : Module.finrank ℂ (gamma0CuspForms 20) = 1 := by
  cusp_basis

theorem level_21_dimension : Module.finrank ℂ (gamma0CuspForms 21) = 1 := by
  cusp_basis

theorem level_22_dimension : Module.finrank ℂ (gamma0CuspForms 22) = 2 := by
  cusp_basis

theorem level_23_dimension : Module.finrank ℂ (gamma0CuspForms 23) = 2 := by
  cusp_basis

theorem level_24_dimension : Module.finrank ℂ (gamma0CuspForms 24) = 1 := by
  cusp_basis

theorem level_25_dimension : Module.finrank ℂ (gamma0CuspForms 25) = 0 := by
  cusp_basis

example : Module.Basis (Fin 0) ℂ (gamma0CuspForms 25) := cuspFormBasis ![]

theorem level_26_dimension : Module.finrank ℂ (gamma0CuspForms 26) = 2 := by
  cusp_basis

theorem level_27_dimension : Module.finrank ℂ (gamma0CuspForms 27) = 1 := by
  cusp_basis

theorem level_28_dimension : Module.finrank ℂ (gamma0CuspForms 28) = 2 := by
  cusp_basis

theorem level_29_dimension : Module.finrank ℂ (gamma0CuspForms 29) = 2 := by
  cusp_basis

theorem level_30_dimension : Module.finrank ℂ (gamma0CuspForms 30) = 3 := by
  cusp_basis

theorem level_31_dimension : Module.finrank ℂ (gamma0CuspForms 31) = 2 := by
  cusp_basis

theorem level_32_dimension : Module.finrank ℂ (gamma0CuspForms 32) = 1 := by
  cusp_basis

theorem level_33_dimension : Module.finrank ℂ (gamma0CuspForms 33) = 3 := by
  cusp_basis

theorem level_34_dimension : Module.finrank ℂ (gamma0CuspForms 34) = 3 := by
  cusp_basis

theorem level_35_dimension : Module.finrank ℂ (gamma0CuspForms 35) = 3 := by
  cusp_basis

theorem level_36_dimension : Module.finrank ℂ (gamma0CuspForms 36) = 1 := by
  cusp_basis

theorem level_37_dimension : Module.finrank ℂ (gamma0CuspForms 37) = 2 := by
  cusp_basis

theorem level_38_dimension : Module.finrank ℂ (gamma0CuspForms 38) = 4 := by
  cusp_basis

theorem level_39_dimension : Module.finrank ℂ (gamma0CuspForms 39) = 3 := by
  cusp_basis

theorem level_40_dimension : Module.finrank ℂ (gamma0CuspForms 40) = 3 := by
  cusp_basis

theorem level_41_dimension : Module.finrank ℂ (gamma0CuspForms 41) = 3 := by
  cusp_basis

theorem level_42_dimension : Module.finrank ℂ (gamma0CuspForms 42) = 5 := by
  cusp_basis

theorem level_43_dimension : Module.finrank ℂ (gamma0CuspForms 43) = 3 := by
  cusp_basis

theorem level_44_dimension : Module.finrank ℂ (gamma0CuspForms 44) = 4 := by
  cusp_basis

theorem level_45_dimension : Module.finrank ℂ (gamma0CuspForms 45) = 3 := by
  cusp_basis

theorem level_46_dimension : Module.finrank ℂ (gamma0CuspForms 46) = 5 := by
  cusp_basis

theorem level_47_dimension : Module.finrank ℂ (gamma0CuspForms 47) = 4 := by
  cusp_basis

theorem level_48_dimension : Module.finrank ℂ (gamma0CuspForms 48) = 3 := by
  cusp_basis

theorem level_49_dimension : Module.finrank ℂ (gamma0CuspForms 49) = 1 := by
  cusp_basis

theorem level_50_dimension : Module.finrank ℂ (gamma0CuspForms 50) = 2 := by
  cusp_basis

theorem level_51_dimension : Module.finrank ℂ (gamma0CuspForms 51) = 5 := by
  cusp_basis

theorem level_52_dimension : Module.finrank ℂ (gamma0CuspForms 52) = 5 := by
  cusp_basis

theorem level_53_dimension : Module.finrank ℂ (gamma0CuspForms 53) = 4 := by
  cusp_basis

theorem level_54_dimension : Module.finrank ℂ (gamma0CuspForms 54) = 4 := by
  cusp_basis

theorem level_55_dimension : Module.finrank ℂ (gamma0CuspForms 55) = 5 := by
  cusp_basis

theorem level_56_dimension : Module.finrank ℂ (gamma0CuspForms 56) = 5 := by
  cusp_basis

theorem level_57_dimension : Module.finrank ℂ (gamma0CuspForms 57) = 5 := by
  cusp_basis

theorem level_58_dimension : Module.finrank ℂ (gamma0CuspForms 58) = 6 := by
  cusp_basis

theorem level_59_dimension : Module.finrank ℂ (gamma0CuspForms 59) = 5 := by
  cusp_basis

theorem level_60_dimension : Module.finrank ℂ (gamma0CuspForms 60) = 7 := by
  cusp_basis

theorem level_61_dimension : Module.finrank ℂ (gamma0CuspForms 61) = 4 := by
  cusp_basis

theorem level_62_dimension : Module.finrank ℂ (gamma0CuspForms 62) = 7 := by
  cusp_basis

theorem level_63_dimension : Module.finrank ℂ (gamma0CuspForms 63) = 5 := by
  cusp_basis

theorem level_64_dimension : Module.finrank ℂ (gamma0CuspForms 64) = 3 := by
  cusp_basis

theorem level_65_dimension : Module.finrank ℂ (gamma0CuspForms 65) = 5 := by
  cusp_basis

theorem level_66_dimension : Module.finrank ℂ (gamma0CuspForms 66) = 9 := by
  cusp_basis

theorem level_67_dimension : Module.finrank ℂ (gamma0CuspForms 67) = 5 := by
  cusp_basis

theorem level_68_dimension : Module.finrank ℂ (gamma0CuspForms 68) = 7 := by
  cusp_basis

theorem level_69_dimension : Module.finrank ℂ (gamma0CuspForms 69) = 7 := by
  cusp_basis

theorem level_70_dimension : Module.finrank ℂ (gamma0CuspForms 70) = 9 := by
  cusp_basis

theorem level_71_dimension : Module.finrank ℂ (gamma0CuspForms 71) = 6 := by
  cusp_basis

theorem level_72_dimension : Module.finrank ℂ (gamma0CuspForms 72) = 5 := by
  cusp_basis

theorem level_73_dimension : Module.finrank ℂ (gamma0CuspForms 73) = 5 := by
  cusp_basis

theorem level_74_dimension : Module.finrank ℂ (gamma0CuspForms 74) = 8 := by
  cusp_basis

theorem level_75_dimension : Module.finrank ℂ (gamma0CuspForms 75) = 5 := by
  cusp_basis

theorem level_76_dimension : Module.finrank ℂ (gamma0CuspForms 76) = 8 := by
  cusp_basis

theorem level_77_dimension : Module.finrank ℂ (gamma0CuspForms 77) = 7 := by
  cusp_basis

theorem level_78_dimension : Module.finrank ℂ (gamma0CuspForms 78) = 11 := by
  cusp_basis

theorem level_79_dimension : Module.finrank ℂ (gamma0CuspForms 79) = 6 := by
  cusp_basis

theorem level_80_dimension : Module.finrank ℂ (gamma0CuspForms 80) = 7 := by
  cusp_basis

theorem level_81_dimension : Module.finrank ℂ (gamma0CuspForms 81) = 4 := by
  cusp_basis

theorem level_82_dimension : Module.finrank ℂ (gamma0CuspForms 82) = 9 := by
  cusp_basis

theorem level_83_dimension : Module.finrank ℂ (gamma0CuspForms 83) = 7 := by
  cusp_basis

theorem level_84_dimension : Module.finrank ℂ (gamma0CuspForms 84) = 11 := by
  cusp_basis

theorem level_85_dimension : Module.finrank ℂ (gamma0CuspForms 85) = 7 := by
  cusp_basis

theorem level_86_dimension : Module.finrank ℂ (gamma0CuspForms 86) = 10 := by
  cusp_basis

theorem level_87_dimension : Module.finrank ℂ (gamma0CuspForms 87) = 9 := by
  cusp_basis

theorem level_88_dimension : Module.finrank ℂ (gamma0CuspForms 88) = 9 := by
  cusp_basis

theorem level_89_dimension : Module.finrank ℂ (gamma0CuspForms 89) = 7 := by
  cusp_basis

theorem level_90_dimension : Module.finrank ℂ (gamma0CuspForms 90) = 11 := by
  cusp_basis

theorem level_91_dimension : Module.finrank ℂ (gamma0CuspForms 91) = 7 := by
  cusp_basis

theorem level_92_dimension : Module.finrank ℂ (gamma0CuspForms 92) = 10 := by
  cusp_basis

theorem level_93_dimension : Module.finrank ℂ (gamma0CuspForms 93) = 9 := by
  cusp_basis

theorem level_94_dimension : Module.finrank ℂ (gamma0CuspForms 94) = 11 := by
  cusp_basis

theorem level_95_dimension : Module.finrank ℂ (gamma0CuspForms 95) = 9 := by
  cusp_basis

theorem level_96_dimension : Module.finrank ℂ (gamma0CuspForms 96) = 9 := by
  cusp_basis

theorem level_97_dimension : Module.finrank ℂ (gamma0CuspForms 97) = 7 := by
  cusp_basis

theorem level_98_dimension : Module.finrank ℂ (gamma0CuspForms 98) = 7 := by
  cusp_basis

theorem level_99_dimension : Module.finrank ℂ (gamma0CuspForms 99) = 9 := by
  cusp_basis

theorem level_100_dimension : Module.finrank ℂ (gamma0CuspForms 100) = 7 := by
  cusp_basis

theorem level_101_dimension : Module.finrank ℂ (gamma0CuspForms 101) = 8 := by
  cusp_basis

theorem level_102_dimension : Module.finrank ℂ (gamma0CuspForms 102) = 15 := by
  cusp_basis

theorem level_103_dimension : Module.finrank ℂ (gamma0CuspForms 103) = 8 := by
  cusp_basis

theorem level_104_dimension : Module.finrank ℂ (gamma0CuspForms 104) = 11 := by
  cusp_basis

theorem level_105_dimension : Module.finrank ℂ (gamma0CuspForms 105) = 13 := by
  cusp_basis

theorem level_106_dimension : Module.finrank ℂ (gamma0CuspForms 106) = 12 := by
  cusp_basis

theorem level_107_dimension : Module.finrank ℂ (gamma0CuspForms 107) = 9 := by
  cusp_basis

theorem level_108_dimension : Module.finrank ℂ (gamma0CuspForms 108) = 10 := by
  cusp_basis

theorem level_109_dimension : Module.finrank ℂ (gamma0CuspForms 109) = 8 := by
  cusp_basis

theorem level_110_dimension : Module.finrank ℂ (gamma0CuspForms 110) = 15 := by
  cusp_basis

theorem level_111_dimension : Module.finrank ℂ (gamma0CuspForms 111) = 11 := by
  cusp_basis

theorem level_112_dimension : Module.finrank ℂ (gamma0CuspForms 112) = 11 := by
  cusp_basis

theorem level_113_dimension : Module.finrank ℂ (gamma0CuspForms 113) = 9 := by
  cusp_basis

theorem level_114_dimension : Module.finrank ℂ (gamma0CuspForms 114) = 17 := by
  cusp_basis

theorem level_115_dimension : Module.finrank ℂ (gamma0CuspForms 115) = 11 := by
  cusp_basis

theorem level_116_dimension : Module.finrank ℂ (gamma0CuspForms 116) = 13 := by
  cusp_basis

theorem level_117_dimension : Module.finrank ℂ (gamma0CuspForms 117) = 11 := by
  cusp_basis

theorem level_118_dimension : Module.finrank ℂ (gamma0CuspForms 118) = 14 := by
  cusp_basis

theorem level_119_dimension : Module.finrank ℂ (gamma0CuspForms 119) = 11 := by
  cusp_basis

theorem level_120_dimension : Module.finrank ℂ (gamma0CuspForms 120) = 17 := by
  cusp_basis

theorem level_121_dimension : Module.finrank ℂ (gamma0CuspForms 121) = 6 := by
  cusp_basis

theorem level_122_dimension : Module.finrank ℂ (gamma0CuspForms 122) = 14 := by
  cusp_basis

theorem level_123_dimension : Module.finrank ℂ (gamma0CuspForms 123) = 13 := by
  cusp_basis

theorem level_124_dimension : Module.finrank ℂ (gamma0CuspForms 124) = 14 := by
  cusp_basis

theorem level_125_dimension : Module.finrank ℂ (gamma0CuspForms 125) = 8 := by
  cusp_basis

theorem level_126_dimension : Module.finrank ℂ (gamma0CuspForms 126) = 17 := by
  cusp_basis

theorem level_127_dimension : Module.finrank ℂ (gamma0CuspForms 127) = 10 := by
  cusp_basis

theorem level_128_dimension : Module.finrank ℂ (gamma0CuspForms 128) = 9 := by
  cusp_basis

theorem level_129_dimension : Module.finrank ℂ (gamma0CuspForms 129) = 13 := by
  cusp_basis

theorem level_130_dimension : Module.finrank ℂ (gamma0CuspForms 130) = 17 := by
  cusp_basis

theorem level_131_dimension : Module.finrank ℂ (gamma0CuspForms 131) = 11 := by
  cusp_basis

theorem level_132_dimension : Module.finrank ℂ (gamma0CuspForms 132) = 19 := by
  cusp_basis

theorem level_133_dimension : Module.finrank ℂ (gamma0CuspForms 133) = 11 := by
  cusp_basis

theorem level_134_dimension : Module.finrank ℂ (gamma0CuspForms 134) = 16 := by
  cusp_basis

theorem level_135_dimension : Module.finrank ℂ (gamma0CuspForms 135) = 13 := by
  cusp_basis

theorem level_136_dimension : Module.finrank ℂ (gamma0CuspForms 136) = 15 := by
  cusp_basis

theorem level_137_dimension : Module.finrank ℂ (gamma0CuspForms 137) = 11 := by
  cusp_basis

theorem level_138_dimension : Module.finrank ℂ (gamma0CuspForms 138) = 21 := by
  cusp_basis

theorem level_139_dimension : Module.finrank ℂ (gamma0CuspForms 139) = 11 := by
  cusp_basis

theorem level_140_dimension : Module.finrank ℂ (gamma0CuspForms 140) = 19 := by
  cusp_basis

theorem level_141_dimension : Module.finrank ℂ (gamma0CuspForms 141) = 15 := by
  cusp_basis

theorem level_142_dimension : Module.finrank ℂ (gamma0CuspForms 142) = 17 := by
  cusp_basis

theorem level_143_dimension : Module.finrank ℂ (gamma0CuspForms 143) = 13 := by
  cusp_basis

theorem level_144_dimension : Module.finrank ℂ (gamma0CuspForms 144) = 13 := by
  cusp_basis

theorem level_145_dimension : Module.finrank ℂ (gamma0CuspForms 145) = 13 := by
  cusp_basis

theorem level_146_dimension : Module.finrank ℂ (gamma0CuspForms 146) = 17 := by
  cusp_basis

theorem level_147_dimension : Module.finrank ℂ (gamma0CuspForms 147) = 11 := by
  cusp_basis

theorem level_148_dimension : Module.finrank ℂ (gamma0CuspForms 148) = 17 := by
  cusp_basis

theorem level_149_dimension : Module.finrank ℂ (gamma0CuspForms 149) = 12 := by
  cusp_basis

theorem level_150_dimension : Module.finrank ℂ (gamma0CuspForms 150) = 19 := by
  cusp_basis

theorem level_151_dimension : Module.finrank ℂ (gamma0CuspForms 151) = 12 := by
  cusp_basis

theorem level_152_dimension : Module.finrank ℂ (gamma0CuspForms 152) = 17 := by
  cusp_basis

theorem level_153_dimension : Module.finrank ℂ (gamma0CuspForms 153) = 15 := by
  cusp_basis

theorem level_154_dimension : Module.finrank ℂ (gamma0CuspForms 154) = 21 := by
  cusp_basis

theorem level_155_dimension : Module.finrank ℂ (gamma0CuspForms 155) = 15 := by
  cusp_basis

theorem level_156_dimension : Module.finrank ℂ (gamma0CuspForms 156) = 23 := by
  cusp_basis

theorem level_157_dimension : Module.finrank ℂ (gamma0CuspForms 157) = 12 := by
  cusp_basis

theorem level_158_dimension : Module.finrank ℂ (gamma0CuspForms 158) = 19 := by
  cusp_basis

theorem level_159_dimension : Module.finrank ℂ (gamma0CuspForms 159) = 17 := by
  cusp_basis

theorem level_160_dimension : Module.finrank ℂ (gamma0CuspForms 160) = 17 := by
  cusp_basis

theorem level_161_dimension : Module.finrank ℂ (gamma0CuspForms 161) = 15 := by
  cusp_basis

theorem level_162_dimension : Module.finrank ℂ (gamma0CuspForms 162) = 16 := by
  cusp_basis

theorem level_163_dimension : Module.finrank ℂ (gamma0CuspForms 163) = 13 := by
  cusp_basis

theorem level_164_dimension : Module.finrank ℂ (gamma0CuspForms 164) = 19 := by
  cusp_basis

theorem level_165_dimension : Module.finrank ℂ (gamma0CuspForms 165) = 21 := by
  cusp_basis

theorem level_166_dimension : Module.finrank ℂ (gamma0CuspForms 166) = 20 := by
  cusp_basis

theorem level_167_dimension : Module.finrank ℂ (gamma0CuspForms 167) = 14 := by
  cusp_basis

theorem level_168_dimension : Module.finrank ℂ (gamma0CuspForms 168) = 25 := by
  cusp_basis

theorem level_169_dimension : Module.finrank ℂ (gamma0CuspForms 169) = 8 := by
  cusp_basis

theorem level_170_dimension : Module.finrank ℂ (gamma0CuspForms 170) = 23 := by
  cusp_basis

theorem level_171_dimension : Module.finrank ℂ (gamma0CuspForms 171) = 17 := by
  cusp_basis

theorem level_172_dimension : Module.finrank ℂ (gamma0CuspForms 172) = 20 := by
  cusp_basis

theorem level_173_dimension : Module.finrank ℂ (gamma0CuspForms 173) = 14 := by
  cusp_basis

theorem level_174_dimension : Module.finrank ℂ (gamma0CuspForms 174) = 27 := by
  cusp_basis

theorem level_175_dimension : Module.finrank ℂ (gamma0CuspForms 175) = 15 := by
  cusp_basis

theorem level_176_dimension : Module.finrank ℂ (gamma0CuspForms 176) = 19 := by
  cusp_basis

theorem level_177_dimension : Module.finrank ℂ (gamma0CuspForms 177) = 19 := by
  cusp_basis

theorem level_178_dimension : Module.finrank ℂ (gamma0CuspForms 178) = 21 := by
  cusp_basis

theorem level_179_dimension : Module.finrank ℂ (gamma0CuspForms 179) = 15 := by
  cusp_basis

theorem level_180_dimension : Module.finrank ℂ (gamma0CuspForms 180) = 25 := by
  cusp_basis

theorem level_181_dimension : Module.finrank ℂ (gamma0CuspForms 181) = 14 := by
  cusp_basis

theorem level_182_dimension : Module.finrank ℂ (gamma0CuspForms 182) = 25 := by
  cusp_basis

theorem level_183_dimension : Module.finrank ℂ (gamma0CuspForms 183) = 19 := by
  cusp_basis

theorem level_184_dimension : Module.finrank ℂ (gamma0CuspForms 184) = 21 := by
  cusp_basis

theorem level_185_dimension : Module.finrank ℂ (gamma0CuspForms 185) = 17 := by
  cusp_basis

theorem level_186_dimension : Module.finrank ℂ (gamma0CuspForms 186) = 29 := by
  cusp_basis

theorem level_187_dimension : Module.finrank ℂ (gamma0CuspForms 187) = 17 := by
  cusp_basis

theorem level_188_dimension : Module.finrank ℂ (gamma0CuspForms 188) = 22 := by
  cusp_basis

theorem level_189_dimension : Module.finrank ℂ (gamma0CuspForms 189) = 19 := by
  cusp_basis

theorem level_190_dimension : Module.finrank ℂ (gamma0CuspForms 190) = 27 := by
  cusp_basis

theorem level_191_dimension : Module.finrank ℂ (gamma0CuspForms 191) = 16 := by
  cusp_basis

theorem level_192_dimension : Module.finrank ℂ (gamma0CuspForms 192) = 21 := by
  cusp_basis

theorem level_193_dimension : Module.finrank ℂ (gamma0CuspForms 193) = 15 := by
  cusp_basis

theorem level_194_dimension : Module.finrank ℂ (gamma0CuspForms 194) = 23 := by
  cusp_basis

theorem level_195_dimension : Module.finrank ℂ (gamma0CuspForms 195) = 25 := by
  cusp_basis

theorem level_196_dimension : Module.finrank ℂ (gamma0CuspForms 196) = 17 := by
  cusp_basis

theorem level_197_dimension : Module.finrank ℂ (gamma0CuspForms 197) = 16 := by
  cusp_basis

theorem level_198_dimension : Module.finrank ℂ (gamma0CuspForms 198) = 29 := by
  cusp_basis

theorem level_199_dimension : Module.finrank ℂ (gamma0CuspForms 199) = 16 := by
  cusp_basis

theorem level_200_dimension : Module.finrank ℂ (gamma0CuspForms 200) = 19 := by
  cusp_basis

theorem level_201_dimension : Module.finrank ℂ (gamma0CuspForms 201) = 21 := by
  cusp_basis

theorem level_202_dimension : Module.finrank ℂ (gamma0CuspForms 202) = 24 := by
  cusp_basis

theorem level_203_dimension : Module.finrank ℂ (gamma0CuspForms 203) = 19 := by
  cusp_basis

theorem level_204_dimension : Module.finrank ℂ (gamma0CuspForms 204) = 31 := by
  cusp_basis

theorem level_205_dimension : Module.finrank ℂ (gamma0CuspForms 205) = 19 := by
  cusp_basis

theorem level_206_dimension : Module.finrank ℂ (gamma0CuspForms 206) = 25 := by
  cusp_basis

theorem level_207_dimension : Module.finrank ℂ (gamma0CuspForms 207) = 21 := by
  cusp_basis

theorem level_208_dimension : Module.finrank ℂ (gamma0CuspForms 208) = 23 := by
  cusp_basis

theorem level_209_dimension : Module.finrank ℂ (gamma0CuspForms 209) = 19 := by
  cusp_basis

theorem level_210_dimension : Module.finrank ℂ (gamma0CuspForms 210) = 41 := by
  cusp_basis

theorem level_211_dimension : Module.finrank ℂ (gamma0CuspForms 211) = 17 := by
  cusp_basis

theorem level_212_dimension : Module.finrank ℂ (gamma0CuspForms 212) = 25 := by
  cusp_basis

theorem level_213_dimension : Module.finrank ℂ (gamma0CuspForms 213) = 23 := by
  cusp_basis

theorem level_214_dimension : Module.finrank ℂ (gamma0CuspForms 214) = 26 := by
  cusp_basis

theorem level_215_dimension : Module.finrank ℂ (gamma0CuspForms 215) = 21 := by
  cusp_basis

theorem level_216_dimension : Module.finrank ℂ (gamma0CuspForms 216) = 25 := by
  cusp_basis

theorem level_217_dimension : Module.finrank ℂ (gamma0CuspForms 217) = 19 := by
  cusp_basis

theorem level_218_dimension : Module.finrank ℂ (gamma0CuspForms 218) = 26 := by
  cusp_basis

theorem level_219_dimension : Module.finrank ℂ (gamma0CuspForms 219) = 23 := by
  cusp_basis

theorem level_220_dimension : Module.finrank ℂ (gamma0CuspForms 220) = 31 := by
  cusp_basis

theorem level_221_dimension : Module.finrank ℂ (gamma0CuspForms 221) = 19 := by
  cusp_basis

theorem level_222_dimension : Module.finrank ℂ (gamma0CuspForms 222) = 35 := by
  cusp_basis

theorem level_223_dimension : Module.finrank ℂ (gamma0CuspForms 223) = 18 := by
  cusp_basis

theorem level_224_dimension : Module.finrank ℂ (gamma0CuspForms 224) = 25 := by
  cusp_basis

theorem level_225_dimension : Module.finrank ℂ (gamma0CuspForms 225) = 19 := by
  cusp_basis

theorem level_226_dimension : Module.finrank ℂ (gamma0CuspForms 226) = 27 := by
  cusp_basis

theorem level_227_dimension : Module.finrank ℂ (gamma0CuspForms 227) = 19 := by
  cusp_basis

theorem level_228_dimension : Module.finrank ℂ (gamma0CuspForms 228) = 35 := by
  cusp_basis

theorem level_229_dimension : Module.finrank ℂ (gamma0CuspForms 229) = 18 := by
  cusp_basis

theorem level_230_dimension : Module.finrank ℂ (gamma0CuspForms 230) = 33 := by
  cusp_basis

theorem level_231_dimension : Module.finrank ℂ (gamma0CuspForms 231) = 29 := by
  cusp_basis

theorem level_232_dimension : Module.finrank ℂ (gamma0CuspForms 232) = 27 := by
  cusp_basis

theorem level_233_dimension : Module.finrank ℂ (gamma0CuspForms 233) = 19 := by
  cusp_basis

theorem level_234_dimension : Module.finrank ℂ (gamma0CuspForms 234) = 35 := by
  cusp_basis

theorem level_235_dimension : Module.finrank ℂ (gamma0CuspForms 235) = 23 := by
  cusp_basis

theorem level_236_dimension : Module.finrank ℂ (gamma0CuspForms 236) = 28 := by
  cusp_basis

theorem level_237_dimension : Module.finrank ℂ (gamma0CuspForms 237) = 25 := by
  cusp_basis

theorem level_238_dimension : Module.finrank ℂ (gamma0CuspForms 238) = 33 := by
  cusp_basis

theorem level_239_dimension : Module.finrank ℂ (gamma0CuspForms 239) = 20 := by
  cusp_basis

theorem level_240_dimension : Module.finrank ℂ (gamma0CuspForms 240) = 37 := by
  cusp_basis

theorem level_241_dimension : Module.finrank ℂ (gamma0CuspForms 241) = 19 := by
  cusp_basis

theorem level_242_dimension : Module.finrank ℂ (gamma0CuspForms 242) = 22 := by
  cusp_basis

theorem level_243_dimension : Module.finrank ℂ (gamma0CuspForms 243) = 19 := by
  cusp_basis

theorem level_244_dimension : Module.finrank ℂ (gamma0CuspForms 244) = 29 := by
  cusp_basis

theorem level_245_dimension : Module.finrank ℂ (gamma0CuspForms 245) = 21 := by
  cusp_basis

theorem level_246_dimension : Module.finrank ℂ (gamma0CuspForms 246) = 39 := by
  cusp_basis

theorem level_247_dimension : Module.finrank ℂ (gamma0CuspForms 247) = 21 := by
  cusp_basis

theorem level_248_dimension : Module.finrank ℂ (gamma0CuspForms 248) = 29 := by
  cusp_basis

theorem level_249_dimension : Module.finrank ℂ (gamma0CuspForms 249) = 27 := by
  cusp_basis

theorem level_250_dimension : Module.finrank ℂ (gamma0CuspForms 250) = 28 := by
  cusp_basis

theorem level_251_dimension : Module.finrank ℂ (gamma0CuspForms 251) = 21 := by
  cusp_basis

theorem level_252_dimension : Module.finrank ℂ (gamma0CuspForms 252) = 37 := by
  cusp_basis

theorem level_253_dimension : Module.finrank ℂ (gamma0CuspForms 253) = 23 := by
  cusp_basis

theorem level_254_dimension : Module.finrank ℂ (gamma0CuspForms 254) = 31 := by
  cusp_basis

theorem level_255_dimension : Module.finrank ℂ (gamma0CuspForms 255) = 33 := by
  cusp_basis

theorem level_256_dimension : Module.finrank ℂ (gamma0CuspForms 256) = 21 := by
  cusp_basis

theorem level_257_dimension : Module.finrank ℂ (gamma0CuspForms 257) = 21 := by
  cusp_basis

theorem level_258_dimension : Module.finrank ℂ (gamma0CuspForms 258) = 41 := by
  cusp_basis

theorem level_259_dimension : Module.finrank ℂ (gamma0CuspForms 259) = 23 := by
  cusp_basis

theorem level_260_dimension : Module.finrank ℂ (gamma0CuspForms 260) = 37 := by
  cusp_basis

theorem level_261_dimension : Module.finrank ℂ (gamma0CuspForms 261) = 27 := by
  cusp_basis

theorem level_262_dimension : Module.finrank ℂ (gamma0CuspForms 262) = 32 := by
  cusp_basis

theorem level_263_dimension : Module.finrank ℂ (gamma0CuspForms 263) = 22 := by
  cusp_basis

theorem level_264_dimension : Module.finrank ℂ (gamma0CuspForms 264) = 41 := by
  cusp_basis

theorem level_265_dimension : Module.finrank ℂ (gamma0CuspForms 265) = 25 := by
  cusp_basis

theorem level_266_dimension : Module.finrank ℂ (gamma0CuspForms 266) = 37 := by
  cusp_basis

theorem level_267_dimension : Module.finrank ℂ (gamma0CuspForms 267) = 29 := by
  cusp_basis

theorem level_268_dimension : Module.finrank ℂ (gamma0CuspForms 268) = 32 := by
  cusp_basis

theorem level_269_dimension : Module.finrank ℂ (gamma0CuspForms 269) = 22 := by
  cusp_basis

theorem level_270_dimension : Module.finrank ℂ (gamma0CuspForms 270) = 43 := by
  cusp_basis

theorem level_271_dimension : Module.finrank ℂ (gamma0CuspForms 271) = 22 := by
  cusp_basis

theorem level_272_dimension : Module.finrank ℂ (gamma0CuspForms 272) = 31 := by
  cusp_basis

theorem level_273_dimension : Module.finrank ℂ (gamma0CuspForms 273) = 33 := by
  cusp_basis

theorem level_274_dimension : Module.finrank ℂ (gamma0CuspForms 274) = 33 := by
  cusp_basis

theorem level_275_dimension : Module.finrank ℂ (gamma0CuspForms 275) = 25 := by
  cusp_basis

theorem level_276_dimension : Module.finrank ℂ (gamma0CuspForms 276) = 43 := by
  cusp_basis

theorem level_277_dimension : Module.finrank ℂ (gamma0CuspForms 277) = 22 := by
  cusp_basis

theorem level_278_dimension : Module.finrank ℂ (gamma0CuspForms 278) = 34 := by
  cusp_basis

theorem level_279_dimension : Module.finrank ℂ (gamma0CuspForms 279) = 29 := by
  cusp_basis

theorem level_280_dimension : Module.finrank ℂ (gamma0CuspForms 280) = 41 := by
  cusp_basis

theorem level_281_dimension : Module.finrank ℂ (gamma0CuspForms 281) = 23 := by
  cusp_basis

theorem level_282_dimension : Module.finrank ℂ (gamma0CuspForms 282) = 45 := by
  cusp_basis

theorem level_283_dimension : Module.finrank ℂ (gamma0CuspForms 283) = 23 := by
  cusp_basis

theorem level_284_dimension : Module.finrank ℂ (gamma0CuspForms 284) = 34 := by
  cusp_basis

theorem level_285_dimension : Module.finrank ℂ (gamma0CuspForms 285) = 37 := by
  cusp_basis

theorem level_286_dimension : Module.finrank ℂ (gamma0CuspForms 286) = 39 := by
  cusp_basis

theorem level_287_dimension : Module.finrank ℂ (gamma0CuspForms 287) = 27 := by
  cusp_basis

theorem level_288_dimension : Module.finrank ℂ (gamma0CuspForms 288) = 33 := by
  cusp_basis

theorem level_289_dimension : Module.finrank ℂ (gamma0CuspForms 289) = 17 := by
  cusp_basis

theorem level_290_dimension : Module.finrank ℂ (gamma0CuspForms 290) = 41 := by
  cusp_basis

theorem level_291_dimension : Module.finrank ℂ (gamma0CuspForms 291) = 31 := by
  cusp_basis

theorem level_292_dimension : Module.finrank ℂ (gamma0CuspForms 292) = 35 := by
  cusp_basis

theorem level_293_dimension : Module.finrank ℂ (gamma0CuspForms 293) = 24 := by
  cusp_basis

theorem level_294_dimension : Module.finrank ℂ (gamma0CuspForms 294) = 41 := by
  cusp_basis

theorem level_295_dimension : Module.finrank ℂ (gamma0CuspForms 295) = 29 := by
  cusp_basis

theorem level_296_dimension : Module.finrank ℂ (gamma0CuspForms 296) = 35 := by
  cusp_basis

theorem level_297_dimension : Module.finrank ℂ (gamma0CuspForms 297) = 31 := by
  cusp_basis

theorem level_298_dimension : Module.finrank ℂ (gamma0CuspForms 298) = 36 := by
  cusp_basis

theorem level_299_dimension : Module.finrank ℂ (gamma0CuspForms 299) = 27 := by
  cusp_basis

theorem level_300_dimension : Module.finrank ℂ (gamma0CuspForms 300) = 43 := by
  cusp_basis

theorem level_301_dimension : Module.finrank ℂ (gamma0CuspForms 301) = 27 := by
  cusp_basis

theorem level_302_dimension : Module.finrank ℂ (gamma0CuspForms 302) = 37 := by
  cusp_basis

theorem level_303_dimension : Module.finrank ℂ (gamma0CuspForms 303) = 33 := by
  cusp_basis

theorem level_304_dimension : Module.finrank ℂ (gamma0CuspForms 304) = 35 := by
  cusp_basis

theorem level_305_dimension : Module.finrank ℂ (gamma0CuspForms 305) = 29 := by
  cusp_basis

theorem level_306_dimension : Module.finrank ℂ (gamma0CuspForms 306) = 47 := by
  cusp_basis

theorem level_307_dimension : Module.finrank ℂ (gamma0CuspForms 307) = 25 := by
  cusp_basis

theorem level_308_dimension : Module.finrank ℂ (gamma0CuspForms 308) = 43 := by
  cusp_basis

theorem level_309_dimension : Module.finrank ℂ (gamma0CuspForms 309) = 33 := by
  cusp_basis

theorem level_310_dimension : Module.finrank ℂ (gamma0CuspForms 310) = 45 := by
  cusp_basis

theorem level_311_dimension : Module.finrank ℂ (gamma0CuspForms 311) = 26 := by
  cusp_basis

theorem level_312_dimension : Module.finrank ℂ (gamma0CuspForms 312) = 49 := by
  cusp_basis

theorem level_313_dimension : Module.finrank ℂ (gamma0CuspForms 313) = 25 := by
  cusp_basis

theorem level_314_dimension : Module.finrank ℂ (gamma0CuspForms 314) = 38 := by
  cusp_basis

theorem level_315_dimension : Module.finrank ℂ (gamma0CuspForms 315) = 41 := by
  cusp_basis

theorem level_316_dimension : Module.finrank ℂ (gamma0CuspForms 316) = 38 := by
  cusp_basis

theorem level_317_dimension : Module.finrank ℂ (gamma0CuspForms 317) = 26 := by
  cusp_basis

theorem level_318_dimension : Module.finrank ℂ (gamma0CuspForms 318) = 51 := by
  cusp_basis

theorem level_319_dimension : Module.finrank ℂ (gamma0CuspForms 319) = 29 := by
  cusp_basis

theorem level_320_dimension : Module.finrank ℂ (gamma0CuspForms 320) = 37 := by
  cusp_basis

theorem level_321_dimension : Module.finrank ℂ (gamma0CuspForms 321) = 35 := by
  cusp_basis

theorem level_322_dimension : Module.finrank ℂ (gamma0CuspForms 322) = 45 := by
  cusp_basis

theorem level_323_dimension : Module.finrank ℂ (gamma0CuspForms 323) = 29 := by
  cusp_basis

theorem level_324_dimension : Module.finrank ℂ (gamma0CuspForms 324) = 37 := by
  cusp_basis

theorem level_325_dimension : Module.finrank ℂ (gamma0CuspForms 325) = 29 := by
  cusp_basis

theorem level_326_dimension : Module.finrank ℂ (gamma0CuspForms 326) = 40 := by
  cusp_basis

theorem level_327_dimension : Module.finrank ℂ (gamma0CuspForms 327) = 35 := by
  cusp_basis

theorem level_328_dimension : Module.finrank ℂ (gamma0CuspForms 328) = 39 := by
  cusp_basis

theorem level_329_dimension : Module.finrank ℂ (gamma0CuspForms 329) = 31 := by
  cusp_basis

theorem level_330_dimension : Module.finrank ℂ (gamma0CuspForms 330) = 65 := by
  cusp_basis

theorem level_331_dimension : Module.finrank ℂ (gamma0CuspForms 331) = 27 := by
  cusp_basis

theorem level_332_dimension : Module.finrank ℂ (gamma0CuspForms 332) = 40 := by
  cusp_basis

theorem level_333_dimension : Module.finrank ℂ (gamma0CuspForms 333) = 35 := by
  cusp_basis

theorem level_334_dimension : Module.finrank ℂ (gamma0CuspForms 334) = 41 := by
  cusp_basis

theorem level_335_dimension : Module.finrank ℂ (gamma0CuspForms 335) = 33 := by
  cusp_basis

theorem level_336_dimension : Module.finrank ℂ (gamma0CuspForms 336) = 53 := by
  cusp_basis

theorem level_337_dimension : Module.finrank ℂ (gamma0CuspForms 337) = 27 := by
  cusp_basis

theorem level_338_dimension : Module.finrank ℂ (gamma0CuspForms 338) = 32 := by
  cusp_basis

theorem level_339_dimension : Module.finrank ℂ (gamma0CuspForms 339) = 37 := by
  cusp_basis

theorem level_340_dimension : Module.finrank ℂ (gamma0CuspForms 340) = 49 := by
  cusp_basis

theorem level_341_dimension : Module.finrank ℂ (gamma0CuspForms 341) = 31 := by
  cusp_basis

theorem level_342_dimension : Module.finrank ℂ (gamma0CuspForms 342) = 53 := by
  cusp_basis

theorem level_343_dimension : Module.finrank ℂ (gamma0CuspForms 343) = 26 := by
  cusp_basis

theorem level_344_dimension : Module.finrank ℂ (gamma0CuspForms 344) = 41 := by
  cusp_basis

theorem level_345_dimension : Module.finrank ℂ (gamma0CuspForms 345) = 45 := by
  cusp_basis

theorem level_346_dimension : Module.finrank ℂ (gamma0CuspForms 346) = 42 := by
  cusp_basis

theorem level_347_dimension : Module.finrank ℂ (gamma0CuspForms 347) = 29 := by
  cusp_basis

theorem level_348_dimension : Module.finrank ℂ (gamma0CuspForms 348) = 55 := by
  cusp_basis

theorem level_349_dimension : Module.finrank ℂ (gamma0CuspForms 349) = 28 := by
  cusp_basis

theorem level_350_dimension : Module.finrank ℂ (gamma0CuspForms 350) = 49 := by
  cusp_basis

theorem level_351_dimension : Module.finrank ℂ (gamma0CuspForms 351) = 37 := by
  cusp_basis

theorem level_352_dimension : Module.finrank ℂ (gamma0CuspForms 352) = 41 := by
  cusp_basis

theorem level_353_dimension : Module.finrank ℂ (gamma0CuspForms 353) = 29 := by
  cusp_basis

theorem level_354_dimension : Module.finrank ℂ (gamma0CuspForms 354) = 57 := by
  cusp_basis

theorem level_355_dimension : Module.finrank ℂ (gamma0CuspForms 355) = 35 := by
  cusp_basis

theorem level_356_dimension : Module.finrank ℂ (gamma0CuspForms 356) = 43 := by
  cusp_basis

theorem level_357_dimension : Module.finrank ℂ (gamma0CuspForms 357) = 45 := by
  cusp_basis

theorem level_358_dimension : Module.finrank ℂ (gamma0CuspForms 358) = 44 := by
  cusp_basis

theorem level_359_dimension : Module.finrank ℂ (gamma0CuspForms 359) = 30 := by
  cusp_basis

theorem level_360_dimension : Module.finrank ℂ (gamma0CuspForms 360) = 57 := by
  cusp_basis

theorem level_361_dimension : Module.finrank ℂ (gamma0CuspForms 361) = 22 := by
  cusp_basis

theorem level_362_dimension : Module.finrank ℂ (gamma0CuspForms 362) = 44 := by
  cusp_basis

theorem level_363_dimension : Module.finrank ℂ (gamma0CuspForms 363) = 33 := by
  cusp_basis

theorem level_364_dimension : Module.finrank ℂ (gamma0CuspForms 364) = 51 := by
  cusp_basis

theorem level_365_dimension : Module.finrank ℂ (gamma0CuspForms 365) = 35 := by
  cusp_basis

theorem level_366_dimension : Module.finrank ℂ (gamma0CuspForms 366) = 59 := by
  cusp_basis

theorem level_367_dimension : Module.finrank ℂ (gamma0CuspForms 367) = 30 := by
  cusp_basis

theorem level_368_dimension : Module.finrank ℂ (gamma0CuspForms 368) = 43 := by
  cusp_basis

theorem level_369_dimension : Module.finrank ℂ (gamma0CuspForms 369) = 39 := by
  cusp_basis

theorem level_370_dimension : Module.finrank ℂ (gamma0CuspForms 370) = 53 := by
  cusp_basis

theorem level_371_dimension : Module.finrank ℂ (gamma0CuspForms 371) = 35 := by
  cusp_basis

theorem level_372_dimension : Module.finrank ℂ (gamma0CuspForms 372) = 59 := by
  cusp_basis

theorem level_373_dimension : Module.finrank ℂ (gamma0CuspForms 373) = 30 := by
  cusp_basis

theorem level_374_dimension : Module.finrank ℂ (gamma0CuspForms 374) = 51 := by
  cusp_basis

theorem level_375_dimension : Module.finrank ℂ (gamma0CuspForms 375) = 41 := by
  cusp_basis

theorem level_376_dimension : Module.finrank ℂ (gamma0CuspForms 376) = 45 := by
  cusp_basis

theorem level_377_dimension : Module.finrank ℂ (gamma0CuspForms 377) = 33 := by
  cusp_basis

theorem level_378_dimension : Module.finrank ℂ (gamma0CuspForms 378) = 61 := by
  cusp_basis

theorem level_379_dimension : Module.finrank ℂ (gamma0CuspForms 379) = 31 := by
  cusp_basis

theorem level_380_dimension : Module.finrank ℂ (gamma0CuspForms 380) = 55 := by
  cusp_basis

theorem level_381_dimension : Module.finrank ℂ (gamma0CuspForms 381) = 41 := by
  cusp_basis

theorem level_382_dimension : Module.finrank ℂ (gamma0CuspForms 382) = 47 := by
  cusp_basis

theorem level_383_dimension : Module.finrank ℂ (gamma0CuspForms 383) = 32 := by
  cusp_basis

theorem level_384_dimension : Module.finrank ℂ (gamma0CuspForms 384) = 49 := by
  cusp_basis

theorem level_385_dimension : Module.finrank ℂ (gamma0CuspForms 385) = 45 := by
  cusp_basis

theorem level_386_dimension : Module.finrank ℂ (gamma0CuspForms 386) = 47 := by
  cusp_basis

theorem level_387_dimension : Module.finrank ℂ (gamma0CuspForms 387) = 41 := by
  cusp_basis

theorem level_388_dimension : Module.finrank ℂ (gamma0CuspForms 388) = 47 := by
  cusp_basis

theorem level_389_dimension : Module.finrank ℂ (gamma0CuspForms 389) = 32 := by
  cusp_basis

theorem level_390_dimension : Module.finrank ℂ (gamma0CuspForms 390) = 77 := by
  cusp_basis

theorem level_391_dimension : Module.finrank ℂ (gamma0CuspForms 391) = 35 := by
  cusp_basis

theorem level_392_dimension : Module.finrank ℂ (gamma0CuspForms 392) = 41 := by
  cusp_basis

theorem level_393_dimension : Module.finrank ℂ (gamma0CuspForms 393) = 43 := by
  cusp_basis

theorem level_394_dimension : Module.finrank ℂ (gamma0CuspForms 394) = 48 := by
  cusp_basis

theorem level_395_dimension : Module.finrank ℂ (gamma0CuspForms 395) = 39 := by
  cusp_basis

theorem level_396_dimension : Module.finrank ℂ (gamma0CuspForms 396) = 61 := by
  cusp_basis

theorem level_397_dimension : Module.finrank ℂ (gamma0CuspForms 397) = 32 := by
  cusp_basis

theorem level_398_dimension : Module.finrank ℂ (gamma0CuspForms 398) = 49 := by
  cusp_basis

theorem level_399_dimension : Module.finrank ℂ (gamma0CuspForms 399) = 49 := by
  cusp_basis

theorem level_400_dimension : Module.finrank ℂ (gamma0CuspForms 400) = 43 := by
  cusp_basis

theorem level_401_dimension : Module.finrank ℂ (gamma0CuspForms 401) = 33 := by
  cusp_basis

theorem level_402_dimension : Module.finrank ℂ (gamma0CuspForms 402) = 65 := by
  cusp_basis

theorem level_403_dimension : Module.finrank ℂ (gamma0CuspForms 403) = 35 := by
  cusp_basis

theorem level_404_dimension : Module.finrank ℂ (gamma0CuspForms 404) = 49 := by
  cusp_basis

theorem level_405_dimension : Module.finrank ℂ (gamma0CuspForms 405) = 43 := by
  cusp_basis

theorem level_406_dimension : Module.finrank ℂ (gamma0CuspForms 406) = 57 := by
  cusp_basis

theorem level_407_dimension : Module.finrank ℂ (gamma0CuspForms 407) = 37 := by
  cusp_basis

theorem level_408_dimension : Module.finrank ℂ (gamma0CuspForms 408) = 65 := by
  cusp_basis

theorem level_409_dimension : Module.finrank ℂ (gamma0CuspForms 409) = 33 := by
  cusp_basis

theorem level_410_dimension : Module.finrank ℂ (gamma0CuspForms 410) = 59 := by
  cusp_basis

theorem level_411_dimension : Module.finrank ℂ (gamma0CuspForms 411) = 45 := by
  cusp_basis

theorem level_412_dimension : Module.finrank ℂ (gamma0CuspForms 412) = 50 := by
  cusp_basis

theorem level_413_dimension : Module.finrank ℂ (gamma0CuspForms 413) = 39 := by
  cusp_basis

theorem level_414_dimension : Module.finrank ℂ (gamma0CuspForms 414) = 65 := by
  cusp_basis

theorem level_415_dimension : Module.finrank ℂ (gamma0CuspForms 415) = 41 := by
  cusp_basis

theorem level_416_dimension : Module.finrank ℂ (gamma0CuspForms 416) = 49 := by
  cusp_basis

theorem level_417_dimension : Module.finrank ℂ (gamma0CuspForms 417) = 45 := by
  cusp_basis

theorem level_418_dimension : Module.finrank ℂ (gamma0CuspForms 418) = 57 := by
  cusp_basis

theorem level_419_dimension : Module.finrank ℂ (gamma0CuspForms 419) = 35 := by
  cusp_basis

theorem level_420_dimension : Module.finrank ℂ (gamma0CuspForms 420) = 85 := by
  cusp_basis

theorem level_421_dimension : Module.finrank ℂ (gamma0CuspForms 421) = 34 := by
  cusp_basis

theorem level_422_dimension : Module.finrank ℂ (gamma0CuspForms 422) = 52 := by
  cusp_basis

theorem level_423_dimension : Module.finrank ℂ (gamma0CuspForms 423) = 45 := by
  cusp_basis

theorem level_424_dimension : Module.finrank ℂ (gamma0CuspForms 424) = 51 := by
  cusp_basis

theorem level_425_dimension : Module.finrank ℂ (gamma0CuspForms 425) = 39 := by
  cusp_basis

theorem level_426_dimension : Module.finrank ℂ (gamma0CuspForms 426) = 69 := by
  cusp_basis

theorem level_427_dimension : Module.finrank ℂ (gamma0CuspForms 427) = 39 := by
  cusp_basis

theorem level_428_dimension : Module.finrank ℂ (gamma0CuspForms 428) = 52 := by
  cusp_basis

theorem level_429_dimension : Module.finrank ℂ (gamma0CuspForms 429) = 53 := by
  cusp_basis

theorem level_430_dimension : Module.finrank ℂ (gamma0CuspForms 430) = 63 := by
  cusp_basis

theorem level_431_dimension : Module.finrank ℂ (gamma0CuspForms 431) = 36 := by
  cusp_basis

theorem level_432_dimension : Module.finrank ℂ (gamma0CuspForms 432) = 55 := by
  cusp_basis

theorem level_433_dimension : Module.finrank ℂ (gamma0CuspForms 433) = 35 := by
  cusp_basis

theorem level_434_dimension : Module.finrank ℂ (gamma0CuspForms 434) = 61 := by
  cusp_basis

theorem level_435_dimension : Module.finrank ℂ (gamma0CuspForms 435) = 57 := by
  cusp_basis

theorem level_436_dimension : Module.finrank ℂ (gamma0CuspForms 436) = 53 := by
  cusp_basis

theorem level_437_dimension : Module.finrank ℂ (gamma0CuspForms 437) = 39 := by
  cusp_basis

theorem level_438_dimension : Module.finrank ℂ (gamma0CuspForms 438) = 71 := by
  cusp_basis

theorem level_439_dimension : Module.finrank ℂ (gamma0CuspForms 439) = 36 := by
  cusp_basis

theorem level_440_dimension : Module.finrank ℂ (gamma0CuspForms 440) = 65 := by
  cusp_basis

theorem level_441_dimension : Module.finrank ℂ (gamma0CuspForms 441) = 41 := by
  cusp_basis

theorem level_442_dimension : Module.finrank ℂ (gamma0CuspForms 442) = 59 := by
  cusp_basis

theorem level_443_dimension : Module.finrank ℂ (gamma0CuspForms 443) = 37 := by
  cusp_basis

theorem level_444_dimension : Module.finrank ℂ (gamma0CuspForms 444) = 71 := by
  cusp_basis

theorem level_445_dimension : Module.finrank ℂ (gamma0CuspForms 445) = 43 := by
  cusp_basis

theorem level_446_dimension : Module.finrank ℂ (gamma0CuspForms 446) = 55 := by
  cusp_basis

theorem level_447_dimension : Module.finrank ℂ (gamma0CuspForms 447) = 49 := by
  cusp_basis

theorem level_448_dimension : Module.finrank ℂ (gamma0CuspForms 448) = 53 := by
  cusp_basis

theorem level_449_dimension : Module.finrank ℂ (gamma0CuspForms 449) = 37 := by
  cusp_basis

theorem level_450_dimension : Module.finrank ℂ (gamma0CuspForms 450) = 67 := by
  cusp_basis

theorem level_451_dimension : Module.finrank ℂ (gamma0CuspForms 451) = 41 := by
  cusp_basis

theorem level_452_dimension : Module.finrank ℂ (gamma0CuspForms 452) = 55 := by
  cusp_basis

theorem level_453_dimension : Module.finrank ℂ (gamma0CuspForms 453) = 49 := by
  cusp_basis

theorem level_454_dimension : Module.finrank ℂ (gamma0CuspForms 454) = 56 := by
  cusp_basis

theorem level_455_dimension : Module.finrank ℂ (gamma0CuspForms 455) = 53 := by
  cusp_basis

theorem level_456_dimension : Module.finrank ℂ (gamma0CuspForms 456) = 73 := by
  cusp_basis

theorem level_457_dimension : Module.finrank ℂ (gamma0CuspForms 457) = 37 := by
  cusp_basis

theorem level_458_dimension : Module.finrank ℂ (gamma0CuspForms 458) = 56 := by
  cusp_basis

theorem level_459_dimension : Module.finrank ℂ (gamma0CuspForms 459) = 49 := by
  cusp_basis

theorem level_460_dimension : Module.finrank ℂ (gamma0CuspForms 460) = 67 := by
  cusp_basis

theorem level_461_dimension : Module.finrank ℂ (gamma0CuspForms 461) = 38 := by
  cusp_basis

theorem level_462_dimension : Module.finrank ℂ (gamma0CuspForms 462) = 89 := by
  cusp_basis

theorem level_463_dimension : Module.finrank ℂ (gamma0CuspForms 463) = 38 := by
  cusp_basis

theorem level_464_dimension : Module.finrank ℂ (gamma0CuspForms 464) = 55 := by
  cusp_basis

theorem level_465_dimension : Module.finrank ℂ (gamma0CuspForms 465) = 61 := by
  cusp_basis

theorem level_466_dimension : Module.finrank ℂ (gamma0CuspForms 466) = 57 := by
  cusp_basis

theorem level_467_dimension : Module.finrank ℂ (gamma0CuspForms 467) = 39 := by
  cusp_basis

theorem level_468_dimension : Module.finrank ℂ (gamma0CuspForms 468) = 73 := by
  cusp_basis

theorem level_469_dimension : Module.finrank ℂ (gamma0CuspForms 469) = 43 := by
  cusp_basis

theorem level_470_dimension : Module.finrank ℂ (gamma0CuspForms 470) = 69 := by
  cusp_basis

theorem level_471_dimension : Module.finrank ℂ (gamma0CuspForms 471) = 51 := by
  cusp_basis

theorem level_472_dimension : Module.finrank ℂ (gamma0CuspForms 472) = 57 := by
  cusp_basis

theorem level_473_dimension : Module.finrank ℂ (gamma0CuspForms 473) = 43 := by
  cusp_basis

theorem level_474_dimension : Module.finrank ℂ (gamma0CuspForms 474) = 77 := by
  cusp_basis

theorem level_475_dimension : Module.finrank ℂ (gamma0CuspForms 475) = 45 := by
  cusp_basis

theorem level_476_dimension : Module.finrank ℂ (gamma0CuspForms 476) = 67 := by
  cusp_basis

theorem level_477_dimension : Module.finrank ℂ (gamma0CuspForms 477) = 51 := by
  cusp_basis

theorem level_478_dimension : Module.finrank ℂ (gamma0CuspForms 478) = 59 := by
  cusp_basis

theorem level_479_dimension : Module.finrank ℂ (gamma0CuspForms 479) = 40 := by
  cusp_basis

theorem level_480_dimension : Module.finrank ℂ (gamma0CuspForms 480) = 81 := by
  cusp_basis

theorem level_481_dimension : Module.finrank ℂ (gamma0CuspForms 481) = 41 := by
  cusp_basis

theorem level_482_dimension : Module.finrank ℂ (gamma0CuspForms 482) = 59 := by
  cusp_basis

theorem level_483_dimension : Module.finrank ℂ (gamma0CuspForms 483) = 61 := by
  cusp_basis

theorem level_484_dimension : Module.finrank ℂ (gamma0CuspForms 484) = 49 := by
  cusp_basis

theorem level_485_dimension : Module.finrank ℂ (gamma0CuspForms 485) = 47 := by
  cusp_basis

theorem level_486_dimension : Module.finrank ℂ (gamma0CuspForms 486) = 64 := by
  cusp_basis

theorem level_487_dimension : Module.finrank ℂ (gamma0CuspForms 487) = 40 := by
  cusp_basis

theorem level_488_dimension : Module.finrank ℂ (gamma0CuspForms 488) = 59 := by
  cusp_basis

theorem level_489_dimension : Module.finrank ℂ (gamma0CuspForms 489) = 53 := by
  cusp_basis

theorem level_490_dimension : Module.finrank ℂ (gamma0CuspForms 490) = 69 := by
  cusp_basis

theorem level_491_dimension : Module.finrank ℂ (gamma0CuspForms 491) = 41 := by
  cusp_basis

theorem level_492_dimension : Module.finrank ℂ (gamma0CuspForms 492) = 79 := by
  cusp_basis

theorem level_493_dimension : Module.finrank ℂ (gamma0CuspForms 493) = 43 := by
  cusp_basis

theorem level_494_dimension : Module.finrank ℂ (gamma0CuspForms 494) = 67 := by
  cusp_basis

theorem level_495_dimension : Module.finrank ℂ (gamma0CuspForms 495) = 65 := by
  cusp_basis

theorem level_496_dimension : Module.finrank ℂ (gamma0CuspForms 496) = 59 := by
  cusp_basis

theorem level_497_dimension : Module.finrank ℂ (gamma0CuspForms 497) = 47 := by
  cusp_basis

theorem level_498_dimension : Module.finrank ℂ (gamma0CuspForms 498) = 81 := by
  cusp_basis

theorem level_499_dimension : Module.finrank ℂ (gamma0CuspForms 499) = 41 := by
  cusp_basis

theorem level_500_dimension : Module.finrank ℂ (gamma0CuspForms 500) = 61 := by
  cusp_basis

end WeightTwoCusps.LevelRangeTests
