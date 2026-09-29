import ForestUnimodality.IntermediateBridgeCoverData.Batch000_015

import ForestUnimodality.IntermediateBridgeCoverData.Batch016_031

import ForestUnimodality.IntermediateBridgeCoverData.Batch032_047

import ForestUnimodality.IntermediateBridgeCoverData.Batch048_063

import ForestUnimodality.IntermediateBridgeCoverData.Batch064_079

import ForestUnimodality.IntermediateBridgeCoverData.Batch080_095

import ForestUnimodality.IntermediateBridgeCoverData.Batch096_111

import ForestUnimodality.IntermediateBridgeCoverData.Batch112_127

import ForestUnimodality.IntermediateBridgeCoverData.Batch128_143

import ForestUnimodality.IntermediateBridgeCoverData.Batch144_159

import ForestUnimodality.IntermediateBridgeCoverData.Batch160_175

import ForestUnimodality.IntermediateBridgeCoverData.Batch176_191

import ForestUnimodality.IntermediateBridgeCoverData.Batch192_207

import ForestUnimodality.IntermediateBridgeCoverData.Batch208_223

import ForestUnimodality.IntermediateBridgeCoverData.Batch224_239

import ForestUnimodality.IntermediateBridgeCoverData.Batch240_255

import ForestUnimodality.IntermediateBridgeCoverData.Batch256_271

import ForestUnimodality.IntermediateBridgeCoverData.Batch272_287

import ForestUnimodality.IntermediateBridgeCoverData.Batch288_303

import ForestUnimodality.IntermediateBridgeCoverData.Batch304_319

import ForestUnimodality.IntermediateBridgeCoverData.Batch320_335

import ForestUnimodality.IntermediateBridgeCoverData.Batch336_351

import ForestUnimodality.IntermediateBridgeCoverData.Batch352_367

import ForestUnimodality.IntermediateBridgeCoverData.Batch368_383

import ForestUnimodality.IntermediateBridgeCoverData.Batch384_399

import ForestUnimodality.IntermediateBridgeCoverData.Batch400_415

import ForestUnimodality.IntermediateBridgeCoverData.Batch416_431

import ForestUnimodality.IntermediateBridgeCoverData.Batch432_447

import ForestUnimodality.IntermediateBridgeCoverData.Batch448_463

import ForestUnimodality.IntermediateBridgeCoverData.Batch464_479

import ForestUnimodality.IntermediateBridgeCoverData.Batch480_495

import ForestUnimodality.IntermediateBridgeCoverData.Batch496_511

import ForestUnimodality.IntermediateBridgeCoverData.Batch512_527

import ForestUnimodality.IntermediateBridgeCoverData.Batch528_543

import ForestUnimodality.IntermediateBridgeCoverData.Batch544_559

import ForestUnimodality.IntermediateBridgeCoverData.Batch560_575

import ForestUnimodality.IntermediateBridgeCoverData.Batch576_591

import ForestUnimodality.IntermediateBridgeCoverData.Batch592_607

import ForestUnimodality.IntermediateBridgeCoverData.Batch608_615



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def cover59 : ActivityCover CellKey where
  qlo := (1/4)
  qhi := (9/13)
  lowerOrder := 59
  orderCap := 79
  bands := [band000,band004,band008,band012,band016,band020,band024,band028,band032,band036,band040,band044,band048,band052,band056,band060,band064,band068,band072,band076,band080,band084,band088,band092,band096,band100,band104,band108,band112,band116,band120,band124,band128,band132,band136,band140,band144,band148,band152,band156,band160,band164,band168,band172,band176,band180,band184,band188,band192,band196,band200,band204,band208,band212,band216,band220,band224,band228,band232,band236,band240,band244,band248,band252,band256,band260,band264,band268,band272,band276,band280,band284,band288,band292,band296,band300,band304,band308,band312,band316,band320,band324,band328,band332,band336,band340,band344,band348,band352,band356,band360,band364,band368,band372,band376,band380,band384,band388,band392,band396,band400,band404,band408,band412,band416,band420,band424,band428,band432,band436,band440,band444,band448,band452,band456,band460,band464,band468,band472,band476,band480,band484,band488,band492,band496,band500,band504,band508,band512,band516,band520,band524,band528,band532,band536,band540,band544,band548,band552,band556,band560,band564,band568,band572,band576,band580,band584,band588,band592,band596,band600,band604,band608,band612]

theorem cover59_checked : cover59.check rectangle=true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨by decide +kernel,?_⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨by decide +kernel,?_⟩
  simp only [cover59,List.all_cons,List.all_nil,band000_checked,band004_checked,band008_checked,band012_checked,band016_checked,band020_checked,band024_checked,band028_checked,band032_checked,band036_checked,band040_checked,band044_checked,band048_checked,band052_checked,band056_checked,band060_checked,band064_checked,band068_checked,band072_checked,band076_checked,band080_checked,band084_checked,band088_checked,band092_checked,band096_checked,band100_checked,band104_checked,band108_checked,band112_checked,band116_checked,band120_checked,band124_checked,band128_checked,band132_checked,band136_checked,band140_checked,band144_checked,band148_checked,band152_checked,band156_checked,band160_checked,band164_checked,band168_checked,band172_checked,band176_checked,band180_checked,band184_checked,band188_checked,band192_checked,band196_checked,band200_checked,band204_checked,band208_checked,band212_checked,band216_checked,band220_checked,band224_checked,band228_checked,band232_checked,band236_checked,band240_checked,band244_checked,band248_checked,band252_checked,band256_checked,band260_checked,band264_checked,band268_checked,band272_checked,band276_checked,band280_checked,band284_checked,band288_checked,band292_checked,band296_checked,band300_checked,band304_checked,band308_checked,band312_checked,band316_checked,band320_checked,band324_checked,band328_checked,band332_checked,band336_checked,band340_checked,band344_checked,band348_checked,band352_checked,band356_checked,band360_checked,band364_checked,band368_checked,band372_checked,band376_checked,band380_checked,band384_checked,band388_checked,band392_checked,band396_checked,band400_checked,band404_checked,band408_checked,band412_checked,band416_checked,band420_checked,band424_checked,band428_checked,band432_checked,band436_checked,band440_checked,band444_checked,band448_checked,band452_checked,band456_checked,band460_checked,band464_checked,band468_checked,band472_checked,band476_checked,band480_checked,band484_checked,band488_checked,band492_checked,band496_checked,band500_checked,band504_checked,band508_checked,band512_checked,band516_checked,band520_checked,band524_checked,band528_checked,band532_checked,band536_checked,band540_checked,band544_checked,band548_checked,band552_checked,band556_checked,band560_checked,band564_checked,band568_checked,band572_checked,band576_checked,band580_checked,band584_checked,band588_checked,band592_checked,band596_checked,band600_checked,band604_checked,band608_checked,band612_checked,Bool.and_self]

#print axioms cover59_checked

def cover80 : ActivityCover CellKey where
  qlo := (1/4)
  qhi := (9/13)
  lowerOrder := 80
  orderCap := 98
  bands := [band001,band005,band009,band013,band017,band021,band025,band029,band033,band037,band041,band045,band049,band053,band057,band061,band065,band069,band073,band077,band081,band085,band089,band093,band097,band101,band105,band109,band113,band117,band121,band125,band129,band133,band137,band141,band145,band149,band153,band157,band161,band165,band169,band173,band177,band181,band185,band189,band193,band197,band201,band205,band209,band213,band217,band221,band225,band229,band233,band237,band241,band245,band249,band253,band257,band261,band265,band269,band273,band277,band281,band285,band289,band293,band297,band301,band305,band309,band313,band317,band321,band325,band329,band333,band337,band341,band345,band349,band353,band357,band361,band365,band369,band373,band377,band381,band385,band389,band393,band397,band401,band405,band409,band413,band417,band421,band425,band429,band433,band437,band441,band445,band449,band453,band457,band461,band465,band469,band473,band477,band481,band485,band489,band493,band497,band501,band505,band509,band513,band517,band521,band525,band529,band533,band537,band541,band545,band549,band553,band557,band561,band565,band569,band573,band577,band581,band585,band589,band593,band597,band601,band605,band609,band613]

theorem cover80_checked : cover80.check rectangle=true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨by decide +kernel,?_⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨by decide +kernel,?_⟩
  simp only [cover80,List.all_cons,List.all_nil,band001_checked,band005_checked,band009_checked,band013_checked,band017_checked,band021_checked,band025_checked,band029_checked,band033_checked,band037_checked,band041_checked,band045_checked,band049_checked,band053_checked,band057_checked,band061_checked,band065_checked,band069_checked,band073_checked,band077_checked,band081_checked,band085_checked,band089_checked,band093_checked,band097_checked,band101_checked,band105_checked,band109_checked,band113_checked,band117_checked,band121_checked,band125_checked,band129_checked,band133_checked,band137_checked,band141_checked,band145_checked,band149_checked,band153_checked,band157_checked,band161_checked,band165_checked,band169_checked,band173_checked,band177_checked,band181_checked,band185_checked,band189_checked,band193_checked,band197_checked,band201_checked,band205_checked,band209_checked,band213_checked,band217_checked,band221_checked,band225_checked,band229_checked,band233_checked,band237_checked,band241_checked,band245_checked,band249_checked,band253_checked,band257_checked,band261_checked,band265_checked,band269_checked,band273_checked,band277_checked,band281_checked,band285_checked,band289_checked,band293_checked,band297_checked,band301_checked,band305_checked,band309_checked,band313_checked,band317_checked,band321_checked,band325_checked,band329_checked,band333_checked,band337_checked,band341_checked,band345_checked,band349_checked,band353_checked,band357_checked,band361_checked,band365_checked,band369_checked,band373_checked,band377_checked,band381_checked,band385_checked,band389_checked,band393_checked,band397_checked,band401_checked,band405_checked,band409_checked,band413_checked,band417_checked,band421_checked,band425_checked,band429_checked,band433_checked,band437_checked,band441_checked,band445_checked,band449_checked,band453_checked,band457_checked,band461_checked,band465_checked,band469_checked,band473_checked,band477_checked,band481_checked,band485_checked,band489_checked,band493_checked,band497_checked,band501_checked,band505_checked,band509_checked,band513_checked,band517_checked,band521_checked,band525_checked,band529_checked,band533_checked,band537_checked,band541_checked,band545_checked,band549_checked,band553_checked,band557_checked,band561_checked,band565_checked,band569_checked,band573_checked,band577_checked,band581_checked,band585_checked,band589_checked,band593_checked,band597_checked,band601_checked,band605_checked,band609_checked,band613_checked,Bool.and_self]

#print axioms cover80_checked

def cover99 : ActivityCover CellKey where
  qlo := (1/4)
  qhi := (9/13)
  lowerOrder := 99
  orderCap := 129
  bands := [band002,band006,band010,band014,band018,band022,band026,band030,band034,band038,band042,band046,band050,band054,band058,band062,band066,band070,band074,band078,band082,band086,band090,band094,band098,band102,band106,band110,band114,band118,band122,band126,band130,band134,band138,band142,band146,band150,band154,band158,band162,band166,band170,band174,band178,band182,band186,band190,band194,band198,band202,band206,band210,band214,band218,band222,band226,band230,band234,band238,band242,band246,band250,band254,band258,band262,band266,band270,band274,band278,band282,band286,band290,band294,band298,band302,band306,band310,band314,band318,band322,band326,band330,band334,band338,band342,band346,band350,band354,band358,band362,band366,band370,band374,band378,band382,band386,band390,band394,band398,band402,band406,band410,band414,band418,band422,band426,band430,band434,band438,band442,band446,band450,band454,band458,band462,band466,band470,band474,band478,band482,band486,band490,band494,band498,band502,band506,band510,band514,band518,band522,band526,band530,band534,band538,band542,band546,band550,band554,band558,band562,band566,band570,band574,band578,band582,band586,band590,band594,band598,band602,band606,band610,band614]

theorem cover99_checked : cover99.check rectangle=true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨by decide +kernel,?_⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨by decide +kernel,?_⟩
  simp only [cover99,List.all_cons,List.all_nil,band002_checked,band006_checked,band010_checked,band014_checked,band018_checked,band022_checked,band026_checked,band030_checked,band034_checked,band038_checked,band042_checked,band046_checked,band050_checked,band054_checked,band058_checked,band062_checked,band066_checked,band070_checked,band074_checked,band078_checked,band082_checked,band086_checked,band090_checked,band094_checked,band098_checked,band102_checked,band106_checked,band110_checked,band114_checked,band118_checked,band122_checked,band126_checked,band130_checked,band134_checked,band138_checked,band142_checked,band146_checked,band150_checked,band154_checked,band158_checked,band162_checked,band166_checked,band170_checked,band174_checked,band178_checked,band182_checked,band186_checked,band190_checked,band194_checked,band198_checked,band202_checked,band206_checked,band210_checked,band214_checked,band218_checked,band222_checked,band226_checked,band230_checked,band234_checked,band238_checked,band242_checked,band246_checked,band250_checked,band254_checked,band258_checked,band262_checked,band266_checked,band270_checked,band274_checked,band278_checked,band282_checked,band286_checked,band290_checked,band294_checked,band298_checked,band302_checked,band306_checked,band310_checked,band314_checked,band318_checked,band322_checked,band326_checked,band330_checked,band334_checked,band338_checked,band342_checked,band346_checked,band350_checked,band354_checked,band358_checked,band362_checked,band366_checked,band370_checked,band374_checked,band378_checked,band382_checked,band386_checked,band390_checked,band394_checked,band398_checked,band402_checked,band406_checked,band410_checked,band414_checked,band418_checked,band422_checked,band426_checked,band430_checked,band434_checked,band438_checked,band442_checked,band446_checked,band450_checked,band454_checked,band458_checked,band462_checked,band466_checked,band470_checked,band474_checked,band478_checked,band482_checked,band486_checked,band490_checked,band494_checked,band498_checked,band502_checked,band506_checked,band510_checked,band514_checked,band518_checked,band522_checked,band526_checked,band530_checked,band534_checked,band538_checked,band542_checked,band546_checked,band550_checked,band554_checked,band558_checked,band562_checked,band566_checked,band570_checked,band574_checked,band578_checked,band582_checked,band586_checked,band590_checked,band594_checked,band598_checked,band602_checked,band606_checked,band610_checked,band614_checked,Bool.and_self]

#print axioms cover99_checked

def cover130 : ActivityCover CellKey where
  qlo := (1/4)
  qhi := (9/13)
  lowerOrder := 130
  orderCap := 169
  bands := [band003,band007,band011,band015,band019,band023,band027,band031,band035,band039,band043,band047,band051,band055,band059,band063,band067,band071,band075,band079,band083,band087,band091,band095,band099,band103,band107,band111,band115,band119,band123,band127,band131,band135,band139,band143,band147,band151,band155,band159,band163,band167,band171,band175,band179,band183,band187,band191,band195,band199,band203,band207,band211,band215,band219,band223,band227,band231,band235,band239,band243,band247,band251,band255,band259,band263,band267,band271,band275,band279,band283,band287,band291,band295,band299,band303,band307,band311,band315,band319,band323,band327,band331,band335,band339,band343,band347,band351,band355,band359,band363,band367,band371,band375,band379,band383,band387,band391,band395,band399,band403,band407,band411,band415,band419,band423,band427,band431,band435,band439,band443,band447,band451,band455,band459,band463,band467,band471,band475,band479,band483,band487,band491,band495,band499,band503,band507,band511,band515,band519,band523,band527,band531,band535,band539,band543,band547,band551,band555,band559,band563,band567,band571,band575,band579,band583,band587,band591,band595,band599,band603,band607,band611,band615]

theorem cover130_checked : cover130.check rectangle=true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨by decide +kernel,?_⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨by decide +kernel,?_⟩
  simp only [cover130,List.all_cons,List.all_nil,band003_checked,band007_checked,band011_checked,band015_checked,band019_checked,band023_checked,band027_checked,band031_checked,band035_checked,band039_checked,band043_checked,band047_checked,band051_checked,band055_checked,band059_checked,band063_checked,band067_checked,band071_checked,band075_checked,band079_checked,band083_checked,band087_checked,band091_checked,band095_checked,band099_checked,band103_checked,band107_checked,band111_checked,band115_checked,band119_checked,band123_checked,band127_checked,band131_checked,band135_checked,band139_checked,band143_checked,band147_checked,band151_checked,band155_checked,band159_checked,band163_checked,band167_checked,band171_checked,band175_checked,band179_checked,band183_checked,band187_checked,band191_checked,band195_checked,band199_checked,band203_checked,band207_checked,band211_checked,band215_checked,band219_checked,band223_checked,band227_checked,band231_checked,band235_checked,band239_checked,band243_checked,band247_checked,band251_checked,band255_checked,band259_checked,band263_checked,band267_checked,band271_checked,band275_checked,band279_checked,band283_checked,band287_checked,band291_checked,band295_checked,band299_checked,band303_checked,band307_checked,band311_checked,band315_checked,band319_checked,band323_checked,band327_checked,band331_checked,band335_checked,band339_checked,band343_checked,band347_checked,band351_checked,band355_checked,band359_checked,band363_checked,band367_checked,band371_checked,band375_checked,band379_checked,band383_checked,band387_checked,band391_checked,band395_checked,band399_checked,band403_checked,band407_checked,band411_checked,band415_checked,band419_checked,band423_checked,band427_checked,band431_checked,band435_checked,band439_checked,band443_checked,band447_checked,band451_checked,band455_checked,band459_checked,band463_checked,band467_checked,band471_checked,band475_checked,band479_checked,band483_checked,band487_checked,band491_checked,band495_checked,band499_checked,band503_checked,band507_checked,band511_checked,band515_checked,band519_checked,band523_checked,band527_checked,band531_checked,band535_checked,band539_checked,band543_checked,band547_checked,band551_checked,band555_checked,band559_checked,band563_checked,band567_checked,band571_checked,band575_checked,band579_checked,band583_checked,band587_checked,band591_checked,band595_checked,band599_checked,band603_checked,band607_checked,band611_checked,band615_checked,Bool.and_self]

#print axioms cover130_checked

end ForestUnimodality.IntermediateBridgeCoverData

