import ForestUnimodality.KernelCertificate
import ForestUnimodality.FiniteWitness
import Mathlib.Tactic.IntervalCases

/-! Generated candidate witnesses. Each sign is rechecked by the Lean kernel.
The coverage theorem quantifies over Domain, independently of this record list.
Source and integer-witness hashes are recorded in research/finite-integer-witnesses/manifest.json.
-/
namespace ForestUnimodality.FiniteRows.FiniteData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_37_19_1_checked :
    (Witness.rising).check 37 19 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_19_2_checked :
    (Witness.rising).check 37 19 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_19_3_checked :
    (Witness.rising).check 37 19 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_19_4_checked :
    (Witness.rising).check 37 19 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_19_5_checked :
    (Witness.rising).check 37 19 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_19_6_checked :
    (Witness.rising).check 37 19 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_19_7_checked :
    (Witness.rising).check 37 19 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_19_8_checked :
    (Witness.rising).check 37 19 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_19_9 : Certificate := {
  objectiveScale := 3929360292000000
  eta := 23828583857158080000
  rows := #[⟨.count 2, 6041246848491254400⟩, ⟨.count 3, 1006582457789508600⟩, ⟨.count 4, 182919423138772320⟩, ⟨.count 5, 40798940847865200⟩, ⟨.count 6, 11321272873310400⟩, ⟨.count 7, 4582419972530400⟩, ⟨.count 8, 3920787142272000⟩, ⟨.path 9, 631530438739200⟩, ⟨.path 10, 886427960418000⟩, ⟨.privateRow 8 2, 21441804684300⟩, ⟨.privateRow 9 0, 143019621894240⟩, ⟨.privateRow 10 0, 88707809093904⟩, ⟨.hall 10 2, 19059381941600⟩, ⟨.hall 7 3, 20693043250880⟩, ⟨.hall 11 4, 31287531325050⟩, ⟨.hall 6 5, 10277704390800⟩, ⟨.hall 6 6, 971348855400⟩, ⟨.hall 5 8, 13391577399200⟩, ⟨.hall 10 8, 266831347182400⟩, ⟨.hall 8 10, 57920719147200⟩, ⟨.hall 4 12, 229506075935136⟩, ⟨.hall 3 15, 6898900657173525⟩]
  caps := #[0, 11066791986993600, 1384856846287200, 0, 0, 0, 0, 0, 8573149728000, 14080504669920, 18463706797536, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_37_19_9_checked :
    (Witness.linear .positive case_37_19_9).check 37 19 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_19_10 : Certificate := {
  objectiveScale := 5148000000
  eta := 39491665012800
  rows := #[⟨.count 2, 11283332860800⟩, ⟨.count 3, 2213019408600⟩, ⟨.count 4, 466050705120⟩, ⟨.count 5, 116976459600⟩, ⟨.count 6, 33772939200⟩, ⟨.count 7, 11515303800⟩, ⟨.count 8, 5145940800⟩, ⟨.count 9, 5176211040⟩, ⟨.path 11, 1281680400⟩, ⟨.path 12, 264726000⟩, ⟨.privateRow 4 15, 23807543760⟩, ⟨.privateRow 8 4, 22072050⟩, ⟨.privateRow 10 0, 263351088⟩, ⟨.privateRow 11 0, 142942800⟩, ⟨.privateRow 12 0, 32207175⟩, ⟨.hall 8 3, 54348840⟩, ⟨.hall 7 5, 38963925⟩, ⟨.hall 8 5, 2256800⟩, ⟨.hall 6 7, 46500300⟩, ⟨.hall 9 9, 217945728⟩, ⟨.hall 5 10, 198326700⟩, ⟨.hall 8 10, 9172800⟩, ⟨.hall 4 13, 4026326304⟩]
  caps := #[0, 0, 0, 0, 583616880, 214830000, 0, 62376600, 9632700, 0, 71321184, 0, 7068600, 0, 0, 0, 0, 0, 0] }

theorem case_37_19_10_checked :
    (Witness.linear .positive case_37_19_10).check 37 19 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_19_11 : Certificate := {
  objectiveScale := 14014000000
  eta := 110380430160000
  rows := #[⟨.count 2, 27963042307200⟩, ⟨.count 3, 7109798295600⟩, ⟨.count 4, 1839673836000⟩, ⟨.count 5, 565815650400⟩, ⟨.count 6, 189080892000⟩, ⟨.count 7, 71589117600⟩, ⟨.count 8, 32994561600⟩, ⟨.count 9, 21522140640⟩, ⟨.count 10, 21491870400⟩, ⟨.path 10, 3954436200⟩, ⟨.privateRow 8 5, 243243000⟩, ⟨.privateRow 10 1, 1106545440⟩, ⟨.privateRow 11 0, 1929727800⟩, ⟨.privateRow 12 0, 1754052300⟩, ⟨.hall 9 2, 13621608⟩, ⟨.hall 9 3, 321080760⟩, ⟨.hall 8 4, 420376320⟩, ⟨.hall 7 6, 417867450⟩, ⟨.hall 8 7, 20409480⟩, ⟨.hall 6 8, 707081760⟩, ⟨.hall 10 8, 639038400⟩, ⟨.hall 5 10, 1818917100⟩, ⟨.hall 4 13, 42956641728⟩, ⟨.hall 3 15, 444362393475⟩, ⟨.assumptionRow 11, 17620772400⟩]
  caps := #[0, 313377292800, 33233714800, 1025596000, 907645200, 557597040, 74560200, 180991800, 177276000, 61385984, 324335880, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_37_19_11_checked :
    (Witness.linear .conditional case_37_19_11).check 37 19 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_19_12 : Certificate := {
  objectiveScale := 1591228548000000
  eta := 7454942663882313600
  rows := #[⟨.count 2, 1940327542654300800⟩, ⟨.count 3, 520374220998231600⟩, ⟨.count 4, 157989518178972480⟩, ⟨.count 5, 50310350370680400⟩, ⟨.count 6, 16932399370286400⟩, ⟨.count 7, 5978325216263400⟩, ⟨.count 8, 2625527104200000⟩, ⟨.count 9, 1266554275066080⟩, ⟨.count 10, 840168673344000⟩, ⟨.count 11, 837543146239800⟩, ⟨.count 13, 1609073039574000⟩, ⟨.path 9, 405798599606400⟩, ⟨.path 10, 18539436286800⟩, ⟨.privateRow 3 16, 50685800746581000⟩, ⟨.privateRow 12 0, 102629979126675⟩, ⟨.hall 10 2, 78265712725200⟩, ⟨.hall 9 3, 75345126384528⟩, ⟨.hall 10 4, 8835107080800⟩, ⟨.hall 8 5, 63777955659600⟩, ⟨.hall 7 7, 96714208135545⟩, ⟨.hall 9 7, 42060944209284⟩, ⟨.hall 8 8, 34709998727040⟩, ⟨.hall 6 9, 255339723870000⟩, ⟨.hall 7 9, 33125400297990⟩, ⟨.hall 5 10, 283503345067800⟩, ⟨.hall 4 12, 1075355889832224⟩, ⟨.hall 3 15, 86447449051113150⟩, ⟨.assumptionRow 12, 830152773650200⟩]
  caps := #[0, 10732504220240400, 0, 29468831935400, 27724831013880, 97876071373080, 26027298125400, 0, 8133684897000, 6475970764120, 8523536593000, 14365257725000, 0, 0, 0, 0, 0, 0, 0] }

theorem case_37_19_12_checked :
    (Witness.linear .conditional case_37_19_12).check 37 19 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_20_1_checked :
    (Witness.rising).check 37 20 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_20_2_checked :
    (Witness.rising).check 37 20 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_20_3_checked :
    (Witness.rising).check 37 20 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_20_4_checked :
    (Witness.rising).check 37 20 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_20_5_checked :
    (Witness.rising).check 37 20 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_20_6_checked :
    (Witness.rising).check 37 20 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_20_7_checked :
    (Witness.rising).check 37 20 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_20_8_checked :
    (Witness.rising).check 37 20 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_20_9 : Certificate := {
  objectiveScale := 1306800000
  eta := 10721719008000
  rows := #[⟨.count 2, 2377424649600⟩, ⟨.count 3, 360109910160⟩, ⟨.count 4, 66261555360⟩, ⟨.count 5, 14215370400⟩, ⟨.count 6, 3841992000⟩, ⟨.count 7, 1548439200⟩, ⟨.count 8, 1303948800⟩, ⟨.path 9, 242945010⟩, ⟨.path 10, 273637980⟩, ⟨.privateRow 5 11, 696681216⟩, ⟨.privateRow 6 7, 17342325⟩, ⟨.privateRow 6 8, 301870800⟩, ⟨.privateRow 6 9, 391314000⟩, ⟨.privateRow 6 10, 469576800⟩, ⟨.privateRow 7 4, 5821200⟩, ⟨.privateRow 7 5, 123538800⟩, ⟨.privateRow 7 6, 173908350⟩, ⟨.privateRow 7 7, 184615200⟩, ⟨.privateRow 8 2, 57047760⟩, ⟨.privateRow 8 3, 70494732⟩, ⟨.privateRow 9 0, 41352080⟩, ⟨.privateRow 10 0, 24819480⟩, ⟨.hall 10 3, 2668050⟩, ⟨.hall 4 13, 15261246⟩, ⟨.hall 4 14, 418990572⟩, ⟨.hall 5 14, 1374579360⟩, ⟨.hall 3 16, 6992425440⟩]
  caps := #[0, 0, 0, 681801120, 0, 34102530, 102618285, 1305810, 2851200, 0, 8032500, 0, 0, 0, 0, 0, 0, 0] }

theorem case_37_20_9_checked :
    (Witness.linear .positive case_37_20_9).check 37 20 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_20_10 : Certificate := {
  objectiveScale := 242000000
  eta := 2452898448000
  rows := #[⟨.count 2, 542884141800⟩, ⟨.count 3, 108216108000⟩, ⟨.count 4, 23910606720⟩, ⟨.count 5, 5945940000⟩, ⟨.count 6, 1625223600⟩, ⟨.count 7, 554954400⟩, ⟨.count 8, 242161920⟩, ⟨.count 9, 242161920⟩, ⟨.path 11, 70583040⟩, ⟨.privateRow 9 2, 3251248⟩, ⟨.privateRow 10 0, 6650280⟩, ⟨.privateRow 11 0, 7027020⟩, ⟨.hall 8 4, 789880⟩, ⟨.hall 9 4, 301392⟩, ⟨.hall 7 5, 712950⟩, ⟨.hall 6 7, 726825⟩, ⟨.hall 7 7, 176400⟩, ⟨.hall 5 10, 498960⟩]
  caps := #[0, 2789621120, 835263000, 0, 47160960, 0, 8274640, 2044900, 3914768, 0, 0, 312840, 0, 0, 0, 0, 0, 0] }

theorem case_37_20_10_checked :
    (Witness.linear .positive case_37_20_10).check 37 20 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_20_11 : Certificate := {
  objectiveScale := 918000000
  eta := 12844268236800
  rows := #[⟨.count 2, 2976926752800⟩, ⟨.count 3, 700748488440⟩, ⟨.count 4, 185400895680⟩, ⟨.count 5, 50356706400⟩, ⟨.count 6, 16448632200⟩, ⟨.count 7, 6023089800⟩, ⟨.count 8, 2666532960⟩, ⟨.count 9, 1637344800⟩, ⟨.count 10, 1520391600⟩, ⟨.path 10, 305987760⟩, ⟨.privateRow 3 17, 34006092120⟩, ⟨.privateRow 6 10, 2468826360⟩, ⟨.privateRow 6 11, 742792050⟩, ⟨.privateRow 7 7, 194524200⟩, ⟨.privateRow 7 8, 1108270800⟩, ⟨.privateRow 7 9, 2546238240⟩, ⟨.privateRow 7 10, 1518303150⟩, ⟨.privateRow 8 5, 172505970⟩, ⟨.privateRow 8 6, 558869220⟩, ⟨.privateRow 8 7, 1317672720⟩, ⟨.privateRow 8 8, 1553138496⟩, ⟨.privateRow 9 3, 121284800⟩, ⟨.privateRow 9 4, 376199460⟩, ⟨.privateRow 9 5, 640086720⟩, ⟨.privateRow 10 1, 91808262⟩, ⟨.privateRow 10 2, 230007960⟩, ⟨.privateRow 11 0, 115282440⟩, ⟨.privateRow 12 0, 102102000⟩, ⟨.hall 6 10, 31120200⟩, ⟨.hall 5 11, 127369440⟩, ⟨.hall 6 11, 51583950⟩, ⟨.hall 4 13, 760842225⟩, ⟨.hall 3 15, 4586887305⟩, ⟨.assumptionRow 11, 1329264000⟩]
  caps := #[0, 3541056480, 0, 847154880, 309188880, 0, 68918850, 11520900, 12312522, 0, 36794358, 0, 0, 0, 0, 0, 0, 0] }

theorem case_37_20_11_checked :
    (Witness.linear .conditional case_37_20_11).check 37 20 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_20_12 : Certificate := {
  objectiveScale := 14994000000
  eta := 68435866699200
  rows := #[⟨.count 2, 18764673127200⟩, ⟨.count 3, 5316657386040⟩, ⟨.count 4, 1597888131840⟩, ⟨.count 5, 515512998000⟩, ⟨.count 6, 180934954200⟩, ⟨.count 7, 70113443400⟩, ⟨.count 8, 30361050720⟩, ⟨.count 9, 18010792800⟩, ⟨.count 10, 5789183400⟩, ⟨.count 11, 11118907800⟩, ⟨.count 13, 15768632880⟩, ⟨.path 9, 3139527105⟩, ⟨.privateRow 2 18, 1609714606500⟩, ⟨.privateRow 6 10, 42925722840⟩, ⟨.privateRow 6 11, 37610547975⟩, ⟨.privateRow 7 8, 16310794500⟩, ⟨.privateRow 7 9, 49860490680⟩, ⟨.privateRow 7 10, 49070221200⟩, ⟨.privateRow 8 6, 6165939780⟩, ⟨.privateRow 8 7, 22417004610⟩, ⟨.privateRow 8 8, 39868176348⟩, ⟨.privateRow 8 9, 34413479100⟩, ⟨.privateRow 9 4, 2229907680⟩, ⟨.privateRow 9 5, 7343175840⟩, ⟨.privateRow 9 6, 27397370000⟩, ⟨.privateRow 9 7, 9651497856⟩, ⟨.privateRow 10 1, 514594080⟩, ⟨.privateRow 10 3, 5467562100⟩, ⟨.privateRow 10 4, 9152423280⟩, ⟨.privateRow 11 1, 2797594800⟩, ⟨.privateRow 11 2, 1412836425⟩, ⟨.privateRow 12 0, 973372400⟩, ⟨.hall 6 10, 849999150⟩, ⟨.hall 6 11, 3098150550⟩, ⟨.hall 5 12, 13677404400⟩, ⟨.hall 7 12, 75655225800⟩, ⟨.hall 4 13, 21419059662⟩, ⟨.hall 3 15, 173145772800⟩, ⟨.hall 2 17, 2580653575500⟩, ⟨.assumptionRow 12, 10892712600⟩]
  caps := #[0, 116752529790, 11659876020, 5953822875, 530969670, 0, 0, 689844870, 0, 594349393, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_37_20_12_checked :
    (Witness.linear .conditional case_37_20_12).check 37 20 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_21_1_checked :
    (Witness.rising).check 37 21 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_21_2_checked :
    (Witness.rising).check 37 21 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_21_3_checked :
    (Witness.rising).check 37 21 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_21_4_checked :
    (Witness.rising).check 37 21 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_21_5_checked :
    (Witness.rising).check 37 21 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_21_6_checked :
    (Witness.rising).check 37 21 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_21_7_checked :
    (Witness.rising).check 37 21 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_21_8_checked :
    (Witness.rising).check 37 21 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_21_9 : Certificate := {
  objectiveScale := 386100000
  eta := 3846590748000
  rows := #[⟨.count 2, 680121842400⟩, ⟨.count 3, 107991243360⟩, ⟨.count 4, 20142682560⟩, ⟨.count 5, 4349545200⟩, ⟨.count 6, 1169532000⟩, ⟨.count 7, 467812800⟩, ⟨.count 8, 395041920⟩, ⟨.path 9, 78289200⟩, ⟨.path 10, 75604320⟩, ⟨.privateRow 5 12, 867458592⟩, ⟨.privateRow 6 10, 705432000⟩, ⟨.privateRow 7 10, 294722064⟩, ⟨.privateRow 8 7, 29331120⟩, ⟨.privateRow 8 10, 62375040⟩, ⟨.privateRow 9 0, 999600⟩, ⟨.privateRow 9 4, 13861120⟩, ⟨.privateRow 10 0, 6404580⟩, ⟨.hall 5 10, 44625⟩, ⟨.hall 4 12, 1368576⟩, ⟨.hall 3 15, 44114070⟩]
  caps := #[0, 7456363200, 0, 99150480, 114354240, 0, 0, 0, 0, 16607600, 0, 0, 0, 0, 0, 0, 0] }

theorem case_37_21_9_checked :
    (Witness.linear .positive case_37_21_9).check 37 21 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_21_10 : Certificate := {
  objectiveScale := 108900000
  eta := 1747690144200
  rows := #[⟨.count 2, 352604151900⟩, ⟨.count 3, 77967129240⟩, ⟨.count 4, 17453315880⟩, ⟨.count 5, 4015161150⟩, ⟨.count 6, 1087386300⟩, ⟨.count 7, 321621300⟩, ⟨.count 8, 133413280⟩, ⟨.count 9, 107207100⟩, ⟨.path 10, 23097690⟩, ⟨.path 11, 13201650⟩, ⟨.privateRow 10 2, 612612⟩, ⟨.privateRow 11 0, 1160250⟩, ⟨.hall 11 1, 2246244⟩, ⟨.hall 9 3, 69615⟩, ⟨.hall 8 8, 253232⟩]
  caps := #[0, 0, 361003500, 0, 0, 4086390, 0, 1771110, 0, 1692900, 0, 438900, 0, 0, 0, 0, 0] }

theorem case_37_21_10_checked :
    (Witness.linear .positive case_37_21_10).check 37 21 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_21_11 : Certificate := {
  objectiveScale := 104652000000
  eta := 1929449919196800
  rows := #[⟨.count 2, 420843786723360⟩, ⟨.count 3, 96472495959840⟩, ⟨.count 4, 25812039052800⟩, ⟨.count 5, 7067582121600⟩, ⟨.count 6, 2157987031200⟩, ⟨.count 7, 777294357840⟩, ⟨.count 8, 338945967360⟩, ⟨.count 9, 293318625600⟩, ⟨.count 10, 20951330400⟩, ⟨.path 10, 38256831360⟩, ⟨.privateRow 4 15, 3218822727120⟩, ⟨.privateRow 5 12, 420982065504⟩, ⟨.privateRow 5 13, 1307886800220⟩, ⟨.privateRow 5 14, 2560718160000⟩, ⟨.privateRow 6 10, 330565435200⟩, ⟨.privateRow 6 11, 632730178080⟩, ⟨.privateRow 6 12, 1092961069200⟩, ⟨.privateRow 6 13, 1186078093200⟩, ⟨.privateRow 7 7, 12570798240⟩, ⟨.privateRow 7 8, 181079355600⟩, ⟨.privateRow 7 9, 215798703120⟩, ⟨.privateRow 7 10, 761371346736⟩, ⟨.privateRow 7 11, 294889975380⟩, ⟨.privateRow 8 5, 18468209760⟩, ⟨.privateRow 8 6, 95124859830⟩, ⟨.privateRow 8 7, 180181441440⟩, ⟨.privateRow 8 8, 205051446600⟩, ⟨.privateRow 9 3, 16458433992⟩, ⟨.privateRow 9 4, 59387968640⟩, ⟨.privateRow 9 5, 72718575930⟩, ⟨.privateRow 10 0, 14142148020⟩, ⟨.privateRow 10 2, 23884516656⟩, ⟨.privateRow 11 0, 11745442800⟩, ⟨.privateRow 12 0, 10755016272⟩, ⟨.hall 5 15, 1097107686675⟩, ⟨.hall 4 16, 5769749905920⟩, ⟨.hall 3 17, 13016130407280⟩, ⟨.hall 2 18, 14202282013920⟩, ⟨.assumptionRow 11, 163140258600⟩]
  caps := #[0, 0, 423615947040, 132670755360, 19787367600, 13865242248, 11750889150, 6104540970, 0, 7073500500, 22520693844, 12734404200, 0, 0, 0, 0, 0] }

theorem case_37_21_11_checked :
    (Witness.linear .conditional case_37_21_11).check 37 21 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_21_12 : Certificate := {
  objectiveScale := 48837600000
  eta := 639654592777200
  rows := #[⟨.count 2, 159855391856160⟩, ⟨.count 3, 39947203296000⟩, ⟨.count 4, 11431045866240⟩, ⟨.count 5, 3418558743600⟩, ⟨.count 6, 1089469180800⟩, ⟨.count 7, 371536925760⟩, ⟨.count 8, 143400216960⟩, ⟨.count 9, 58663725120⟩, ⟨.count 10, 62853991200⟩, ⟨.path 9, 15101119440⟩, ⟨.privateRow 2 19, 3961430993520⟩, ⟨.privateRow 4 15, 1884688565760⟩, ⟨.privateRow 5 12, 107550162720⟩, ⟨.privateRow 5 13, 738767189160⟩, ⟨.privateRow 5 14, 1666173949440⟩, ⟨.privateRow 6 10, 78567489000⟩, ⟨.privateRow 6 11, 320089770000⟩, ⟨.privateRow 6 12, 714964149900⟩, ⟨.privateRow 6 13, 952121570400⟩, ⟨.privateRow 7 8, 41403819600⟩, ⟨.privateRow 7 9, 148638049560⟩, ⟨.privateRow 7 10, 329075562816⟩, ⟨.privateRow 7 11, 457262785980⟩, ⟨.privateRow 7 12, 372235303440⟩, ⟨.privateRow 8 6, 19215085890⟩, ⟨.privateRow 8 7, 72631278720⟩, ⟨.privateRow 8 8, 157522965600⟩, ⟨.privateRow 8 9, 255513113856⟩, ⟨.privateRow 9 4, 7966678720⟩, ⟨.privateRow 9 5, 37479602160⟩, ⟨.privateRow 9 6, 90711500880⟩, ⟨.privateRow 9 7, 44993628680⟩, ⟨.privateRow 10 2, 1885619736⟩, ⟨.privateRow 10 3, 21184122960⟩, ⟨.privateRow 10 4, 33696723060⟩, ⟨.privateRow 11 0, 3915147600⟩, ⟨.privateRow 11 1, 6983776800⟩, ⟨.privateRow 11 2, 3750546800⟩, ⟨.privateRow 12 0, 3072861792⟩, ⟨.hall 5 15, 1646061642225⟩, ⟨.hall 4 16, 4846083802560⟩, ⟨.hall 3 17, 9465267892080⟩, ⟨.hall 2 18, 11749383565920⟩, ⟨.assumptionRow 12, 43493371200⟩]
  caps := #[0, 1878726657600, 60341645520, 106321438080, 22087905840, 4574592000, 0, 2475132660, 0, 3306296400, 2244645864, 4761020000, 12265493472, 48837600000, 0, 0, 0] }

theorem case_37_21_12_checked :
    (Witness.linear .conditional case_37_21_12).check 37 21 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_21_13 : Certificate := {
  objectiveScale := 1081979791200000
  eta := 20345315368069692000
  rows := #[⟨.count 2, 4803090137873707680⟩, ⟨.count 3, 1119847190427365400⟩, ⟨.count 4, 290384333113754880⟩, ⟨.count 5, 75840111154407600⟩, ⟨.count 6, 19846755309981600⟩, ⟨.count 7, 5021468210959200⟩, ⟨.count 8, 1115881824657600⟩, ⟨.count 9, 585837957945240⟩, ⟨.count 11, 438382145401200⟩, ⟨.count 12, 526058574481440⟩, ⟨.path 8, 725005424183040⟩, ⟨.privateRow 2 19, 107710493125074840⟩, ⟨.privateRow 4 15, 51246872797400280⟩, ⟨.privateRow 5 12, 2665363444039296⟩, ⟨.privateRow 5 13, 18861391805886630⟩, ⟨.privateRow 5 14, 46775374914308040⟩, ⟨.privateRow 6 10, 1733602120450200⟩, ⟨.privateRow 6 11, 7560099362055240⟩, ⟨.privateRow 6 12, 19119439477838700⟩, ⟨.privateRow 6 13, 29232118513798200⟩, ⟨.privateRow 7 8, 758344178797920⟩, ⟨.privateRow 7 9, 3150373508542260⟩, ⟨.privateRow 7 10, 8251946093342952⟩, ⟨.privateRow 7 11, 13617743553053640⟩, ⟨.privateRow 7 12, 15319463335656480⟩, ⟨.privateRow 8 6, 247586279845905⟩, ⟨.privateRow 8 7, 1304518990254480⟩, ⟨.privateRow 8 8, 3783149352762780⟩, ⟨.privateRow 8 9, 6821757554740128⟩, ⟨.privateRow 8 10, 7581022146267570⟩, ⟨.privateRow 9 4, 32029941263320⟩, ⟨.privateRow 9 5, 502146821095920⟩, ⟨.privateRow 9 6, 1538322801135120⟩, ⟨.privateRow 9 7, 4296145024931760⟩, ⟨.privateRow 9 8, 1534337508904200⟩, ⟨.privateRow 10 2, 35867630078280⟩, ⟨.privateRow 10 3, 54465660489240⟩, ⟨.privateRow 10 4, 883240390677645⟩, ⟨.privateRow 10 5, 1948807900919880⟩, ⟨.privateRow 11 2, 254615892531000⟩, ⟨.privateRow 11 3, 754714716230475⟩, ⟨.privateRow 12 1, 292254763600800⟩, ⟨.privateRow 13 0, 73063690900200⟩, ⟨.hall 6 14, 11652994483210080⟩, ⟨.hall 5 15, 65620327389742125⟩, ⟨.hall 4 16, 157229624525893920⟩, ⟨.hall 3 17, 283998566529077400⟩, ⟨.hall 2 18, 342238019091368400⟩, ⟨.assumptionRow 13, 356920542667080⟩]
  caps := #[0, 37935214426380600, 0, 0, 21613245496920, 194765510531592, 22525437124080, 31187256274440, 11469456239241, 27635233222520, 0, 0, 113612249711520, 0, 1081979791200000, 0, 0] }

theorem case_37_21_13_checked :
    (Witness.linear .conditional case_37_21_13).check 37 21 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_22_1_checked :
    (Witness.rising).check 37 22 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_22_2_checked :
    (Witness.rising).check 37 22 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_22_3_checked :
    (Witness.rising).check 37 22 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_22_4_checked :
    (Witness.rising).check 37 22 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_22_5_checked :
    (Witness.rising).check 37 22 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_22_6_checked :
    (Witness.rising).check 37 22 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_22_7_checked :
    (Witness.rising).check 37 22 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_22_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_37_22_8_checked :
    (Witness.linear .positive case_37_22_8).check 37 22 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_22_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_37_22_9_checked :
    (Witness.linear .positive case_37_22_9).check 37 22 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_22_10 : Certificate := {
  objectiveScale := 357500
  eta := 7512001497
  rows := #[⟨.count 2, 1598100504⟩, ⟨.count 3, 351639288⟩, ⟨.count 4, 76831755⟩, ⟨.count 5, 18842460⟩, ⟨.count 6, 4678128⟩, ⟨.count 7, 1364454⟩, ⟨.count 8, 454818⟩, ⟨.count 9, 389844⟩, ⟨.path 10, 134057⟩]
  caps := #[0, 0, 1560702, 0, 0, 0, 13867, 0, 36739, 0, 0, 0, 0, 0, 0, 0] }

theorem case_37_22_10_checked :
    (Witness.linear .positive case_37_22_10).check 37 22 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_22_11 : Certificate := {
  objectiveScale := 1425000
  eta := 46605070512
  rows := #[⟨.count 2, 10894691808⟩, ⟨.count 3, 2799330534⟩, ⟨.count 4, 719716998⟩, ⟨.count 5, 185175900⟩, ⟨.count 6, 51320178⟩, ⟨.count 7, 15637076⟩, ⟨.count 8, 4938024⟩, ⟨.count 9, 2116296⟩, ⟨.count 10, 1763580⟩, ⟨.path 9, 559845⟩]
  caps := #[0, 0, 0, 2693691, 803517, 0, 0, 0, 151356, 0, 0, 0, 0, 0, 0, 0] }

theorem case_37_22_11_checked :
    (Witness.linear .positive case_37_22_11).check 37 22 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_22_12 : Certificate := {
  objectiveScale := 250209269100000
  eta := 8538464168976661920
  rows := #[⟨.count 2, 1796925105551656080⟩, ⟨.count 3, 424120924685137680⟩, ⟨.count 4, 98552226745692720⟩, ⟨.count 5, 26047785750386400⟩, ⟨.count 6, 7127361155874960⟩, ⟨.count 7, 2070465021184560⟩, ⟨.count 8, 667891942317600⟩, ⟨.count 9, 257615463465360⟩, ⟨.count 10, 143119701925200⟩, ⟨.path 8, 193721743094880⟩, ⟨.privateRow 2 20, 51165293438259000⟩, ⟨.privateRow 3 17, 1364407825020240⟩, ⟨.privateRow 3 18, 49590976717081800⟩, ⟨.privateRow 4 15, 7891262564900715⟩, ⟨.privateRow 4 16, 21384468795990300⟩, ⟨.privateRow 5 13, 5438548673157600⟩, ⟨.privateRow 5 14, 9424432371774420⟩, ⟨.privateRow 5 15, 16315646019472800⟩, ⟨.privateRow 6 10, 372111225005520⟩, ⟨.privateRow 6 11, 2409181649074200⟩, ⟨.privateRow 6 12, 4588417643721912⟩, ⟨.privateRow 6 13, 7363508664051540⟩, ⟨.privateRow 6 14, 7642592082805680⟩, ⟨.privateRow 7 8, 314863344235440⟩, ⟨.privateRow 7 9, 1132690212379440⟩, ⟨.privateRow 7 10, 2169058593621920⟩, ⟨.privateRow 7 11, 3759277503901920⟩, ⟨.privateRow 7 12, 2041841080799520⟩, ⟨.privateRow 8 6, 186453167230330⟩, ⟨.privateRow 8 7, 605277072725325⟩, ⟨.privateRow 8 8, 1128260316843660⟩, ⟨.privateRow 8 9, 1513888402586560⟩, ⟨.privateRow 9 4, 91596609232128⟩, ⟨.privateRow 9 5, 359389473723280⟩, ⟨.privateRow 9 6, 676240591596570⟩, ⟨.privateRow 10 2, 32527204983000⟩, ⟨.privateRow 10 3, 233285114138076⟩, ⟨.privateRow 10 4, 68379413142040⟩, ⟨.privateRow 11 1, 85871821155120⟩, ⟨.privateRow 12 0, 21467955288780⟩, ⟨.privateRow 13 0, 31486334423544⟩, ⟨.hall 5 16, 2096282692904400⟩, ⟨.hall 4 17, 27865405964836440⟩, ⟨.hall 3 18, 76213501059936240⟩, ⟨.hall 2 19, 61603013299663836⟩, ⟨.assumptionRow 12, 240057395961075⟩]
  caps := #[0, 4562168791651380, 683022815010900, 425679827124552, 0, 189467265067080, 14269355691780, 77377936380030, 17090516192750, 0, 96032966755194, 154185574805955, 358793468702865, 0, 0, 0] }

theorem case_37_22_12_checked :
    (Witness.linear .conditional case_37_22_12).check 37 22 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_22_13 : Certificate := {
  objectiveScale := 18681160145760000
  eta := 911096339512241282400
  rows := #[⟨.count 2, 177798854395380778560⟩, ⟨.count 3, 38083562522427502080⟩, ⟨.count 4, 7757762736050046720⟩, ⟨.count 5, 1694434599963705600⟩, ⟨.count 6, 346901137695272160⟩, ⟨.count 7, 64113741620248320⟩, ⟨.count 8, 8014217702531040⟩, ⟨.count 9, 6869329459312320⟩, ⟨.count 10, 5724441216093600⟩, ⟨.count 11, 12593770675405920⟩, ⟨.path 7, 37106957141654400⟩, ⟨.privateRow 2 20, 4092975469506924000⟩, ⟨.privateRow 3 18, 4584132525847754880⟩, ⟨.privateRow 4 15, 635985419107998960⟩, ⟨.privateRow 4 16, 1901659371986293920⟩, ⟨.privateRow 5 12, 1144888243218720⟩, ⟨.privateRow 5 13, 413533633450601664⟩, ⟨.privateRow 5 14, 800276882009885280⟩, ⟨.privateRow 5 15, 1551323569561365600⟩, ⟨.privateRow 6 10, 22161765279448080⟩, ⟨.privateRow 6 11, 168203164399550280⟩, ⟨.privateRow 6 12, 366936681951599760⟩, ⟨.privateRow 6 13, 681924059867150100⟩, ⟨.privateRow 6 14, 848171373517868400⟩, ⟨.privateRow 7 8, 14263399363433220⟩, ⟨.privateRow 7 9, 70165293762975840⟩, ⟨.privateRow 7 10, 161938081513047840⟩, ⟨.privateRow 7 11, 230504166301368960⟩, ⟨.privateRow 7 12, 640374157373670720⟩, ⟨.privateRow 8 6, 5120194643283720⟩, ⟨.privateRow 8 7, 31305537900511875⟩, ⟨.privateRow 8 8, 76564401265251900⟩, ⟨.privateRow 8 9, 169912546151578230⟩, ⟨.privateRow 8 10, 171704614276727532⟩, ⟨.privateRow 9 4, 267140590084368⟩, ⟨.privateRow 9 5, 13569045845555200⟩, ⟨.privateRow 9 6, 40166495866256760⟩, ⟨.privateRow 9 7, 96334167893689440⟩, ⟨.privateRow 9 8, 23406604083582720⟩, ⟨.privateRow 10 3, 2747731783724928⟩, ⟨.privateRow 10 4, 22070901133160880⟩, ⟨.privateRow 10 5, 37351978935010740⟩, ⟨.privateRow 11 2, 6869329459312320⟩, ⟨.privateRow 11 3, 13357029504218400⟩, ⟨.privateRow 12 1, 5352352537047516⟩, ⟨.privateRow 13 0, 1259377067540592⟩, ⟨.hall 5 16, 745524285437131200⟩, ⟨.hall 4 17, 3271581759899893440⟩, ⟨.hall 3 18, 7655686910575704000⟩, ⟨.hall 2 19, 6024859891114192128⟩, ⟨.assumptionRow 13, 9008989480292760⟩]
  caps := #[0, 354578513704254000, 0, 8216583335303616, 6345057334936320, 0, 0, 1956162150451080, 996886381305997, 5300711413907624, 536816480474232, 0, 27134585267003676, 0, 18681160145760000, 0] }

theorem case_37_22_13_checked :
    (Witness.linear .conditional case_37_22_13).check 37 22 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_22_14 : Certificate := {
  objectiveScale := 3166046699200000
  eta := 122747585570120871360
  rows := #[⟨.count 2, 27113512298802209280⟩, ⟨.count 3, 6631022029598366400⟩, ⟨.count 4, 1605803055600744000⟩, ⟨.count 5, 382988322351835200⟩, ⟨.count 6, 88619719432083840⟩, ⟨.count 7, 19235287938746880⟩, ⟨.count 8, 3205881323124480⟩, ⟨.path 8, 3166348490585280⟩, ⟨.privateRow 5 13, 41149776697533504⟩, ⟨.privateRow 6 11, 21410707408009920⟩, ⟨.privateRow 6 12, 5427099097003584⟩, ⟨.privateRow 6 14, 332152204228004160⟩, ⟨.privateRow 7 9, 8718034414415040⟩, ⟨.privateRow 7 10, 26047785750386400⟩, ⟨.privateRow 7 13, 365661297105424320⟩, ⟨.privateRow 8 7, 3068128610021475⟩, ⟨.privateRow 8 8, 10991593107855360⟩, ⟨.privateRow 8 11, 141735018809073690⟩, ⟨.privateRow 8 12, 59275409880687000⟩, ⟨.privateRow 9 5, 63608756411200⟩, ⟨.privateRow 9 6, 6082587331821000⟩, ⟨.privateRow 9 8, 5877449092394880⟩, ⟨.privateRow 9 11, 89497520270558400⟩, ⟨.privateRow 10 3, 17174364231024⟩, ⟨.privateRow 10 4, 610644061547520⟩, ⟨.privateRow 10 7, 27020999723477760⟩, ⟨.privateRow 11 2, 34348728462048⟩, ⟨.privateRow 11 6, 1717436423102400⟩, ⟨.privateRow 11 8, 3778360130825280⟩, ⟨.privateRow 11 9, 3663864369285120⟩, ⟨.privateRow 12 9, 1889180065412640⟩, ⟨.privateRow 13 0, 377836013082528⟩, ⟨.hall 11 3, 160294066156224⟩, ⟨.hall 12 3, 62972668847088⟩, ⟨.hall 10 6, 65797888937040⟩, ⟨.hall 5 12, 226697167160640⟩, ⟨.hall 4 15, 15471520404980640⟩, ⟨.hall 3 16, 17055260280938880⟩]
  caps := #[0, 0, 18778275219728640, 1539315971793600, 0, 153123829936000, 154757402995360, 764600113031040, 0, 384340799937248, 0, 0, 16075947502100640, 0, 22162326894400000, 3166046699200000] }

theorem case_37_22_14_checked :
    (Witness.linear .negative case_37_22_14).check 37 22 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_23_1_checked :
    (Witness.rising).check 37 23 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_23_2_checked :
    (Witness.rising).check 37 23 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_23_3_checked :
    (Witness.rising).check 37 23 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_23_4_checked :
    (Witness.rising).check 37 23 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_23_5_checked :
    (Witness.rising).check 37 23 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_23_6_checked :
    (Witness.rising).check 37 23 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_23_7_checked :
    (Witness.rising).check 37 23 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_23_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_37_23_8_checked :
    (Witness.linear .positive case_37_23_8).check 37 23 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_23_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_37_23_9_checked :
    (Witness.linear .positive case_37_23_9).check 37 23 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_23_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_37_23_10_checked :
    (Witness.linear .positive case_37_23_10).check 37 23 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_23_11 : Certificate := {
  objectiveScale := 3974030000
  eta := 292735861019316
  rows := #[⟨.count 2, 64453737067632⟩, ⟨.count 3, 13470221074860⟩, ⟨.count 4, 3077587387944⟩, ⟨.count 5, 674666304264⟩, ⟨.count 6, 166356075024⟩, ⟨.count 7, 40433768235⟩, ⟨.count 8, 12322672224⟩, ⟨.count 9, 4621002084⟩, ⟨.path 7, 3352212864⟩, ⟨.path 8, 2963831574⟩]
  caps := #[0, 204325325804, 0, 5935701222, 285066570, 0, 0, 571584073, 0, 0, 3974030000, 0, 0, 0, 0] }

theorem case_37_23_11_checked :
    (Witness.linear .positive case_37_23_11).check 37 23 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_23_12 : Certificate := {
  objectiveScale := 697680706800000
  eta := 37862205158985086880
  rows := #[⟨.count 2, 7638383914512230880⟩, ⟨.count 3, 1625675233604221800⟩, ⟨.count 4, 344701432374979680⟩, ⟨.count 5, 82428603394016880⟩, ⟨.count 6, 19982691731882880⟩, ⟨.count 7, 5342594664427020⟩, ⟨.count 8, 1665224310990240⟩, ⟨.count 9, 832612155495120⟩, ⟨.path 7, 991289849790240⟩, ⟨.path 8, 215617763436075⟩, ⟨.privateRow 2 21, 778492365387937200⟩, ⟨.privateRow 3 18, 165366025327503000⟩, ⟨.privateRow 3 19, 282394289405428200⟩, ⟨.privateRow 4 15, 22980095491665312⟩, ⟨.privateRow 4 16, 89609883235162290⟩, ⟨.privateRow 4 17, 125585666787180600⟩, ⟨.privateRow 4 18, 168603961487761800⟩, ⟨.privateRow 5 13, 20621027717762472⟩, ⟨.privateRow 5 14, 38966248877171616⟩, ⟨.privateRow 5 15, 56201320495920600⟩, ⟨.privateRow 5 16, 77266408029947136⟩, ⟨.privateRow 5 17, 49373900820860616⟩, ⟨.privateRow 6 10, 1457071272116460⟩, ⟨.privateRow 6 11, 10823958021436560⟩, ⟨.privateRow 6 12, 19026729627425520⟩, ⟨.privateRow 6 13, 25829479312693056⟩, ⟨.privateRow 6 14, 36958728457811160⟩, ⟨.privateRow 7 8, 1403105669445480⟩, ⟨.privateRow 7 9, 5516055530155170⟩, ⟨.privateRow 7 10, 10159850706934500⟩, ⟨.privateRow 7 11, 13865305200536790⟩, ⟨.privateRow 7 12, 4398967554865884⟩, ⟨.privateRow 8 6, 957503978819388⟩, ⟨.privateRow 8 7, 3183970557587820⟩, ⟨.privateRow 8 8, 6036438127339620⟩, ⟨.privateRow 8 9, 1972497844565820⟩, ⟨.privateRow 9 4, 588715665501600⟩, ⟨.privateRow 9 5, 2174042850459480⟩, ⟨.privateRow 9 6, 1058753728592560⟩, ⟨.privateRow 10 2, 346921731456300⟩, ⟨.privateRow 10 3, 711504932877648⟩, ⟨.privateRow 11 0, 96070633326360⟩, ⟨.privateRow 11 1, 173460865728150⟩, ⟨.hall 3 19, 92045273789985516⟩, ⟨.hall 2 20, 277378792373517120⟩, ⟨.assumptionRow 12, 714878536222620⟩]
  caps := #[0, 0, 7333567081020180, 2872845440899434, 1223367948084282, 66586708908720, 175348914732750, 79768642468944, 11523957765495, 0, 1601966235559872, 0, 6261928531777380, 697680706800000, 0] }

theorem case_37_23_12_checked :
    (Witness.linear .conditional case_37_23_12).check 37 23 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_23_13 : Certificate := {
  objectiveScale := 29184618220632000000
  eta := 2097082370964075670375200
  rows := #[⟨.count 2, 387247319590776058814400⟩, ⟨.count 3, 73047861978429341203200⟩, ⟨.count 4, 13153723398213675076800⟩, ⟨.count 5, 2468983679923602441600⟩, ⟨.count 6, 425686841366138352000⟩, ⟨.count 7, 74495197239074211600⟩, ⟨.count 8, 14189561378871278400⟩, ⟨.count 9, 21284342068306917600⟩, ⟨.path 6, 132028234621478395200⟩, ⟨.path 7, 18817862145081199200⟩, ⟨.privateRow 2 21, 41674741769744944660800⟩, ⟨.privateRow 3 18, 8155450402506267260400⟩, ⟨.privateRow 3 19, 14652495818856953857800⟩, ⟨.privateRow 4 15, 996107208796763743680⟩, ⟨.privateRow 4 16, 4177052130905232579000⟩, ⟨.privateRow 4 17, 6413681743249817836800⟩, ⟨.privateRow 4 18, 9418321365225811038000⟩, ⟨.privateRow 5 13, 799581783699396537840⟩, ⟨.privateRow 5 14, 1731694070677450815936⟩, ⟨.privateRow 5 15, 2798890981982359664400⟩, ⟨.privateRow 5 16, 4385993422209112153440⟩, ⟨.privateRow 5 17, 3588540072716546307360⟩, ⟨.privateRow 6 10, 32517744826580013000⟩, ⟨.privateRow 6 11, 385820930825499998400⟩, ⟨.privateRow 6 12, 795797900665030863600⟩, ⟨.privateRow 6 13, 1260033050443769521920⟩, ⟨.privateRow 6 14, 2076405815108163739200⟩, ⟨.privateRow 6 15, 1454430041334306036000⟩, ⟨.privateRow 7 8, 21481419309680129800⟩, ⟨.privateRow 7 9, 176039245856621797650⟩, ⟨.privateRow 7 10, 397307718608395795200⟩, ⟨.privateRow 7 11, 546002497224484400100⟩, ⟨.privateRow 7 12, 1270320482443451198760⟩, ⟨.privateRow 8 6, 7626889241143312140⟩, ⟨.privateRow 8 7, 84546136549108033800⟩, ⟨.privateRow 8 8, 215725675338152404425⟩, ⟨.privateRow 8 9, 377290301663202384600⟩, ⟨.privateRow 8 10, 257481415854101739300⟩, ⟨.privateRow 9 5, 41859206067670271280⟩, ⟨.privateRow 9 6, 130859288271812900800⟩, ⟨.privateRow 9 7, 168501041374096431000⟩, ⟨.privateRow 10 3, 15479521504223212800⟩, ⟨.privateRow 10 4, 88117176162790638864⟩, ⟨.privateRow 10 5, 9932692965209894880⟩, ⟨.privateRow 11 1, 3547390344717819600⟩, ⟨.privateRow 11 2, 30959043008446425600⟩, ⟨.privateRow 12 0, 9755323447974003900⟩, ⟨.hall 4 18, 880499624509959854400⟩, ⟨.hall 3 19, 6017083502710365605520⟩, ⟨.hall 2 20, 15519325988091215347200⟩, ⟨.assumptionRow 13, 17506879649949782400⟩]
  caps := #[0, 395202017064215104800, 0, 0, 88832583978629651160, 0, 2729555870561284800, 17242403491985932260, 10563050318131566255, 0, 24600045457177213296, 31015953013976658000, 0, 245154684335738217600, 29184618220632000000] }

theorem case_37_23_13_checked :
    (Witness.linear .conditional case_37_23_13).check 37 23 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_23_14 : Certificate := {
  objectiveScale := 9914410044000000
  eta := 781056810826862169600
  rows := #[⟨.count 2, 161010538629646305600⟩, ⟨.count 3, 32513504672084436000⟩, ⟨.count 4, 6794115188840179200⟩, ⟨.count 5, 1315527205682289600⟩, ⟨.count 6, 255334394351836800⟩, ⟨.count 7, 38855233923105600⟩, ⟨.path 7, 26334195092805600⟩, ⟨.path 8, 1857857167140975⟩, ⟨.privateRow 3 18, 2783237410896742800⟩, ⟨.privateRow 4 15, 155698473077587440⟩, ⟨.privateRow 4 16, 1714140275125578300⟩, ⟨.privateRow 4 17, 2840595137164184400⟩, ⟨.privateRow 5 13, 197884155622673520⟩, ⟨.privateRow 5 14, 705389018135465664⟩, ⟨.privateRow 5 15, 1278475964762756760⟩, ⟨.privateRow 5 16, 2168122052909292480⟩, ⟨.privateRow 6 11, 121587806834208000⟩, ⟨.privateRow 6 12, 298815251361026400⟩, ⟨.privateRow 6 13, 556925019564513600⟩, ⟨.privateRow 6 14, 1035214446665599200⟩, ⟨.privateRow 6 15, 1196802879806133600⟩, ⟨.privateRow 7 8, 1541874362028000⟩, ⟨.privateRow 7 10, 258010647708785400⟩, ⟨.privateRow 7 11, 201792807130414500⟩, ⟨.privateRow 7 14, 1592370747384417000⟩, ⟨.privateRow 8 6, 1803993003572760⟩, ⟨.privateRow 8 7, 7709371810140000⟩, ⟨.privateRow 8 8, 56548242227376900⟩, ⟨.privateRow 8 10, 567332671508202600⟩, ⟨.privateRow 9 4, 925124617216800⟩, ⟨.privateRow 9 5, 370049846886720⟩, ⟨.privateRow 9 6, 32482153226723200⟩, ⟨.privateRow 9 9, 254871832043228400⟩, ⟨.privateRow 10 8, 110737416680850960⟩, ⟨.privateRow 12 2, 1526455618407720⟩, ⟨.privateRow 12 7, 12211644947261760⟩, ⟨.privateRow 12 9, 5088185394692400⟩, ⟨.hall 9 3, 530675879326560⟩, ⟨.hall 10 3, 1310054090814000⟩, ⟨.hall 7 7, 6671571758775⟩, ⟨.hall 11 7, 57820288576050⟩, ⟨.hall 3 16, 2842610075765460⟩, ⟨.hall 4 16, 13341270795652800⟩, ⟨.hall 2 19, 763663939380547920⟩]
  caps := #[0, 0, 5662576493135100, 7822643331943440, 3635193056019525, 3224743154879400, 0, 3267249998641200, 1996625859723495, 2445167693128160, 4403159461855440, 0, 0, 347004351540000000, 79315280352000000] }

theorem case_37_23_14_checked :
    (Witness.linear .negative case_37_23_14).check 37 23 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_24_1_checked :
    (Witness.rising).check 37 24 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_24_2_checked :
    (Witness.rising).check 37 24 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_24_3_checked :
    (Witness.rising).check 37 24 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_24_4_checked :
    (Witness.rising).check 37 24 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_24_5_checked :
    (Witness.rising).check 37 24 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_24_6_checked :
    (Witness.rising).check 37 24 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_24_7_checked :
    (Witness.rising).check 37 24 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_24_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_37_24_8_checked :
    (Witness.linear .positive case_37_24_8).check 37 24 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_24_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_37_24_9_checked :
    (Witness.linear .positive case_37_24_9).check 37 24 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_24_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_37_24_10_checked :
    (Witness.linear .positive case_37_24_10).check 37 24 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_24_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_37_24_11_checked :
    (Witness.linear .positive case_37_24_11).check 37 24 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_24_12 : Certificate := {
  objectiveScale := 197048098632000000
  eta := 23345231120084994120000
  rows := #[⟨.count 2, 4202141601615298941600⟩, ⟨.count 3, 786365679834441907200⟩, ⟨.count 4, 159953928057233069760⟩, ⟨.count 5, 32765236659768412800⟩, ⟨.count 6, 7074312460631816400⟩, ⟨.count 7, 1489328939080382400⟩, ⟨.count 8, 496442979693460800⟩, ⟨.path 6, 169750793870658000⟩, ⟨.path 7, 580031690402964800⟩, ⟨.privateRow 2 22, 368608912422394644000⟩, ⟨.privateRow 3 18, 9494471986637437800⟩, ⟨.privateRow 3 19, 104004804245780037600⟩, ⟨.privateRow 3 20, 135901265691084894000⟩, ⟨.privateRow 4 16, 26763241035274471728⟩, ⟨.privateRow 4 17, 49873902847454305620⟩, ⟨.privateRow 4 18, 60690154267525582800⟩, ⟨.privateRow 4 19, 70482492041979097080⟩, ⟨.privateRow 5 13, 4113384688888675200⟩, ⟨.privateRow 5 14, 15489020966435976960⟩, ⟨.privateRow 5 15, 22459080401332166592⟩, ⟨.privateRow 5 16, 27304363883140344000⟩, ⟨.privateRow 5 17, 27205075287201651840⟩, ⟨.privateRow 6 10, 324066945077675800⟩, ⟨.privateRow 6 11, 3653510053681563075⟩, ⟨.privateRow 6 12, 7907627462260125600⟩, ⟨.privateRow 6 13, 11449216219180439700⟩, ⟨.privateRow 6 14, 13143327887384374680⟩, ⟨.privateRow 7 8, 457436745574688880⟩, ⟨.privateRow 7 9, 2440844650159515600⟩, ⟨.privateRow 7 10, 4614260195186541900⟩, ⟨.privateRow 7 11, 5486201500081816800⟩, ⟨.privateRow 8 6, 417463414742228400⟩, ⟨.privateRow 8 7, 1718933817188608020⟩, ⟨.privateRow 8 8, 2151252912004996800⟩, ⟨.privateRow 9 4, 364058185108537920⟩, ⟨.privateRow 9 5, 920676071431509120⟩, ⟨.privateRow 10 2, 326506728952237680⟩, ⟨.privateRow 11 0, 53190319252870800⟩, ⟨.hall 3 20, 15850715137355498400⟩, ⟨.hall 2 21, 98295709979305238400⟩, ⟨.assumptionRow 12, 218096776527870240⟩]
  caps := #[0, 197906234755429200, 0, 4756710198065826000, 27702032878520000, 0, 243319333013391635, 68333246913414560, 132704415557635740, 218096776527870240, 0, 2531559120332161920, 1949432308424129760, 197048098632000000] }

theorem case_37_24_12_checked :
    (Witness.linear .conditional case_37_24_12).check 37 24 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_24_13 : Certificate := {
  objectiveScale := 644804622000000
  eta := 103894600983500527200
  rows := #[⟨.count 2, 16904763077122720800⟩, ⟨.count 3, 2768183382992227200⟩, ⟨.count 4, 463963130388838080⟩, ⟨.count 5, 70395899802228000⟩, ⟨.count 6, 9747124588000800⟩, ⟨.count 7, 2436781147000200⟩, ⟨.count 8, 1083013843111200⟩, ⟨.path 5, 4185122091900750⟩, ⟨.path 6, 5403050169917400⟩, ⟨.privateRow 2 22, 1590405828608797200⟩, ⟨.privateRow 3 18, 36145587013836300⟩, ⟨.privateRow 3 19, 407213205009811200⟩, ⟨.privateRow 3 20, 573455829927380400⟩, ⟨.privateRow 4 16, 90940672406047464⟩, ⟨.privateRow 4 17, 189947090408665590⟩, ⟨.privateRow 4 18, 255699568358554320⟩, ⟨.privateRow 4 19, 331645914106727220⟩, ⟨.privateRow 5 13, 10675422167810400⟩, ⟨.privateRow 5 14, 50360143704670800⟩, ⟨.privateRow 5 15, 83348745365837952⟩, ⟨.privateRow 5 16, 72074571259050360⟩, ⟨.privateRow 5 17, 244327923005886720⟩, ⟨.privateRow 6 10, 165460448253100⟩, ⟨.privateRow 6 11, 8833331657875725⟩, ⟨.privateRow 6 12, 24561206799129000⟩, ⟨.privateRow 6 13, 41267339980216350⟩, ⟨.privateRow 6 14, 56045966381004600⟩, ⟨.privateRow 6 15, 57196668589310250⟩, ⟨.privateRow 7 8, 92829757980960⟩, ⟨.privateRow 7 9, 5466641303323200⟩, ⟨.privateRow 7 10, 13416800958185625⟩, ⟨.privateRow 7 11, 23058248812770600⟩, ⟨.privateRow 7 12, 30208350409637400⟩, ⟨.privateRow 8 7, 3249041529333600⟩, ⟨.privateRow 8 8, 8709236321685900⟩, ⟨.privateRow 8 9, 14654531064598425⟩, ⟨.privateRow 9 5, 2008498399951680⟩, ⟨.privateRow 9 6, 6736346104151664⟩, ⟨.privateRow 9 7, 529473434409920⟩, ⟨.privateRow 10 3, 1421455669083450⟩, ⟨.privateRow 10 4, 1550678911727400⟩, ⟨.privateRow 11 1, 874741950205200⟩, ⟨.hall 3 20, 108610816837723200⟩, ⟨.hall 2 21, 452429032959703800⟩, ⟨.assumptionRow 13, 462066992125200⟩]
  caps := #[0, 0, 7828266117672000, 269782561748700, 0, 0, 709339877170925, 0, 1181472822204675, 462066992125200, 4311042069092850, 0, 29736712674622800, 5985979227874800] }

theorem case_37_24_13_checked :
    (Witness.linear .conditional case_37_24_13).check 37 24 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_24_14 : Certificate := {
  objectiveScale := 6835752000000
  eta := 50391553240828800
  rows := #[⟨.count 3, 321477213657600⟩, ⟨.count 9, 1109096387118720⟩, ⟨.count 10, 6831390790224000⟩, ⟨.count 11, 2946874458528000⟩, ⟨.count 12, 884062337558400⟩, ⟨.path 3, 307593465379200⟩, ⟨.privateRow 2 11, 153483044715000⟩, ⟨.privateRow 2 12, 154041164877600⟩, ⟨.privateRow 2 17, 994570129753200⟩, ⟨.privateRow 2 18, 4376108570914080⟩, ⟨.privateRow 2 19, 7090916665833000⟩, ⟨.privateRow 2 20, 14316898411015200⟩, ⟨.privateRow 2 21, 23906519044808400⟩, ⟨.privateRow 2 22, 33447025104292800⟩, ⟨.privateRow 3 11, 26789767804800⟩, ⟨.privateRow 3 12, 133948839024000⟩, ⟨.privateRow 3 13, 367615147099200⟩, ⟨.privateRow 3 14, 128925757560600⟩, ⟨.privateRow 3 15, 1040973834700800⟩, ⟨.privateRow 3 16, 1018011176582400⟩, ⟨.privateRow 3 17, 3563039118038400⟩, ⟨.privateRow 3 18, 4393521919987200⟩, ⟨.privateRow 3 19, 9586271912817600⟩, ⟨.privateRow 3 20, 9764870364849600⟩, ⟨.privateRow 4 6, 8036930341440⟩, ⟨.privateRow 4 7, 24110791024320⟩, ⟨.privateRow 4 10, 210056133924000⟩, ⟨.privateRow 4 12, 133948839024000⟩, ⟨.privateRow 4 13, 308919509999100⟩, ⟨.privateRow 4 14, 649843224750720⟩, ⟨.privateRow 4 15, 1040782479216480⟩, ⟨.privateRow 4 16, 2247125723466624⟩, ⟨.privateRow 4 17, 3305187602917200⟩, ⟨.privateRow 4 18, 4282344383597280⟩, ⟨.privateRow 4 19, 5159709279204480⟩, ⟨.privateRow 5 2, 10715907121920⟩, ⟨.privateRow 5 6, 46690738174080⟩, ⟨.privateRow 5 7, 23355182188800⟩, ⟨.privateRow 5 9, 35882052635520⟩, ⟨.privateRow 5 11, 311158191984640⟩, ⟨.privateRow 5 12, 134172087089040⟩, ⟨.privateRow 5 13, 555696326465280⟩, ⟨.privateRow 5 14, 933772240040640⟩, ⟨.privateRow 5 15, 1377351262070784⟩, ⟨.privateRow 5 16, 1820364722336160⟩, ⟨.privateRow 5 17, 2411674430605440⟩, ⟨.privateRow 6 1, 20526419313400⟩, ⟨.privateRow 6 3, 11092638231675⟩, ⟨.privateRow 6 7, 66509319376500⟩, ⟨.privateRow 6 9, 122674811739480⟩, ⟨.privateRow 6 10, 90167412935600⟩, ⟨.privateRow 6 11, 272502169389450⟩, ⟨.privateRow 6 12, 443944723622400⟩, ⟨.privateRow 6 13, 659325952084800⟩, ⟨.privateRow 6 14, 882946097233200⟩, ⟨.privateRow 6 15, 456263232925500⟩, ⟨.privateRow 7 0, 17700382299600⟩, ⟨.privateRow 7 6, 164485985063400⟩, ⟨.privateRow 7 8, 33869920724640⟩, ⟨.privateRow 7 9, 149150969167200⟩, ⟨.privateRow 7 10, 251512864703100⟩, ⟨.privateRow 7 11, 372323099491200⟩, ⟨.privateRow 7 12, 111624032520000⟩, ⟨.privateRow 8 0, 19238730310800⟩, ⟨.privateRow 8 3, 46802362206600⟩, ⟨.privateRow 8 4, 92476217710800⟩, ⟨.privateRow 8 5, 47440213821000⟩, ⟨.privateRow 8 7, 91531706666400⟩, ⟨.privateRow 8 8, 55191882746000⟩, ⟨.privateRow 9 0, 92424698926560⟩, ⟨.hall 3 20, 1171095564038400⟩, ⟨.hall 2 21, 7414068239978400⟩]
  caps := #[0, 520105710579840, 1319933815200, 18274603947600, 1772335802160, 4768116759616, 458568458425, 3045022077240, 393967173600, 6320062869120, 11196961776000, 0, 168643470441600, 300773088000000] }

theorem case_37_24_14_checked :
    (Witness.linear .negative case_37_24_14).check 37 24 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_24_15 : Certificate := {
  objectiveScale := 81829440000
  eta := 27232162129972800
  rows := #[⟨.count 2, 3940253854336800⟩, ⟨.count 3, 539454855139200⟩, ⟨.count 4, 63909938252160⟩, ⟨.count 5, 5344917177600⟩, ⟨.path 4, 481042545984⟩, ⟨.path 5, 5289725941500⟩, ⟨.privateRow 6 9, 9544494960⟩, ⟨.privateRow 6 11, 521964568125⟩, ⟨.privateRow 8 8, 108701192600⟩, ⟨.hall 11 4, 2202575760⟩, ⟨.hall 9 6, 3604214880⟩, ⟨.hall 10 6, 2955837600⟩, ⟨.hall 8 7, 353747016⟩, ⟨.hall 11 8, 1223653200⟩, ⟨.hall 6 9, 3260115000⟩, ⟨.hall 7 9, 3763224360⟩, ⟨.hall 8 9, 3744378792⟩, ⟨.hall 5 13, 13443859000⟩, ⟨.hall 4 14, 14593030452⟩]
  caps := #[0, 0, 0, 0, 102599440944, 0, 0, 0, 0, 19679980320, 305837532000, 0, 2356824254400, 9001238400000] }

theorem case_37_24_15_checked :
    (Witness.linear .negative case_37_24_15).check 37 24 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_25_1_checked :
    (Witness.rising).check 37 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_25_2_checked :
    (Witness.rising).check 37 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_25_3_checked :
    (Witness.rising).check 37 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_25_4_checked :
    (Witness.rising).check 37 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_25_5_checked :
    (Witness.rising).check 37 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_25_6_checked :
    (Witness.rising).check 37 25 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_25_7_checked :
    (Witness.rising).check 37 25 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_25_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_37_25_8_checked :
    (Witness.linear .positive case_37_25_8).check 37 25 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_25_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_37_25_9_checked :
    (Witness.linear .positive case_37_25_9).check 37 25 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_25_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_37_25_10_checked :
    (Witness.linear .positive case_37_25_10).check 37 25 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_25_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_37_25_11_checked :
    (Witness.linear .positive case_37_25_11).check 37 25 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_25_12 : Certificate := {
  objectiveScale := 967
  eta := 12978888
  rows := #[⟨.assumptionRow 12, 2162⟩]
  caps := #[0, 0, 3900104, 1196195, 376189, 125829, 44388, 16730, 6942, 267140, 143870, 46353, 9442] }

theorem case_37_25_12_checked :
    (Witness.linear .conditional case_37_25_12).check 37 25 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_25_13 : Certificate := {
  objectiveScale := 62280048600000
  eta := 17553337611520510800
  rows := #[⟨.count 2, 2438355828041733600⟩, ⟨.count 3, 341746395976505520⟩, ⟨.count 4, 43934339243995200⟩, ⟨.count 5, 4968764557356600⟩, ⟨.count 6, 448309584122400⟩, ⟨.count 7, 261513924071400⟩, ⟨.path 5, 3268596104373600⟩, ⟨.privateRow 2 22, 142002060770770200⟩, ⟨.privateRow 2 23, 276158703819398400⟩, ⟨.privateRow 3 19, 48720044054501820⟩, ⟨.privateRow 3 20, 92052901273132800⟩, ⟨.privateRow 3 21, 93674287602375480⟩, ⟨.privateRow 4 15, 463253236926480⟩, ⟨.privateRow 4 16, 9536541097803720⟩, ⟨.privateRow 4 17, 28306267141488336⟩, ⟨.privateRow 4 18, 36873463294067400⟩, ⟨.privateRow 4 19, 42504729792404880⟩, ⟨.privateRow 4 20, 41789925066609720⟩, ⟨.privateRow 5 13, 1536394303919475⟩, ⟨.privateRow 5 14, 6911439421887000⟩, ⟨.privateRow 5 15, 13093130465174760⟩, ⟨.privateRow 5 16, 17082089520343848⟩, ⟨.privateRow 5 17, 19535090128133580⟩, ⟨.privateRow 5 18, 7392126920418240⟩, ⟨.privateRow 6 9, 23773993097400⟩, ⟨.privateRow 6 11, 1378136869709600⟩, ⟨.privateRow 6 12, 4137523870129650⟩, ⟨.privateRow 6 13, 6847395195583800⟩, ⟨.privateRow 6 14, 9246385172524500⟩, ⟨.privateRow 6 15, 3646251284195520⟩, ⟨.privateRow 7 9, 1087150741496820⟩, ⟨.privateRow 7 10, 2735518666080200⟩, ⟨.privateRow 7 11, 4445736709213800⟩, ⟨.privateRow 7 12, 1088751847154400⟩, ⟨.privateRow 8 7, 903411737701200⟩, ⟨.privateRow 8 8, 2249019747014040⟩, ⟨.privateRow 8 9, 151096933907920⟩, ⟨.privateRow 9 5, 906581603447520⟩, ⟨.privateRow 9 6, 209211139257120⟩, ⟨.privateRow 10 3, 337956455723040⟩, ⟨.privateRow 11 1, 112077396030600⟩, ⟨.hall 2 22, 50892883658416800⟩, ⟨.assumptionRow 13, 49998778902072⟩]
  caps := #[0, 1868576125977792, 2227866259554936, 0, 0, 257201003471412, 19184813573394, 116755246244208, 538704780667144, 49998778902072, 1420707556643760, 0, 3448217812175136] }

theorem case_37_25_13_checked :
    (Witness.linear .conditional case_37_25_13).check 37 25 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_25_14 : Certificate := {
  objectiveScale := 133457247000000
  eta := 41579144843808171600
  rows := #[⟨.count 2, 5793056446029652800⟩, ⟨.count 3, 792701006645227680⟩, ⟨.count 4, 95818701779760960⟩, ⟨.count 5, 8629959494356200⟩, ⟨.path 5, 7989901588468800⟩, ⟨.privateRow 2 22, 447188810162094000⟩, ⟨.privateRow 2 23, 790818106391913600⟩, ⟨.privateRow 3 19, 122623878997079460⟩, ⟨.privateRow 3 20, 253668506349258000⟩, ⟨.privateRow 3 21, 269411644578356280⟩, ⟨.privateRow 4 15, 777069945812160⟩, ⟨.privateRow 4 16, 21513878820273840⟩, ⟨.privateRow 4 17, 69960204967580928⟩, ⟨.privateRow 4 18, 99401442539539140⟩, ⟨.privateRow 4 19, 124166811149100720⟩, ⟨.privateRow 4 20, 143728052669641440⟩, ⟨.privateRow 5 12, 92982728558720⟩, ⟨.privateRow 5 13, 3079326455940735⟩, ⟨.privateRow 5 14, 15152863943337120⟩, ⟨.privateRow 5 15, 31730356120663200⟩, ⟨.privateRow 5 16, 45022237168132224⟩, ⟨.privateRow 5 17, 56892354181733070⟩, ⟨.privateRow 5 18, 51849494012556240⟩, ⟨.privateRow 6 8, 15566305004250⟩, ⟨.privateRow 6 10, 212947052458140⟩, ⟨.privateRow 6 11, 2598535182042800⟩, ⟨.privateRow 6 12, 8774726130895725⟩, ⟨.privateRow 6 13, 16027067632375800⟩, ⟨.privateRow 6 14, 23679463172465100⟩, ⟨.privateRow 6 15, 30283312407468120⟩, ⟨.privateRow 6 16, 308212839084150⟩, ⟨.privateRow 7 8, 193588229507400⟩, ⟨.privateRow 7 9, 1965090343736520⟩, ⟨.privateRow 7 10, 5566510669519800⟩, ⟨.privateRow 7 11, 9946868897715750⟩, ⟨.privateRow 7 12, 14575398502836600⟩, ⟨.privateRow 8 6, 174342616047600⟩, ⟨.privateRow 8 7, 1659424718198520⟩, ⟨.privateRow 8 8, 4372512810473808⟩, ⟨.privateRow 8 9, 6131048664340600⟩, ⟨.privateRow 9 4, 209211139257120⟩, ⟨.privateRow 9 5, 1743426160476000⟩, ⟨.privateRow 9 6, 2567591254519200⟩, ⟨.privateRow 10 2, 336232188091800⟩, ⟨.privateRow 10 3, 1206987341868000⟩, ⟨.privateRow 11 0, 523027848142800⟩, ⟨.hall 3 21, 7488807825681000⟩, ⟨.hall 2 22, 157999890821572800⟩, ⟨.assumptionRow 14, 45844343774460⟩]
  caps := #[0, 10196133015388320, 1206598130614800, 706998919667040, 0, 134604451417436, 35594950776385, 147299166899820, 20808301661056, 0, 2483568189471600, 0, 24779225030660100] }

theorem case_37_25_14_checked :
    (Witness.linear .conditional case_37_25_14).check 37 25 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_25_15 : Certificate := {
  objectiveScale := 657926895600000
  eta := 262974591414734799600
  rows := #[⟨.count 2, 35475634010773756800⟩, ⟨.count 3, 4486816810772215920⟩, ⟨.count 4, 484353674685840960⟩, ⟨.count 5, 35453816277679800⟩, ⟨.path 4, 65773420413386400⟩, ⟨.path 5, 35529056579016000⟩, ⟨.privateRow 6 9, 70836795759600⟩, ⟨.privateRow 6 10, 623363802684480⟩, ⟨.privateRow 6 11, 2640638330816200⟩, ⟨.privateRow 6 12, 7938148424810175⟩, ⟨.privateRow 6 15, 161996668222629240⟩, ⟨.privateRow 7 7, 32466864723150⟩, ⟨.privateRow 7 8, 425020774557600⟩, ⟨.privateRow 7 9, 1792170932717880⟩, ⟨.privateRow 7 10, 5237987508668200⟩, ⟨.privateRow 8 6, 136360831837230⟩, ⟨.privateRow 8 7, 793372112507520⟩, ⟨.hall 10 5, 32693905735200⟩, ⟨.hall 7 6, 58675410725910⟩, ⟨.hall 9 6, 30241862805060⟩, ⟨.hall 8 7, 6955468180920⟩, ⟨.hall 6 8, 26933296527500⟩, ⟨.hall 8 9, 22033128237624⟩, ⟨.hall 5 10, 14571393745500⟩, ⟨.hall 4 14, 72875881782704⟩, ⟨.hall 3 17, 875766490733160⟩, ⟨.hall 2 20, 32178384438969600⟩]
  caps := #[0, 31725974576696400, 0, 165003898625280, 2842396843178880, 1125986105103600, 0, 1105861801871580, 0, 0, 0, 0, 282250638212400000] }

theorem case_37_25_15_checked :
    (Witness.linear .negative case_37_25_15).check 37 25 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_25_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1430, 1430, 1001, 572] }

theorem case_37_25_16_checked :
    (Witness.linear .negative case_37_25_16).check 37 25 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_26_1_checked :
    (Witness.rising).check 37 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_26_2_checked :
    (Witness.rising).check 37 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_26_3_checked :
    (Witness.rising).check 37 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_26_4_checked :
    (Witness.rising).check 37 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_26_5_checked :
    (Witness.rising).check 37 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_26_6_checked :
    (Witness.rising).check 37 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_26_7_checked :
    (Witness.rising).check 37 26 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_26_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_37_26_8_checked :
    (Witness.linear .positive case_37_26_8).check 37 26 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_26_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_37_26_9_checked :
    (Witness.linear .positive case_37_26_9).check 37 26 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_26_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_37_26_10_checked :
    (Witness.linear .positive case_37_26_10).check 37 26 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_26_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_37_26_11_checked :
    (Witness.linear .positive case_37_26_11).check 37 26 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_26_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_37_26_12_checked :
    (Witness.linear .positive case_37_26_12).check 37 26 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_26_13 : Certificate := {
  objectiveScale := 708
  eta := 10265586
  rows := #[⟨.assumptionRow 13, 1061⟩]
  caps := #[0, 0, 3273894, 1064232, 353353, 120417, 42390, 15548, 1233180, 892364, 425240, 152310] }

theorem case_37_26_13_checked :
    (Witness.linear .conditional case_37_26_13).check 37 26 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_26_14 : Certificate := {
  objectiveScale := 982476000000
  eta := 684545248513526400
  rows := #[⟨.count 2, 76750572866647680⟩, ⟨.count 3, 7568324505181440⟩, ⟨.count 4, 533663907416640⟩, ⟨.count 5, 5775583413600⟩, ⟨.path 4, 510721759548000⟩, ⟨.privateRow 2 23, 7519809604507200⟩, ⟨.privateRow 2 24, 8950999174397280⟩, ⟨.privateRow 3 19, 763301103941376⟩, ⟨.privateRow 3 20, 1776184419129120⟩, ⟨.privateRow 3 21, 3520025571142080⟩, ⟨.privateRow 3 22, 3007923841802880⟩, ⟨.privateRow 4 15, 15413588235045⟩, ⟨.privateRow 4 16, 254125670198400⟩, ⟨.privateRow 4 17, 429895925418960⟩, ⟨.privateRow 4 18, 1041453201140352⟩, ⟨.privateRow 4 19, 1333149041444220⟩, ⟨.privateRow 4 20, 1462859018941320⟩, ⟨.privateRow 4 21, 588243170675160⟩, ⟨.privateRow 5 12, 6930700096320⟩, ⟨.privateRow 5 13, 56472371155200⟩, ⟨.privateRow 5 14, 123019926709680⟩, ⟨.privateRow 5 15, 294884787431520⟩, ⟨.privateRow 5 16, 498240329146560⟩, ⟨.privateRow 5 17, 639472595553792⟩, ⟨.privateRow 5 18, 473020281573840⟩, ⟨.privateRow 6 9, 1443895853400⟩, ⟨.privateRow 6 10, 12251237544000⟩, ⟨.privateRow 6 11, 33209604628200⟩, ⟨.privateRow 6 12, 98291873279600⟩, ⟨.privateRow 6 13, 185299967853000⟩, ⟨.privateRow 6 14, 285478837300800⟩, ⟨.privateRow 6 15, 204231046819800⟩, ⟨.privateRow 7 6, 495050006880⟩, ⟨.privateRow 7 7, 3021074400960⟩, ⟨.privateRow 7 8, 9625972356000⟩, ⟨.privateRow 7 9, 34443479266560⟩, ⟨.privateRow 7 10, 83976982833744⟩, ⟨.privateRow 7 11, 144517931638080⟩, ⟨.privateRow 7 12, 32343267116160⟩, ⟨.privateRow 8 3, 252681774345⟩, ⟨.privateRow 8 4, 1212872516856⟩, ⟨.privateRow 8 5, 3609739633500⟩, ⟨.privateRow 8 6, 14150179363320⟩, ⟨.privateRow 8 7, 43124356154880⟩, ⟨.privateRow 8 8, 49985049179520⟩, ⟨.privateRow 9 0, 299474695520⟩, ⟨.privateRow 9 1, 951272562240⟩, ⟨.privateRow 9 2, 2358363227220⟩, ⟨.privateRow 9 3, 8624871230976⟩, ⟨.privateRow 9 4, 26182644808320⟩, ⟨.privateRow 10 0, 12842179590240⟩, ⟨.hall 2 23, 1063284906443760⟩, ⟨.assumptionRow 14, 487069324560⟩]
  caps := #[0, 155330509072320, 8488822255200, 7440152468112, 12527153770131, 0, 5843645844400, 20627083620, 18489217995027, 0, 0, 723578896404000] }

theorem case_37_26_14_checked :
    (Witness.linear .conditional case_37_26_14).check 37 26 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_26_15 : Certificate := {
  objectiveScale := 566
  eta := 1457376
  rows := #[⟨.assumptionRow 15, 377⟩]
  caps := #[0, 0, 650964, 247436, 102466, 44005, 16566, 8465, 1755624, 1669876, 1099644, 584038] }

theorem case_37_26_15_checked :
    (Witness.linear .conditional case_37_26_15).check 37 26 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_26_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 4862, 4862, 3432, 2002] }

theorem case_37_26_16_checked :
    (Witness.linear .negative case_37_26_16).check 37 26 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_27_1_checked :
    (Witness.rising).check 37 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_27_2_checked :
    (Witness.rising).check 37 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_27_3_checked :
    (Witness.rising).check 37 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_27_4_checked :
    (Witness.rising).check 37 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_27_5_checked :
    (Witness.rising).check 37 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_27_6_checked :
    (Witness.rising).check 37 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_27_7_checked :
    (Witness.rising).check 37 27 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_27_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_37_27_8_checked :
    (Witness.linear .positive case_37_27_8).check 37 27 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_27_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_37_27_9_checked :
    (Witness.linear .positive case_37_27_9).check 37 27 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_27_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_37_27_10_checked :
    (Witness.linear .positive case_37_27_10).check 37 27 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_27_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_37_27_11_checked :
    (Witness.linear .positive case_37_27_11).check 37 27 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_27_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_37_27_12_checked :
    (Witness.linear .positive case_37_27_12).check 37 27 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_27_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_37_27_13_checked :
    (Witness.linear .positive case_37_27_13).check 37 27 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_27_14 : Certificate := {
  objectiveScale := 518
  eta := 13339900
  rows := #[⟨.assumptionRow 14, 647⟩]
  caps := #[0, 0, 4253910, 1370200, 446810, 147862, 49775, 19380, 2015520, 1614252, 872644] }

theorem case_37_27_14_checked :
    (Witness.linear .conditional case_37_27_14).check 37 27 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_27_15 : Certificate := {
  objectiveScale := 985
  eta := 13304370
  rows := #[⟨.assumptionRow 15, 853⟩]
  caps := #[0, 0, 4565928, 1527484, 595140, 226408, 82885, 32395, 4978722, 4534512, 2846956] }

theorem case_37_27_15_checked :
    (Witness.linear .conditional case_37_27_15).check 37 27 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_27_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 16796, 16796, 11934, 7072] }

theorem case_37_27_16_checked :
    (Witness.linear .negative case_37_27_16).check 37 27 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_27_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 4862, 4862] }

theorem case_37_27_17_checked :
    (Witness.linear .negative case_37_27_17).check 37 27 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_28_1_checked :
    (Witness.rising).check 37 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_28_2_checked :
    (Witness.rising).check 37 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_28_3_checked :
    (Witness.rising).check 37 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_28_4_checked :
    (Witness.rising).check 37 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_28_5_checked :
    (Witness.rising).check 37 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_28_6_checked :
    (Witness.rising).check 37 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_28_7_checked :
    (Witness.rising).check 37 28 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_28_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_37_28_8_checked :
    (Witness.linear .positive case_37_28_8).check 37 28 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_28_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_37_28_9_checked :
    (Witness.linear .positive case_37_28_9).check 37 28 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_28_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_37_28_10_checked :
    (Witness.linear .positive case_37_28_10).check 37 28 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_28_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_37_28_11_checked :
    (Witness.linear .positive case_37_28_11).check 37 28 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_28_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_37_28_12_checked :
    (Witness.linear .positive case_37_28_12).check 37 28 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_28_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_37_28_13_checked :
    (Witness.linear .positive case_37_28_13).check 37 28 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_28_14 : Certificate := {
  objectiveScale := 994
  eta := 39657940
  rows := #[⟨.assumptionRow 14, 1397⟩]
  caps := #[0, 0, 12079554, 3728712, 1176344, 403403, 141559, 51180, 6038808, 4581432] }

theorem case_37_28_14_checked :
    (Witness.linear .conditional case_37_28_14).check 37 28 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_28_15 : Certificate := {
  objectiveScale := 829
  eta := 9286896
  rows := #[⟨.assumptionRow 15, 696⟩]
  caps := #[0, 0, 3333360, 1150016, 421148, 168623, 63954, 14276600, 13188090, 8488440] }

theorem case_37_28_15_checked :
    (Witness.linear .conditional case_37_28_15).check 37 28 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_28_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 58786, 58786, 41990, 25194] }

theorem case_37_28_16_checked :
    (Witness.linear .negative case_37_28_16).check 37 28 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_28_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 16796, 16796] }

theorem case_37_28_17_checked :
    (Witness.linear .negative case_37_28_17).check 37 28 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_28_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_37_28_18_checked :
    (Witness.linear .negative case_37_28_18).check 37 28 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_29_1_checked :
    (Witness.rising).check 37 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_29_2_checked :
    (Witness.rising).check 37 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_29_3_checked :
    (Witness.rising).check 37 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_29_4_checked :
    (Witness.rising).check 37 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_29_5_checked :
    (Witness.rising).check 37 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_29_6_checked :
    (Witness.rising).check 37 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_29_7_checked :
    (Witness.rising).check 37 29 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_29_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0] }

theorem case_37_29_8_checked :
    (Witness.linear .positive case_37_29_8).check 37 29 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_29_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1] }

theorem case_37_29_9_checked :
    (Witness.linear .positive case_37_29_9).check 37 29 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_29_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_37_29_10_checked :
    (Witness.linear .positive case_37_29_10).check 37 29 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_29_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_37_29_11_checked :
    (Witness.linear .positive case_37_29_11).check 37 29 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_29_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_37_29_12_checked :
    (Witness.linear .positive case_37_29_12).check 37 29 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_29_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_37_29_13_checked :
    (Witness.linear .positive case_37_29_13).check 37 29 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_29_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_37_29_14_checked :
    (Witness.linear .positive case_37_29_14).check 37 29 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_29_15 : Certificate := {
  objectiveScale := 1
  eta := 28424
  rows := #[⟨.assumptionRow 15, 1⟩]
  caps := #[0, 0, 9690, 3264, 1092, 364, 143, 28424, 25194] }

theorem case_37_29_15_checked :
    (Witness.linear .conditional case_37_29_15).check 37 29 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_29_16 : Certificate := {
  objectiveScale := 9
  eta := 20349
  rows := #[⟨.assumptionRow 16, 5⟩]
  caps := #[0, 0, 7752, 3740, 1400, 728, 237728, 454784, 377910] }

theorem case_37_29_16_checked :
    (Witness.linear .conditional case_37_29_16).check 37 29 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_29_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 58786, 58786] }

theorem case_37_29_17_checked :
    (Witness.linear .negative case_37_29_17).check 37 29 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_29_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_37_29_18_checked :
    (Witness.linear .negative case_37_29_18).check 37 29 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_30_1_checked :
    (Witness.rising).check 37 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_30_2_checked :
    (Witness.rising).check 37 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_30_3_checked :
    (Witness.rising).check 37 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_30_4_checked :
    (Witness.rising).check 37 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_30_5_checked :
    (Witness.rising).check 37 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_30_6_checked :
    (Witness.rising).check 37 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_30_7_checked :
    (Witness.rising).check 37 30 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_30_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1] }

theorem case_37_30_8_checked :
    (Witness.linear .positive case_37_30_8).check 37 30 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_30_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_37_30_9_checked :
    (Witness.linear .positive case_37_30_9).check 37 30 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_30_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_37_30_10_checked :
    (Witness.linear .positive case_37_30_10).check 37 30 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_37_30_11_checked :
    (Witness.linear .positive case_37_30_11).check 37 30 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_30_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_37_30_12_checked :
    (Witness.linear .positive case_37_30_12).check 37 30 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_30_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42] }

theorem case_37_30_13_checked :
    (Witness.linear .positive case_37_30_13).check 37 30 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_30_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_37_30_14_checked :
    (Witness.linear .positive case_37_30_14).check 37 30 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_30_15 : Certificate := {
  objectiveScale := 13
  eta := 9152528
  rows := #[⟨.assumptionRow 15, 33⟩]
  caps := #[0, 0, 2615008, 764218, 226746, 68510, 21164, 6721] }

theorem case_37_30_15_checked :
    (Witness.linear .conditional case_37_30_15).check 37 30 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_30_16 : Certificate := {
  objectiveScale := 997
  eta := 4822713
  rows := #[⟨.assumptionRow 16, 623⟩]
  caps := #[0, 0, 1930248, 736032, 331184, 148580, 125995840, 122251624] }

theorem case_37_30_16_checked :
    (Witness.linear .conditional case_37_30_16).check 37 30 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_30_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 208012, 208012] }

theorem case_37_30_17_checked :
    (Witness.linear .negative case_37_30_17).check 37 30 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_30_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_37_30_18_checked :
    (Witness.linear .negative case_37_30_18).check 37 30 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_30_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_37_30_19_checked :
    (Witness.linear .negative case_37_30_19).check 37 30 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_31_1_checked :
    (Witness.rising).check 37 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_31_2_checked :
    (Witness.rising).check 37 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_31_3_checked :
    (Witness.rising).check 37 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_31_4_checked :
    (Witness.rising).check 37 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_31_5_checked :
    (Witness.rising).check 37 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_31_6_checked :
    (Witness.rising).check 37 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_31_7_checked :
    (Witness.rising).check 37 31 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_31_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1] }

theorem case_37_31_8_checked :
    (Witness.linear .positive case_37_31_8).check 37 31 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_31_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_37_31_9_checked :
    (Witness.linear .positive case_37_31_9).check 37 31 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_31_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_37_31_10_checked :
    (Witness.linear .positive case_37_31_10).check 37 31 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_37_31_11_checked :
    (Witness.linear .positive case_37_31_11).check 37 31 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_37_31_12_checked :
    (Witness.linear .positive case_37_31_12).check 37 31 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_31_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_37_31_13_checked :
    (Witness.linear .positive case_37_31_13).check 37 31 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_31_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429] }

theorem case_37_31_14_checked :
    (Witness.linear .positive case_37_31_14).check 37 31 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_31_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430] }

theorem case_37_31_15_checked :
    (Witness.linear .positive case_37_31_15).check 37 31 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_31_16 : Certificate := {
  objectiveScale := 999
  eta := 23396505
  rows := #[⟨.assumptionRow 16, 799⟩]
  caps := #[0, 0, 7736496, 3093048, 1140020, 482885, 208049145] }

theorem case_37_31_16_checked :
    (Witness.linear .conditional case_37_31_16).check 37 31 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_31_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 742900, 742900] }

theorem case_37_31_17_checked :
    (Witness.linear .negative case_37_31_17).check 37 31 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_31_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_37_31_18_checked :
    (Witness.linear .negative case_37_31_18).check 37 31 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_31_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_37_31_19_checked :
    (Witness.linear .negative case_37_31_19).check 37 31 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_31_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_37_31_20_checked :
    (Witness.linear .negative case_37_31_20).check 37 31 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_32_1_checked :
    (Witness.rising).check 37 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_32_2_checked :
    (Witness.rising).check 37 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_32_3_checked :
    (Witness.rising).check 37 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_32_4_checked :
    (Witness.rising).check 37 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_32_5_checked :
    (Witness.rising).check 37 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_32_6_checked :
    (Witness.rising).check 37 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_32_7_checked :
    (Witness.rising).check 37 32 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_32_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2] }

theorem case_37_32_8_checked :
    (Witness.linear .positive case_37_32_8).check 37 32 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_32_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_37_32_9_checked :
    (Witness.linear .positive case_37_32_9).check 37 32 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_32_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_37_32_10_checked :
    (Witness.linear .positive case_37_32_10).check 37 32 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_37_32_11_checked :
    (Witness.linear .positive case_37_32_11).check 37 32 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_37_32_12_checked :
    (Witness.linear .positive case_37_32_12).check 37 32 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_32_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_37_32_13_checked :
    (Witness.linear .positive case_37_32_13).check 37 32 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_32_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_37_32_14_checked :
    (Witness.linear .positive case_37_32_14).check 37 32 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_32_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862] }

theorem case_37_32_15_checked :
    (Witness.linear .positive case_37_32_15).check 37 32 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_32_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796] }

theorem case_37_32_16_checked :
    (Witness.linear .positive case_37_32_16).check 37 32 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_32_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 2674440, 2674440] }

theorem case_37_32_17_checked :
    (Witness.linear .negative case_37_32_17).check 37 32 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_32_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_37_32_18_checked :
    (Witness.linear .negative case_37_32_18).check 37 32 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_32_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_37_32_19_checked :
    (Witness.linear .negative case_37_32_19).check 37 32 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_32_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_37_32_20_checked :
    (Witness.linear .negative case_37_32_20).check 37 32 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_33_1_checked :
    (Witness.rising).check 37 33 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_33_2_checked :
    (Witness.rising).check 37 33 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_33_3_checked :
    (Witness.rising).check 37 33 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_33_4_checked :
    (Witness.rising).check 37 33 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_33_5_checked :
    (Witness.rising).check 37 33 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_33_6_checked :
    (Witness.rising).check 37 33 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_33_7_checked :
    (Witness.rising).check 37 33 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_33_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5] }

theorem case_37_33_8_checked :
    (Witness.linear .positive case_37_33_8).check 37 33 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_33_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_37_33_9_checked :
    (Witness.linear .positive case_37_33_9).check 37 33 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_33_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_37_33_10_checked :
    (Witness.linear .positive case_37_33_10).check 37 33 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_33_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_37_33_11_checked :
    (Witness.linear .positive case_37_33_11).check 37 33 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_33_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_37_33_12_checked :
    (Witness.linear .positive case_37_33_12).check 37 33 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_33_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_37_33_13_checked :
    (Witness.linear .positive case_37_33_13).check 37 33 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_33_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_37_33_14_checked :
    (Witness.linear .positive case_37_33_14).check 37 33 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_33_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796] }

theorem case_37_33_15_checked :
    (Witness.linear .positive case_37_33_15).check 37 33 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_33_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786] }

theorem case_37_33_16_checked :
    (Witness.linear .positive case_37_33_16).check 37 33 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_33_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 9694845, 9694845] }

theorem case_37_33_17_checked :
    (Witness.linear .negative case_37_33_17).check 37 33 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_33_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_37_33_18_checked :
    (Witness.linear .negative case_37_33_18).check 37 33 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_33_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_37_33_19_checked :
    (Witness.linear .negative case_37_33_19).check 37 33 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_33_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_37_33_20_checked :
    (Witness.linear .negative case_37_33_20).check 37 33 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_33_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_37_33_21_checked :
    (Witness.linear .negative case_37_33_21).check 37 33 21 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_34_1_checked :
    (Witness.rising).check 37 34 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_34_2_checked :
    (Witness.rising).check 37 34 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_34_3_checked :
    (Witness.rising).check 37 34 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_34_4_checked :
    (Witness.rising).check 37 34 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_34_5_checked :
    (Witness.rising).check 37 34 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_34_6_checked :
    (Witness.rising).check 37 34 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_34_7_checked :
    (Witness.rising).check 37 34 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_34_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14] }

theorem case_37_34_8_checked :
    (Witness.linear .positive case_37_34_8).check 37 34 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_34_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_37_34_9_checked :
    (Witness.linear .positive case_37_34_9).check 37 34 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_34_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_37_34_10_checked :
    (Witness.linear .positive case_37_34_10).check 37 34 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_34_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_37_34_11_checked :
    (Witness.linear .positive case_37_34_11).check 37 34 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_34_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_37_34_12_checked :
    (Witness.linear .positive case_37_34_12).check 37 34 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_34_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_37_34_13_checked :
    (Witness.linear .positive case_37_34_13).check 37 34 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_34_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_37_34_14_checked :
    (Witness.linear .positive case_37_34_14).check 37 34 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_34_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_37_34_15_checked :
    (Witness.linear .positive case_37_34_15).check 37 34 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_34_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012] }

theorem case_37_34_16_checked :
    (Witness.linear .positive case_37_34_16).check 37 34 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_34_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900] }

theorem case_37_34_17_checked :
    (Witness.linear .positive case_37_34_17).check 37 34 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_34_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_37_34_18_checked :
    (Witness.linear .negative case_37_34_18).check 37 34 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_34_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_37_34_19_checked :
    (Witness.linear .negative case_37_34_19).check 37 34 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_34_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_37_34_20_checked :
    (Witness.linear .negative case_37_34_20).check 37 34 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_34_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_37_34_21_checked :
    (Witness.linear .negative case_37_34_21).check 37 34 21 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_34_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_37_34_22_checked :
    (Witness.linear .negative case_37_34_22).check 37 34 22 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_35_1_checked :
    (Witness.rising).check 37 35 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_35_2_checked :
    (Witness.rising).check 37 35 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_35_3_checked :
    (Witness.rising).check 37 35 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_35_4_checked :
    (Witness.rising).check 37 35 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_35_5_checked :
    (Witness.rising).check 37 35 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_35_6_checked :
    (Witness.rising).check 37 35 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_35_7_checked :
    (Witness.rising).check 37 35 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_35_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_37_35_8_checked :
    (Witness.linear .positive case_37_35_8).check 37 35 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_35_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_37_35_9_checked :
    (Witness.linear .positive case_37_35_9).check 37 35 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_35_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_37_35_10_checked :
    (Witness.linear .positive case_37_35_10).check 37 35 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_35_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_37_35_11_checked :
    (Witness.linear .positive case_37_35_11).check 37 35 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_35_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_37_35_12_checked :
    (Witness.linear .positive case_37_35_12).check 37 35 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_35_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_37_35_13_checked :
    (Witness.linear .positive case_37_35_13).check 37 35 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_35_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_37_35_14_checked :
    (Witness.linear .positive case_37_35_14).check 37 35 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_35_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_37_35_15_checked :
    (Witness.linear .positive case_37_35_15).check 37 35 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_35_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900] }

theorem case_37_35_16_checked :
    (Witness.linear .positive case_37_35_16).check 37 35 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_35_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440] }

theorem case_37_35_17_checked :
    (Witness.linear .positive case_37_35_17).check 37 35 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_35_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_37_35_18_checked :
    (Witness.linear .negative case_37_35_18).check 37 35 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_35_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_37_35_19_checked :
    (Witness.linear .negative case_37_35_19).check 37 35 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_35_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_37_35_20_checked :
    (Witness.linear .negative case_37_35_20).check 37 35 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_35_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_37_35_21_checked :
    (Witness.linear .negative case_37_35_21).check 37 35 21 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_35_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_37_35_22_checked :
    (Witness.linear .negative case_37_35_22).check 37 35 22 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_36_1_checked :
    (Witness.rising).check 37 36 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_36_2_checked :
    (Witness.rising).check 37 36 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_36_3_checked :
    (Witness.rising).check 37 36 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_36_4_checked :
    (Witness.rising).check 37 36 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_36_5_checked :
    (Witness.rising).check 37 36 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_36_6_checked :
    (Witness.rising).check 37 36 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_37_36_7_checked :
    (Witness.rising).check 37 36 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_36_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_37_36_8_checked :
    (Witness.linear .positive case_37_36_8).check 37 36 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_36_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_37_36_9_checked :
    (Witness.linear .positive case_37_36_9).check 37 36 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_36_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_37_36_10_checked :
    (Witness.linear .positive case_37_36_10).check 37 36 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_36_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_37_36_11_checked :
    (Witness.linear .positive case_37_36_11).check 37 36 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_36_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_37_36_12_checked :
    (Witness.linear .positive case_37_36_12).check 37 36 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_36_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_37_36_13_checked :
    (Witness.linear .positive case_37_36_13).check 37 36 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_36_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_37_36_14_checked :
    (Witness.linear .positive case_37_36_14).check 37 36 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_36_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_37_36_15_checked :
    (Witness.linear .positive case_37_36_15).check 37 36 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_36_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_37_36_16_checked :
    (Witness.linear .positive case_37_36_16).check 37 36 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_36_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0] }

theorem case_37_36_17_checked :
    (Witness.linear .positive case_37_36_17).check 37 36 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_36_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0] }

theorem case_37_36_18_checked :
    (Witness.linear .positive case_37_36_18).check 37 36 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_36_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_37_36_19_checked :
    (Witness.linear .negative case_37_36_19).check 37 36 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_36_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_37_36_20_checked :
    (Witness.linear .negative case_37_36_20).check 37 36 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_36_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_37_36_21_checked :
    (Witness.linear .negative case_37_36_21).check 37 36 21 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_36_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_37_36_22_checked :
    (Witness.linear .negative case_37_36_22).check 37 36 22 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_37_36_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_37_36_23_checked :
    (Witness.linear .negative case_37_36_23).check 37 36 23 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_37 (a k : ℕ) (h : Domain 37 a k) :
    ∃ w : Witness, w.check 37 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 19 ≤ a := by omega
  have haHi : a ≤ 36 := by omega
  interval_cases a

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_37_19_1_checked⟩

    · exact ⟨Witness.rising, case_37_19_2_checked⟩

    · exact ⟨Witness.rising, case_37_19_3_checked⟩

    · exact ⟨Witness.rising, case_37_19_4_checked⟩

    · exact ⟨Witness.rising, case_37_19_5_checked⟩

    · exact ⟨Witness.rising, case_37_19_6_checked⟩

    · exact ⟨Witness.rising, case_37_19_7_checked⟩

    · exact ⟨Witness.rising, case_37_19_8_checked⟩

    · exact ⟨Witness.linear .positive case_37_19_9, case_37_19_9_checked⟩

    · exact ⟨Witness.linear .positive case_37_19_10, case_37_19_10_checked⟩

    · exact ⟨Witness.linear .conditional case_37_19_11, case_37_19_11_checked⟩

    · exact ⟨Witness.linear .conditional case_37_19_12, case_37_19_12_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_37_20_1_checked⟩

    · exact ⟨Witness.rising, case_37_20_2_checked⟩

    · exact ⟨Witness.rising, case_37_20_3_checked⟩

    · exact ⟨Witness.rising, case_37_20_4_checked⟩

    · exact ⟨Witness.rising, case_37_20_5_checked⟩

    · exact ⟨Witness.rising, case_37_20_6_checked⟩

    · exact ⟨Witness.rising, case_37_20_7_checked⟩

    · exact ⟨Witness.rising, case_37_20_8_checked⟩

    · exact ⟨Witness.linear .positive case_37_20_9, case_37_20_9_checked⟩

    · exact ⟨Witness.linear .positive case_37_20_10, case_37_20_10_checked⟩

    · exact ⟨Witness.linear .conditional case_37_20_11, case_37_20_11_checked⟩

    · exact ⟨Witness.linear .conditional case_37_20_12, case_37_20_12_checked⟩

  · have hkHi : k ≤ 13 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_37_21_1_checked⟩

    · exact ⟨Witness.rising, case_37_21_2_checked⟩

    · exact ⟨Witness.rising, case_37_21_3_checked⟩

    · exact ⟨Witness.rising, case_37_21_4_checked⟩

    · exact ⟨Witness.rising, case_37_21_5_checked⟩

    · exact ⟨Witness.rising, case_37_21_6_checked⟩

    · exact ⟨Witness.rising, case_37_21_7_checked⟩

    · exact ⟨Witness.rising, case_37_21_8_checked⟩

    · exact ⟨Witness.linear .positive case_37_21_9, case_37_21_9_checked⟩

    · exact ⟨Witness.linear .positive case_37_21_10, case_37_21_10_checked⟩

    · exact ⟨Witness.linear .conditional case_37_21_11, case_37_21_11_checked⟩

    · exact ⟨Witness.linear .conditional case_37_21_12, case_37_21_12_checked⟩

    · exact ⟨Witness.linear .conditional case_37_21_13, case_37_21_13_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_37_22_1_checked⟩

    · exact ⟨Witness.rising, case_37_22_2_checked⟩

    · exact ⟨Witness.rising, case_37_22_3_checked⟩

    · exact ⟨Witness.rising, case_37_22_4_checked⟩

    · exact ⟨Witness.rising, case_37_22_5_checked⟩

    · exact ⟨Witness.rising, case_37_22_6_checked⟩

    · exact ⟨Witness.rising, case_37_22_7_checked⟩

    · exact ⟨Witness.linear .positive case_37_22_8, case_37_22_8_checked⟩

    · exact ⟨Witness.linear .positive case_37_22_9, case_37_22_9_checked⟩

    · exact ⟨Witness.linear .positive case_37_22_10, case_37_22_10_checked⟩

    · exact ⟨Witness.linear .positive case_37_22_11, case_37_22_11_checked⟩

    · exact ⟨Witness.linear .conditional case_37_22_12, case_37_22_12_checked⟩

    · exact ⟨Witness.linear .conditional case_37_22_13, case_37_22_13_checked⟩

    · exact ⟨Witness.linear .negative case_37_22_14, case_37_22_14_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_37_23_1_checked⟩

    · exact ⟨Witness.rising, case_37_23_2_checked⟩

    · exact ⟨Witness.rising, case_37_23_3_checked⟩

    · exact ⟨Witness.rising, case_37_23_4_checked⟩

    · exact ⟨Witness.rising, case_37_23_5_checked⟩

    · exact ⟨Witness.rising, case_37_23_6_checked⟩

    · exact ⟨Witness.rising, case_37_23_7_checked⟩

    · exact ⟨Witness.linear .positive case_37_23_8, case_37_23_8_checked⟩

    · exact ⟨Witness.linear .positive case_37_23_9, case_37_23_9_checked⟩

    · exact ⟨Witness.linear .positive case_37_23_10, case_37_23_10_checked⟩

    · exact ⟨Witness.linear .positive case_37_23_11, case_37_23_11_checked⟩

    · exact ⟨Witness.linear .conditional case_37_23_12, case_37_23_12_checked⟩

    · exact ⟨Witness.linear .conditional case_37_23_13, case_37_23_13_checked⟩

    · exact ⟨Witness.linear .negative case_37_23_14, case_37_23_14_checked⟩

  · have hkHi : k ≤ 15 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_37_24_1_checked⟩

    · exact ⟨Witness.rising, case_37_24_2_checked⟩

    · exact ⟨Witness.rising, case_37_24_3_checked⟩

    · exact ⟨Witness.rising, case_37_24_4_checked⟩

    · exact ⟨Witness.rising, case_37_24_5_checked⟩

    · exact ⟨Witness.rising, case_37_24_6_checked⟩

    · exact ⟨Witness.rising, case_37_24_7_checked⟩

    · exact ⟨Witness.linear .positive case_37_24_8, case_37_24_8_checked⟩

    · exact ⟨Witness.linear .positive case_37_24_9, case_37_24_9_checked⟩

    · exact ⟨Witness.linear .positive case_37_24_10, case_37_24_10_checked⟩

    · exact ⟨Witness.linear .positive case_37_24_11, case_37_24_11_checked⟩

    · exact ⟨Witness.linear .conditional case_37_24_12, case_37_24_12_checked⟩

    · exact ⟨Witness.linear .conditional case_37_24_13, case_37_24_13_checked⟩

    · exact ⟨Witness.linear .negative case_37_24_14, case_37_24_14_checked⟩

    · exact ⟨Witness.linear .negative case_37_24_15, case_37_24_15_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_37_25_1_checked⟩

    · exact ⟨Witness.rising, case_37_25_2_checked⟩

    · exact ⟨Witness.rising, case_37_25_3_checked⟩

    · exact ⟨Witness.rising, case_37_25_4_checked⟩

    · exact ⟨Witness.rising, case_37_25_5_checked⟩

    · exact ⟨Witness.rising, case_37_25_6_checked⟩

    · exact ⟨Witness.rising, case_37_25_7_checked⟩

    · exact ⟨Witness.linear .positive case_37_25_8, case_37_25_8_checked⟩

    · exact ⟨Witness.linear .positive case_37_25_9, case_37_25_9_checked⟩

    · exact ⟨Witness.linear .positive case_37_25_10, case_37_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_37_25_11, case_37_25_11_checked⟩

    · exact ⟨Witness.linear .conditional case_37_25_12, case_37_25_12_checked⟩

    · exact ⟨Witness.linear .conditional case_37_25_13, case_37_25_13_checked⟩

    · exact ⟨Witness.linear .conditional case_37_25_14, case_37_25_14_checked⟩

    · exact ⟨Witness.linear .negative case_37_25_15, case_37_25_15_checked⟩

    · exact ⟨Witness.linear .negative case_37_25_16, case_37_25_16_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_37_26_1_checked⟩

    · exact ⟨Witness.rising, case_37_26_2_checked⟩

    · exact ⟨Witness.rising, case_37_26_3_checked⟩

    · exact ⟨Witness.rising, case_37_26_4_checked⟩

    · exact ⟨Witness.rising, case_37_26_5_checked⟩

    · exact ⟨Witness.rising, case_37_26_6_checked⟩

    · exact ⟨Witness.rising, case_37_26_7_checked⟩

    · exact ⟨Witness.linear .positive case_37_26_8, case_37_26_8_checked⟩

    · exact ⟨Witness.linear .positive case_37_26_9, case_37_26_9_checked⟩

    · exact ⟨Witness.linear .positive case_37_26_10, case_37_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_37_26_11, case_37_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_37_26_12, case_37_26_12_checked⟩

    · exact ⟨Witness.linear .conditional case_37_26_13, case_37_26_13_checked⟩

    · exact ⟨Witness.linear .conditional case_37_26_14, case_37_26_14_checked⟩

    · exact ⟨Witness.linear .conditional case_37_26_15, case_37_26_15_checked⟩

    · exact ⟨Witness.linear .negative case_37_26_16, case_37_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_37_27_1_checked⟩

    · exact ⟨Witness.rising, case_37_27_2_checked⟩

    · exact ⟨Witness.rising, case_37_27_3_checked⟩

    · exact ⟨Witness.rising, case_37_27_4_checked⟩

    · exact ⟨Witness.rising, case_37_27_5_checked⟩

    · exact ⟨Witness.rising, case_37_27_6_checked⟩

    · exact ⟨Witness.rising, case_37_27_7_checked⟩

    · exact ⟨Witness.linear .positive case_37_27_8, case_37_27_8_checked⟩

    · exact ⟨Witness.linear .positive case_37_27_9, case_37_27_9_checked⟩

    · exact ⟨Witness.linear .positive case_37_27_10, case_37_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_37_27_11, case_37_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_37_27_12, case_37_27_12_checked⟩

    · exact ⟨Witness.linear .positive case_37_27_13, case_37_27_13_checked⟩

    · exact ⟨Witness.linear .conditional case_37_27_14, case_37_27_14_checked⟩

    · exact ⟨Witness.linear .conditional case_37_27_15, case_37_27_15_checked⟩

    · exact ⟨Witness.linear .negative case_37_27_16, case_37_27_16_checked⟩

    · exact ⟨Witness.linear .negative case_37_27_17, case_37_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_37_28_1_checked⟩

    · exact ⟨Witness.rising, case_37_28_2_checked⟩

    · exact ⟨Witness.rising, case_37_28_3_checked⟩

    · exact ⟨Witness.rising, case_37_28_4_checked⟩

    · exact ⟨Witness.rising, case_37_28_5_checked⟩

    · exact ⟨Witness.rising, case_37_28_6_checked⟩

    · exact ⟨Witness.rising, case_37_28_7_checked⟩

    · exact ⟨Witness.linear .positive case_37_28_8, case_37_28_8_checked⟩

    · exact ⟨Witness.linear .positive case_37_28_9, case_37_28_9_checked⟩

    · exact ⟨Witness.linear .positive case_37_28_10, case_37_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_37_28_11, case_37_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_37_28_12, case_37_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_37_28_13, case_37_28_13_checked⟩

    · exact ⟨Witness.linear .conditional case_37_28_14, case_37_28_14_checked⟩

    · exact ⟨Witness.linear .conditional case_37_28_15, case_37_28_15_checked⟩

    · exact ⟨Witness.linear .negative case_37_28_16, case_37_28_16_checked⟩

    · exact ⟨Witness.linear .negative case_37_28_17, case_37_28_17_checked⟩

    · exact ⟨Witness.linear .negative case_37_28_18, case_37_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_37_29_1_checked⟩

    · exact ⟨Witness.rising, case_37_29_2_checked⟩

    · exact ⟨Witness.rising, case_37_29_3_checked⟩

    · exact ⟨Witness.rising, case_37_29_4_checked⟩

    · exact ⟨Witness.rising, case_37_29_5_checked⟩

    · exact ⟨Witness.rising, case_37_29_6_checked⟩

    · exact ⟨Witness.rising, case_37_29_7_checked⟩

    · exact ⟨Witness.linear .positive case_37_29_8, case_37_29_8_checked⟩

    · exact ⟨Witness.linear .positive case_37_29_9, case_37_29_9_checked⟩

    · exact ⟨Witness.linear .positive case_37_29_10, case_37_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_37_29_11, case_37_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_37_29_12, case_37_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_37_29_13, case_37_29_13_checked⟩

    · exact ⟨Witness.linear .positive case_37_29_14, case_37_29_14_checked⟩

    · exact ⟨Witness.linear .conditional case_37_29_15, case_37_29_15_checked⟩

    · exact ⟨Witness.linear .conditional case_37_29_16, case_37_29_16_checked⟩

    · exact ⟨Witness.linear .negative case_37_29_17, case_37_29_17_checked⟩

    · exact ⟨Witness.linear .negative case_37_29_18, case_37_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_37_30_1_checked⟩

    · exact ⟨Witness.rising, case_37_30_2_checked⟩

    · exact ⟨Witness.rising, case_37_30_3_checked⟩

    · exact ⟨Witness.rising, case_37_30_4_checked⟩

    · exact ⟨Witness.rising, case_37_30_5_checked⟩

    · exact ⟨Witness.rising, case_37_30_6_checked⟩

    · exact ⟨Witness.rising, case_37_30_7_checked⟩

    · exact ⟨Witness.linear .positive case_37_30_8, case_37_30_8_checked⟩

    · exact ⟨Witness.linear .positive case_37_30_9, case_37_30_9_checked⟩

    · exact ⟨Witness.linear .positive case_37_30_10, case_37_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_37_30_11, case_37_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_37_30_12, case_37_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_37_30_13, case_37_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_37_30_14, case_37_30_14_checked⟩

    · exact ⟨Witness.linear .conditional case_37_30_15, case_37_30_15_checked⟩

    · exact ⟨Witness.linear .conditional case_37_30_16, case_37_30_16_checked⟩

    · exact ⟨Witness.linear .negative case_37_30_17, case_37_30_17_checked⟩

    · exact ⟨Witness.linear .negative case_37_30_18, case_37_30_18_checked⟩

    · exact ⟨Witness.linear .negative case_37_30_19, case_37_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_37_31_1_checked⟩

    · exact ⟨Witness.rising, case_37_31_2_checked⟩

    · exact ⟨Witness.rising, case_37_31_3_checked⟩

    · exact ⟨Witness.rising, case_37_31_4_checked⟩

    · exact ⟨Witness.rising, case_37_31_5_checked⟩

    · exact ⟨Witness.rising, case_37_31_6_checked⟩

    · exact ⟨Witness.rising, case_37_31_7_checked⟩

    · exact ⟨Witness.linear .positive case_37_31_8, case_37_31_8_checked⟩

    · exact ⟨Witness.linear .positive case_37_31_9, case_37_31_9_checked⟩

    · exact ⟨Witness.linear .positive case_37_31_10, case_37_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_37_31_11, case_37_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_37_31_12, case_37_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_37_31_13, case_37_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_37_31_14, case_37_31_14_checked⟩

    · exact ⟨Witness.linear .positive case_37_31_15, case_37_31_15_checked⟩

    · exact ⟨Witness.linear .conditional case_37_31_16, case_37_31_16_checked⟩

    · exact ⟨Witness.linear .negative case_37_31_17, case_37_31_17_checked⟩

    · exact ⟨Witness.linear .negative case_37_31_18, case_37_31_18_checked⟩

    · exact ⟨Witness.linear .negative case_37_31_19, case_37_31_19_checked⟩

    · exact ⟨Witness.linear .negative case_37_31_20, case_37_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_37_32_1_checked⟩

    · exact ⟨Witness.rising, case_37_32_2_checked⟩

    · exact ⟨Witness.rising, case_37_32_3_checked⟩

    · exact ⟨Witness.rising, case_37_32_4_checked⟩

    · exact ⟨Witness.rising, case_37_32_5_checked⟩

    · exact ⟨Witness.rising, case_37_32_6_checked⟩

    · exact ⟨Witness.rising, case_37_32_7_checked⟩

    · exact ⟨Witness.linear .positive case_37_32_8, case_37_32_8_checked⟩

    · exact ⟨Witness.linear .positive case_37_32_9, case_37_32_9_checked⟩

    · exact ⟨Witness.linear .positive case_37_32_10, case_37_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_37_32_11, case_37_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_37_32_12, case_37_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_37_32_13, case_37_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_37_32_14, case_37_32_14_checked⟩

    · exact ⟨Witness.linear .positive case_37_32_15, case_37_32_15_checked⟩

    · exact ⟨Witness.linear .positive case_37_32_16, case_37_32_16_checked⟩

    · exact ⟨Witness.linear .negative case_37_32_17, case_37_32_17_checked⟩

    · exact ⟨Witness.linear .negative case_37_32_18, case_37_32_18_checked⟩

    · exact ⟨Witness.linear .negative case_37_32_19, case_37_32_19_checked⟩

    · exact ⟨Witness.linear .negative case_37_32_20, case_37_32_20_checked⟩

  · have hkHi : k ≤ 21 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_37_33_1_checked⟩

    · exact ⟨Witness.rising, case_37_33_2_checked⟩

    · exact ⟨Witness.rising, case_37_33_3_checked⟩

    · exact ⟨Witness.rising, case_37_33_4_checked⟩

    · exact ⟨Witness.rising, case_37_33_5_checked⟩

    · exact ⟨Witness.rising, case_37_33_6_checked⟩

    · exact ⟨Witness.rising, case_37_33_7_checked⟩

    · exact ⟨Witness.linear .positive case_37_33_8, case_37_33_8_checked⟩

    · exact ⟨Witness.linear .positive case_37_33_9, case_37_33_9_checked⟩

    · exact ⟨Witness.linear .positive case_37_33_10, case_37_33_10_checked⟩

    · exact ⟨Witness.linear .positive case_37_33_11, case_37_33_11_checked⟩

    · exact ⟨Witness.linear .positive case_37_33_12, case_37_33_12_checked⟩

    · exact ⟨Witness.linear .positive case_37_33_13, case_37_33_13_checked⟩

    · exact ⟨Witness.linear .positive case_37_33_14, case_37_33_14_checked⟩

    · exact ⟨Witness.linear .positive case_37_33_15, case_37_33_15_checked⟩

    · exact ⟨Witness.linear .positive case_37_33_16, case_37_33_16_checked⟩

    · exact ⟨Witness.linear .negative case_37_33_17, case_37_33_17_checked⟩

    · exact ⟨Witness.linear .negative case_37_33_18, case_37_33_18_checked⟩

    · exact ⟨Witness.linear .negative case_37_33_19, case_37_33_19_checked⟩

    · exact ⟨Witness.linear .negative case_37_33_20, case_37_33_20_checked⟩

    · exact ⟨Witness.linear .negative case_37_33_21, case_37_33_21_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_37_34_1_checked⟩

    · exact ⟨Witness.rising, case_37_34_2_checked⟩

    · exact ⟨Witness.rising, case_37_34_3_checked⟩

    · exact ⟨Witness.rising, case_37_34_4_checked⟩

    · exact ⟨Witness.rising, case_37_34_5_checked⟩

    · exact ⟨Witness.rising, case_37_34_6_checked⟩

    · exact ⟨Witness.rising, case_37_34_7_checked⟩

    · exact ⟨Witness.linear .positive case_37_34_8, case_37_34_8_checked⟩

    · exact ⟨Witness.linear .positive case_37_34_9, case_37_34_9_checked⟩

    · exact ⟨Witness.linear .positive case_37_34_10, case_37_34_10_checked⟩

    · exact ⟨Witness.linear .positive case_37_34_11, case_37_34_11_checked⟩

    · exact ⟨Witness.linear .positive case_37_34_12, case_37_34_12_checked⟩

    · exact ⟨Witness.linear .positive case_37_34_13, case_37_34_13_checked⟩

    · exact ⟨Witness.linear .positive case_37_34_14, case_37_34_14_checked⟩

    · exact ⟨Witness.linear .positive case_37_34_15, case_37_34_15_checked⟩

    · exact ⟨Witness.linear .positive case_37_34_16, case_37_34_16_checked⟩

    · exact ⟨Witness.linear .positive case_37_34_17, case_37_34_17_checked⟩

    · exact ⟨Witness.linear .negative case_37_34_18, case_37_34_18_checked⟩

    · exact ⟨Witness.linear .negative case_37_34_19, case_37_34_19_checked⟩

    · exact ⟨Witness.linear .negative case_37_34_20, case_37_34_20_checked⟩

    · exact ⟨Witness.linear .negative case_37_34_21, case_37_34_21_checked⟩

    · exact ⟨Witness.linear .negative case_37_34_22, case_37_34_22_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_37_35_1_checked⟩

    · exact ⟨Witness.rising, case_37_35_2_checked⟩

    · exact ⟨Witness.rising, case_37_35_3_checked⟩

    · exact ⟨Witness.rising, case_37_35_4_checked⟩

    · exact ⟨Witness.rising, case_37_35_5_checked⟩

    · exact ⟨Witness.rising, case_37_35_6_checked⟩

    · exact ⟨Witness.rising, case_37_35_7_checked⟩

    · exact ⟨Witness.linear .positive case_37_35_8, case_37_35_8_checked⟩

    · exact ⟨Witness.linear .positive case_37_35_9, case_37_35_9_checked⟩

    · exact ⟨Witness.linear .positive case_37_35_10, case_37_35_10_checked⟩

    · exact ⟨Witness.linear .positive case_37_35_11, case_37_35_11_checked⟩

    · exact ⟨Witness.linear .positive case_37_35_12, case_37_35_12_checked⟩

    · exact ⟨Witness.linear .positive case_37_35_13, case_37_35_13_checked⟩

    · exact ⟨Witness.linear .positive case_37_35_14, case_37_35_14_checked⟩

    · exact ⟨Witness.linear .positive case_37_35_15, case_37_35_15_checked⟩

    · exact ⟨Witness.linear .positive case_37_35_16, case_37_35_16_checked⟩

    · exact ⟨Witness.linear .positive case_37_35_17, case_37_35_17_checked⟩

    · exact ⟨Witness.linear .negative case_37_35_18, case_37_35_18_checked⟩

    · exact ⟨Witness.linear .negative case_37_35_19, case_37_35_19_checked⟩

    · exact ⟨Witness.linear .negative case_37_35_20, case_37_35_20_checked⟩

    · exact ⟨Witness.linear .negative case_37_35_21, case_37_35_21_checked⟩

    · exact ⟨Witness.linear .negative case_37_35_22, case_37_35_22_checked⟩

  · have hkHi : k ≤ 23 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_37_36_1_checked⟩

    · exact ⟨Witness.rising, case_37_36_2_checked⟩

    · exact ⟨Witness.rising, case_37_36_3_checked⟩

    · exact ⟨Witness.rising, case_37_36_4_checked⟩

    · exact ⟨Witness.rising, case_37_36_5_checked⟩

    · exact ⟨Witness.rising, case_37_36_6_checked⟩

    · exact ⟨Witness.rising, case_37_36_7_checked⟩

    · exact ⟨Witness.linear .positive case_37_36_8, case_37_36_8_checked⟩

    · exact ⟨Witness.linear .positive case_37_36_9, case_37_36_9_checked⟩

    · exact ⟨Witness.linear .positive case_37_36_10, case_37_36_10_checked⟩

    · exact ⟨Witness.linear .positive case_37_36_11, case_37_36_11_checked⟩

    · exact ⟨Witness.linear .positive case_37_36_12, case_37_36_12_checked⟩

    · exact ⟨Witness.linear .positive case_37_36_13, case_37_36_13_checked⟩

    · exact ⟨Witness.linear .positive case_37_36_14, case_37_36_14_checked⟩

    · exact ⟨Witness.linear .positive case_37_36_15, case_37_36_15_checked⟩

    · exact ⟨Witness.linear .positive case_37_36_16, case_37_36_16_checked⟩

    · exact ⟨Witness.linear .positive case_37_36_17, case_37_36_17_checked⟩

    · exact ⟨Witness.linear .positive case_37_36_18, case_37_36_18_checked⟩

    · exact ⟨Witness.linear .negative case_37_36_19, case_37_36_19_checked⟩

    · exact ⟨Witness.linear .negative case_37_36_20, case_37_36_20_checked⟩

    · exact ⟨Witness.linear .negative case_37_36_21, case_37_36_21_checked⟩

    · exact ⟨Witness.linear .negative case_37_36_22, case_37_36_22_checked⟩

    · exact ⟨Witness.linear .negative case_37_36_23, case_37_36_23_checked⟩


#print axioms coverage_37
end ForestUnimodality.FiniteRows.FiniteData
