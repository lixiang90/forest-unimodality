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

theorem case_25_13_1_checked :
    (Witness.rising).check 25 13 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_13_2_checked :
    (Witness.rising).check 25 13 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_13_3_checked :
    (Witness.rising).check 25 13 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_13_4_checked :
    (Witness.rising).check 25 13 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_13_5_checked :
    (Witness.rising).check 25 13 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_13_6_checked :
    (Witness.rising).check 25 13 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_13_7 : Certificate := {
  objectiveScale := 29400000
  eta := 4435754400
  rows := #[⟨.count 2, 970552800⟩, ⟨.count 3, 220358880⟩, ⟨.count 4, 69289920⟩, ⟨.count 5, 29370600⟩, ⟨.count 6, 29408400⟩, ⟨.path 8, 10500000⟩, ⟨.privateRow 7 0, 385200⟩, ⟨.privateRow 8 0, 1749300⟩, ⟨.privateRow 9 0, 3062304⟩, ⟨.hall 6 2, 890640⟩, ⟨.hall 5 3, 592515⟩, ⟨.hall 4 5, 487480⟩, ⟨.hall 3 9, 22035888⟩]
  caps := #[0, 0, 0, 141120, 56448, 39200, 0, 6060, 24780, 0, 0, 0, 0] }

theorem case_25_13_7_checked :
    (Witness.linear .positive case_25_13_7).check 25 13 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_13_8 : Certificate := {
  objectiveScale := 351351000000
  eta := 31058022996000
  rows := #[⟨.count 2, 8842239806400⟩, ⟨.count 3, 2776628574720⟩, ⟨.count 4, 1031135545440⟩, ⟨.count 5, 498695897700⟩, ⟨.count 6, 362523961800⟩, ⟨.count 7, 277754677200⟩, ⟨.count 9, 351210459600⟩, ⟨.path 6, 85051480800⟩, ⟨.path 7, 39640552875⟩, ⟨.privateRow 8 0, 28464115680⟩, ⟨.hall 6 3, 18488089620⟩, ⟨.hall 5 4, 19880610750⟩, ⟨.hall 4 6, 36516560080⟩, ⟨.hall 3 8, 126803044368⟩, ⟨.hall 2 10, 803839982400⟩, ⟨.assumptionRow 8, 238013951175⟩]
  caps := #[0, 0, 2592092250, 1491321600, 1201798422, 427395100, 182023050, 0, 361305945, 140540400, 0, 0, 0] }

theorem case_25_13_8_checked :
    (Witness.linear .conditional case_25_13_8).check 25 13 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_14_1_checked :
    (Witness.rising).check 25 14 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_14_2_checked :
    (Witness.rising).check 25 14 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_14_3_checked :
    (Witness.rising).check 25 14 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_14_4_checked :
    (Witness.rising).check 25 14 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_14_5_checked :
    (Witness.rising).check 25 14 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_14_6_checked :
    (Witness.rising).check 25 14 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_14_7 : Certificate := {
  objectiveScale := 7840000
  eta := 2018016000
  rows := #[⟨.count 2, 414081360⟩, ⟨.count 3, 94044720⟩, ⟨.count 4, 25742640⟩, ⟨.count 5, 9840600⟩, ⟨.count 6, 7854000⟩, ⟨.path 7, 2016056⟩, ⟨.path 8, 1120000⟩, ⟨.privateRow 3 11, 12332320⟩, ⟨.privateRow 7 1, 81840⟩, ⟨.privateRow 8 0, 159390⟩, ⟨.hall 6 3, 12045⟩]
  caps := #[0, 96096, 25872, 39200, 17920, 15456, 0, 8831, 4270, 0, 0, 0] }

theorem case_25_14_7_checked :
    (Witness.linear .positive case_25_14_7).check 25 14 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_14_8 : Certificate := {
  objectiveScale := 262218000000
  eta := 55737582516000
  rows := #[⟨.count 2, 13451028212160⟩, ⟨.count 3, 4095131927040⟩, ⟨.count 4, 1398450548880⟩, ⟨.count 5, 585899899200⟩, ⟨.count 6, 475768339200⟩, ⟨.count 9, 259029429120⟩, ⟨.path 6, 130698876000⟩, ⟨.privateRow 3 9, 3768946720⟩, ⟨.privateRow 4 7, 116312693805⟩, ⟨.privateRow 4 8, 284983766760⟩, ⟨.privateRow 5 5, 110572086240⟩, ⟨.privateRow 5 6, 177366877380⟩, ⟨.privateRow 5 7, 106019981760⟩, ⟨.privateRow 6 3, 84036498700⟩, ⟨.privateRow 6 4, 87848274360⟩, ⟨.privateRow 7 0, 23402956500⟩, ⟨.privateRow 7 1, 40780143360⟩, ⟨.privateRow 8 0, 22081377780⟩, ⟨.hall 3 10, 492548384160⟩, ⟨.hall 2 11, 1112438887560⟩, ⟨.assumptionRow 8, 227901355528⟩]
  caps := #[0, 0, 2423096016, 3153223304, 635618655, 0, 1092385140, 0, 1201133252, 3188570880, 0, 0] }

theorem case_25_14_8_checked :
    (Witness.linear .conditional case_25_14_8).check 25 14 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_15_1_checked :
    (Witness.rising).check 25 15 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_15_2_checked :
    (Witness.rising).check 25 15 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_15_3_checked :
    (Witness.rising).check 25 15 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_15_4_checked :
    (Witness.rising).check 25 15 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_15_5_checked :
    (Witness.rising).check 25 15 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_15_6_checked :
    (Witness.rising).check 25 15 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_15_7 : Certificate := {
  objectiveScale := 441000
  eta := 135197370
  rows := #[⟨.count 2, 29106000⟩, ⟨.count 3, 7058205⟩, ⟨.count 4, 1891890⟩, ⟨.count 5, 629475⟩, ⟨.count 6, 443520⟩, ⟨.path 7, 188993⟩, ⟨.hall 4 6, 8319⟩]
  caps := #[0, 0, 0, 0, 0, 518, 0, 0, 0, 0, 0] }

theorem case_25_15_7_checked :
    (Witness.linear .positive case_25_15_7).check 25 15 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_15_8 : Certificate := {
  objectiveScale := 368604600000
  eta := 145704680241120
  rows := #[⟨.count 2, 32923762872000⟩, ⟨.count 3, 8608428688860⟩, ⟨.count 4, 2856095882640⟩, ⟨.count 5, 1127192866800⟩, ⟨.count 6, 627659912880⟩, ⟨.count 7, 170295325200⟩, ⟨.path 6, 236077601760⟩, ⟨.privateRow 3 10, 459797378040⟩, ⟨.privateRow 3 11, 1126787401740⟩, ⟨.privateRow 4 7, 28950205284⟩, ⟨.privateRow 4 8, 616408257465⟩, ⟨.privateRow 4 9, 632525493600⟩, ⟨.privateRow 4 10, 138669050520⟩, ⟨.privateRow 5 5, 120017657760⟩, ⟨.privateRow 5 6, 396058270608⟩, ⟨.privateRow 5 7, 201110669760⟩, ⟨.privateRow 6 3, 148284364800⟩, ⟨.privateRow 6 4, 152319707540⟩, ⟨.privateRow 7 1, 110387862585⟩, ⟨.privateRow 8 0, 44702522865⟩, ⟨.privateRow 9 0, 51899527680⟩, ⟨.hall 2 12, 298671801120⟩, ⟨.assumptionRow 8, 393485410500⟩]
  caps := #[0, 0, 12950197260, 2618719740, 0, 681856812, 1903099380, 2414360130, 0, 5307906240, 0] }

theorem case_25_15_8_checked :
    (Witness.linear .conditional case_25_15_8).check 25 15 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_15_9 : Certificate := {
  objectiveScale := 3684800000
  eta := 996602246640
  rows := #[⟨.count 2, 168511062720⟩, ⟨.count 3, 25015830840⟩, ⟨.count 7, 15827551740⟩, ⟨.count 8, 51533401920⟩, ⟨.count 9, 18495116640⟩, ⟨.count 10, 7113506400⟩, ⟨.path 3, 25016191200⟩, ⟨.privateRow 2 10, 2904681780⟩, ⟨.privateRow 2 11, 34065791760⟩, ⟨.privateRow 2 12, 46988661720⟩, ⟨.privateRow 3 8, 10705827132⟩, ⟨.privateRow 3 9, 12898170285⟩, ⟨.privateRow 3 10, 25220014820⟩, ⟨.privateRow 3 11, 18475356900⟩, ⟨.privateRow 4 5, 2055416220⟩, ⟨.privateRow 4 6, 3635792160⟩, ⟨.privateRow 4 7, 8422730316⟩, ⟨.privateRow 4 8, 10973007045⟩, ⟨.privateRow 4 9, 8118430320⟩, ⟨.privateRow 5 2, 342502160⟩, ⟨.privateRow 5 3, 685239555⟩, ⟨.privateRow 5 4, 2431657800⟩, ⟨.privateRow 5 5, 4650125480⟩, ⟨.privateRow 5 6, 5523694176⟩, ⟨.privateRow 6 0, 342690348⟩, ⟨.privateRow 6 1, 479879400⟩, ⟨.privateRow 6 2, 1458692235⟩, ⟨.privateRow 6 3, 2833304760⟩, ⟨.privateRow 7 0, 1531850320⟩, ⟨.hall 2 12, 6991908000⟩, ⟨.hall 1 13, 38463745320⟩]
  caps := #[0, 158357360, 120420300, 9037735, 0, 10601884, 0, 31380020, 53798080, 0, 0] }

theorem case_25_15_9_checked :
    (Witness.linear .negative case_25_15_9).check 25 15 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_16_1_checked :
    (Witness.rising).check 25 16 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_16_2_checked :
    (Witness.rising).check 25 16 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_16_3_checked :
    (Witness.rising).check 25 16 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_16_4_checked :
    (Witness.rising).check 25 16 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_16_5_checked :
    (Witness.rising).check 25 16 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_16_6_checked :
    (Witness.rising).check 25 16 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_16_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_25_16_7_checked :
    (Witness.linear .positive case_25_16_7).check 25 16 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_16_8 : Certificate := {
  objectiveScale := 1018537500
  eta := 2204416093880
  rows := #[⟨.count 2, 344473999870⟩, ⟨.count 3, 52434310500⟩, ⟨.count 4, 7379643700⟩, ⟨.count 5, 2019691960⟩, ⟨.count 6, 990425865⟩, ⟨.count 7, 951585635⟩, ⟨.path 3, 19862399700⟩, ⟨.path 4, 2291524092⟩]
  caps := #[0, 226973032, 47156270, 19806936, 4567892, 17383040, 28111635, 66951865, 0, 0] }

theorem case_25_16_8_checked :
    (Witness.linear .positive case_25_16_8).check 25 16 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_16_9 : Certificate := {
  objectiveScale := 1075293000000
  eta := 1066697537875200
  rows := #[⟨.count 2, 200105145424800⟩, ⟨.count 3, 38770549349400⟩, ⟨.count 4, 7707270106800⟩, ⟨.count 5, 1163897143200⟩, ⟨.path 4, 3476286110880⟩, ⟨.path 5, 664854933600⟩, ⟨.privateRow 2 14, 14381936345700⟩, ⟨.privateRow 3 10, 1618100906400⟩, ⟨.privateRow 3 11, 7972222302000⟩, ⟨.privateRow 3 12, 7689527772300⟩, ⟨.privateRow 4 8, 2937420899820⟩, ⟨.privateRow 4 9, 4880916220950⟩, ⟨.privateRow 4 10, 2962969861500⟩, ⟨.privateRow 5 5, 232779428640⟩, ⟨.privateRow 5 6, 2250201143520⟩, ⟨.privateRow 5 7, 2624162241888⟩, ⟨.privateRow 6 3, 196052796225⟩, ⟨.privateRow 6 4, 1721006446500⟩, ⟨.privateRow 6 5, 272049129000⟩, ⟨.privateRow 7 1, 31541928000⟩, ⟨.privateRow 7 2, 833889721500⟩, ⟨.privateRow 8 0, 289791463500⟩, ⟨.privateRow 9 0, 99357073200⟩, ⟨.hall 2 13, 656466376500⟩, ⟨.assumptionRow 9, 494586989200⟩]
  caps := #[0, 1789727280, 0, 0, 0, 0, 6299424825, 0, 2162533700, 0] }

theorem case_25_16_9_checked :
    (Witness.linear .conditional case_25_16_9).check 25 16 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_16_10 : Certificate := {
  objectiveScale := 13
  eta := 93
  rows := #[⟨.assumptionRow 10, 6⟩]
  caps := #[0, 0, 58, 29, 17, 11, 6, 258, 244, 146] }

theorem case_25_16_10_checked :
    (Witness.linear .conditional case_25_16_10).check 25 16 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_17_1_checked :
    (Witness.rising).check 25 17 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_17_2_checked :
    (Witness.rising).check 25 17 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_17_3_checked :
    (Witness.rising).check 25 17 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_17_4_checked :
    (Witness.rising).check 25 17 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_17_5_checked :
    (Witness.rising).check 25 17 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_17_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1, 0, 0, 0] }

theorem case_25_17_6_checked :
    (Witness.linear .positive case_25_17_6).check 25 17 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_17_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0] }

theorem case_25_17_7_checked :
    (Witness.linear .positive case_25_17_7).check 25 17 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_17_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0] }

theorem case_25_17_8_checked :
    (Witness.linear .positive case_25_17_8).check 25 17 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_17_9 : Certificate := {
  objectiveScale := 139
  eta := 9295
  rows := #[⟨.assumptionRow 9, 149⟩]
  caps := #[0, 0, 3399, 1392, 646, 308, 6545, 5210, 2561] }

theorem case_25_17_9_checked :
    (Witness.linear .conditional case_25_17_9).check 25 17 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_17_10 : Certificate := {
  objectiveScale := 43
  eta := 278
  rows := #[⟨.assumptionRow 10, 19⟩]
  caps := #[0, 0, 169, 79, 52, 33, 2541, 2445, 1551] }

theorem case_25_17_10_checked :
    (Witness.linear .conditional case_25_17_10).check 25 17 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_18_1_checked :
    (Witness.rising).check 25 18 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_18_2_checked :
    (Witness.rising).check 25 18 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_18_3_checked :
    (Witness.rising).check 25 18 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_18_4_checked :
    (Witness.rising).check 25 18 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_18_5_checked :
    (Witness.rising).check 25 18 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_18_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1, 0, 0] }

theorem case_25_18_6_checked :
    (Witness.linear .positive case_25_18_6).check 25 18 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_18_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0] }

theorem case_25_18_7_checked :
    (Witness.linear .positive case_25_18_7).check 25 18 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_18_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1] }

theorem case_25_18_8_checked :
    (Witness.linear .positive case_25_18_8).check 25 18 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_18_9 : Certificate := {
  objectiveScale := 13
  eta := 3256
  rows := #[⟨.assumptionRow 9, 23⟩]
  caps := #[0, 0, 1095, 384, 142, 63, 33, 418] }

theorem case_25_18_9_checked :
    (Witness.linear .conditional case_25_18_9).check 25 18 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_18_10 : Certificate := {
  objectiveScale := 288
  eta := 14773
  rows := #[⟨.assumptionRow 10, 215⟩]
  caps := #[0, 0, 6045, 2544, 1282, 572, 26411, 23870] }

theorem case_25_18_10_checked :
    (Witness.linear .conditional case_25_18_10).check 25 18 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_18_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 132, 132] }

theorem case_25_18_11_checked :
    (Witness.linear .negative case_25_18_11).check 25 18 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_19_1_checked :
    (Witness.rising).check 25 19 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_19_2_checked :
    (Witness.rising).check 25 19 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_19_3_checked :
    (Witness.rising).check 25 19 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_19_4_checked :
    (Witness.rising).check 25 19 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_19_5_checked :
    (Witness.rising).check 25 19 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_19_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1, 0] }

theorem case_25_19_6_checked :
    (Witness.linear .positive case_25_19_6).check 25 19 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_19_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1] }

theorem case_25_19_7_checked :
    (Witness.linear .positive case_25_19_7).check 25 19 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_19_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1] }

theorem case_25_19_8_checked :
    (Witness.linear .positive case_25_19_8).check 25 19 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_19_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_25_19_9_checked :
    (Witness.linear .positive case_25_19_9).check 25 19 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_19_10 : Certificate := {
  objectiveScale := 27
  eta := 2717
  rows := #[⟨.assumptionRow 10, 25⟩]
  caps := #[0, 0, 1155, 471, 188, 2002, 4719] }

theorem case_25_19_10_checked :
    (Witness.linear .conditional case_25_19_10).check 25 19 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_19_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 429, 429] }

theorem case_25_19_11_checked :
    (Witness.linear .negative case_25_19_11).check 25 19 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_19_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_25_19_12_checked :
    (Witness.linear .negative case_25_19_12).check 25 19 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_20_1_checked :
    (Witness.rising).check 25 20 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_20_2_checked :
    (Witness.rising).check 25 20 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_20_3_checked :
    (Witness.rising).check 25 20 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_20_4_checked :
    (Witness.rising).check 25 20 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_20_5_checked :
    (Witness.rising).check 25 20 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_20_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1, 1] }

theorem case_25_20_6_checked :
    (Witness.linear .positive case_25_20_6).check 25 20 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_20_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1] }

theorem case_25_20_7_checked :
    (Witness.linear .positive case_25_20_7).check 25 20 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_20_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2] }

theorem case_25_20_8_checked :
    (Witness.linear .positive case_25_20_8).check 25 20 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_20_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_25_20_9_checked :
    (Witness.linear .positive case_25_20_9).check 25 20 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_20_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_25_20_10_checked :
    (Witness.linear .positive case_25_20_10).check 25 20 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_20_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 1430, 1430] }

theorem case_25_20_11_checked :
    (Witness.linear .negative case_25_20_11).check 25 20 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_20_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_25_20_12_checked :
    (Witness.linear .negative case_25_20_12).check 25 20 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_21_1_checked :
    (Witness.rising).check 25 21 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_21_2_checked :
    (Witness.rising).check 25 21 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_21_3_checked :
    (Witness.rising).check 25 21 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_21_4_checked :
    (Witness.rising).check 25 21 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_21_5_checked :
    (Witness.rising).check 25 21 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_21_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2, 1] }

theorem case_25_21_6_checked :
    (Witness.linear .positive case_25_21_6).check 25 21 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_21_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2] }

theorem case_25_21_7_checked :
    (Witness.linear .positive case_25_21_7).check 25 21 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_21_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5] }

theorem case_25_21_8_checked :
    (Witness.linear .positive case_25_21_8).check 25 21 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_21_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_25_21_9_checked :
    (Witness.linear .positive case_25_21_9).check 25 21 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_21_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_25_21_10_checked :
    (Witness.linear .positive case_25_21_10).check 25 21 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_21_11 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 4862, 4862] }

theorem case_25_21_11_checked :
    (Witness.linear .negative case_25_21_11).check 25 21 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_21_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_25_21_12_checked :
    (Witness.linear .negative case_25_21_12).check 25 21 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_21_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_25_21_13_checked :
    (Witness.linear .negative case_25_21_13).check 25 21 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_22_1_checked :
    (Witness.rising).check 25 22 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_22_2_checked :
    (Witness.rising).check 25 22 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_22_3_checked :
    (Witness.rising).check 25 22 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_22_4_checked :
    (Witness.rising).check 25 22 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_22_5_checked :
    (Witness.rising).check 25 22 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_22_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5, 2] }

theorem case_25_22_6_checked :
    (Witness.linear .positive case_25_22_6).check 25 22 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_22_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5] }

theorem case_25_22_7_checked :
    (Witness.linear .positive case_25_22_7).check 25 22 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_22_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14] }

theorem case_25_22_8_checked :
    (Witness.linear .positive case_25_22_8).check 25 22 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_22_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_25_22_9_checked :
    (Witness.linear .positive case_25_22_9).check 25 22 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_22_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_25_22_10_checked :
    (Witness.linear .positive case_25_22_10).check 25 22 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_22_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_25_22_11_checked :
    (Witness.linear .positive case_25_22_11).check 25 22 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_22_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_25_22_12_checked :
    (Witness.linear .negative case_25_22_12).check 25 22 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_22_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_25_22_13_checked :
    (Witness.linear .negative case_25_22_13).check 25 22 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_22_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_25_22_14_checked :
    (Witness.linear .negative case_25_22_14).check 25 22 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_23_1_checked :
    (Witness.rising).check 25 23 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_23_2_checked :
    (Witness.rising).check 25 23 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_23_3_checked :
    (Witness.rising).check 25 23 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_23_4_checked :
    (Witness.rising).check 25 23 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_23_5_checked :
    (Witness.rising).check 25 23 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_23_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0, 5] }

theorem case_25_23_6_checked :
    (Witness.linear .positive case_25_23_6).check 25 23 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_23_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14] }

theorem case_25_23_7_checked :
    (Witness.linear .positive case_25_23_7).check 25 23 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_23_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_25_23_8_checked :
    (Witness.linear .positive case_25_23_8).check 25 23 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_23_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_25_23_9_checked :
    (Witness.linear .positive case_25_23_9).check 25 23 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_23_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_25_23_10_checked :
    (Witness.linear .positive case_25_23_10).check 25 23 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_23_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_25_23_11_checked :
    (Witness.linear .positive case_25_23_11).check 25 23 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_23_12 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_25_23_12_checked :
    (Witness.linear .negative case_25_23_12).check 25 23 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_23_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_25_23_13_checked :
    (Witness.linear .negative case_25_23_13).check 25 23 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_23_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_25_23_14_checked :
    (Witness.linear .negative case_25_23_14).check 25 23 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_24_1_checked :
    (Witness.rising).check 25 24 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_24_2_checked :
    (Witness.rising).check 25 24 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_24_3_checked :
    (Witness.rising).check 25 24 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_24_4_checked :
    (Witness.rising).check 25 24 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_25_24_5_checked :
    (Witness.rising).check 25 24 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_24_6 : Certificate := {
  objectiveScale := 1
  eta := 14
  rows := #[]
  caps := #[0, 0] }

theorem case_25_24_6_checked :
    (Witness.linear .positive case_25_24_6).check 25 24 6 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_24_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0] }

theorem case_25_24_7_checked :
    (Witness.linear .positive case_25_24_7).check 25 24 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_24_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_25_24_8_checked :
    (Witness.linear .positive case_25_24_8).check 25 24 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_24_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_25_24_9_checked :
    (Witness.linear .positive case_25_24_9).check 25 24 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_24_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_25_24_10_checked :
    (Witness.linear .positive case_25_24_10).check 25 24 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_24_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_25_24_11_checked :
    (Witness.linear .positive case_25_24_11).check 25 24 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_24_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_25_24_12_checked :
    (Witness.linear .positive case_25_24_12).check 25 24 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_24_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_25_24_13_checked :
    (Witness.linear .negative case_25_24_13).check 25 24 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_24_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_25_24_14_checked :
    (Witness.linear .negative case_25_24_14).check 25 24 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_25_24_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_25_24_15_checked :
    (Witness.linear .negative case_25_24_15).check 25 24 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_25 (a k : ℕ) (h : Domain 25 a k) :
    ∃ w : Witness, w.check 25 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 13 ≤ a := by omega
  have haHi : a ≤ 24 := by omega
  interval_cases a

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_25_13_1_checked⟩

    · exact ⟨Witness.rising, case_25_13_2_checked⟩

    · exact ⟨Witness.rising, case_25_13_3_checked⟩

    · exact ⟨Witness.rising, case_25_13_4_checked⟩

    · exact ⟨Witness.rising, case_25_13_5_checked⟩

    · exact ⟨Witness.rising, case_25_13_6_checked⟩

    · exact ⟨Witness.linear .positive case_25_13_7, case_25_13_7_checked⟩

    · exact ⟨Witness.linear .conditional case_25_13_8, case_25_13_8_checked⟩

  · have hkHi : k ≤ 8 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_25_14_1_checked⟩

    · exact ⟨Witness.rising, case_25_14_2_checked⟩

    · exact ⟨Witness.rising, case_25_14_3_checked⟩

    · exact ⟨Witness.rising, case_25_14_4_checked⟩

    · exact ⟨Witness.rising, case_25_14_5_checked⟩

    · exact ⟨Witness.rising, case_25_14_6_checked⟩

    · exact ⟨Witness.linear .positive case_25_14_7, case_25_14_7_checked⟩

    · exact ⟨Witness.linear .conditional case_25_14_8, case_25_14_8_checked⟩

  · have hkHi : k ≤ 9 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_25_15_1_checked⟩

    · exact ⟨Witness.rising, case_25_15_2_checked⟩

    · exact ⟨Witness.rising, case_25_15_3_checked⟩

    · exact ⟨Witness.rising, case_25_15_4_checked⟩

    · exact ⟨Witness.rising, case_25_15_5_checked⟩

    · exact ⟨Witness.rising, case_25_15_6_checked⟩

    · exact ⟨Witness.linear .positive case_25_15_7, case_25_15_7_checked⟩

    · exact ⟨Witness.linear .conditional case_25_15_8, case_25_15_8_checked⟩

    · exact ⟨Witness.linear .negative case_25_15_9, case_25_15_9_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_25_16_1_checked⟩

    · exact ⟨Witness.rising, case_25_16_2_checked⟩

    · exact ⟨Witness.rising, case_25_16_3_checked⟩

    · exact ⟨Witness.rising, case_25_16_4_checked⟩

    · exact ⟨Witness.rising, case_25_16_5_checked⟩

    · exact ⟨Witness.rising, case_25_16_6_checked⟩

    · exact ⟨Witness.linear .positive case_25_16_7, case_25_16_7_checked⟩

    · exact ⟨Witness.linear .positive case_25_16_8, case_25_16_8_checked⟩

    · exact ⟨Witness.linear .conditional case_25_16_9, case_25_16_9_checked⟩

    · exact ⟨Witness.linear .conditional case_25_16_10, case_25_16_10_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_25_17_1_checked⟩

    · exact ⟨Witness.rising, case_25_17_2_checked⟩

    · exact ⟨Witness.rising, case_25_17_3_checked⟩

    · exact ⟨Witness.rising, case_25_17_4_checked⟩

    · exact ⟨Witness.rising, case_25_17_5_checked⟩

    · exact ⟨Witness.linear .positive case_25_17_6, case_25_17_6_checked⟩

    · exact ⟨Witness.linear .positive case_25_17_7, case_25_17_7_checked⟩

    · exact ⟨Witness.linear .positive case_25_17_8, case_25_17_8_checked⟩

    · exact ⟨Witness.linear .conditional case_25_17_9, case_25_17_9_checked⟩

    · exact ⟨Witness.linear .conditional case_25_17_10, case_25_17_10_checked⟩

  · have hkHi : k ≤ 11 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_25_18_1_checked⟩

    · exact ⟨Witness.rising, case_25_18_2_checked⟩

    · exact ⟨Witness.rising, case_25_18_3_checked⟩

    · exact ⟨Witness.rising, case_25_18_4_checked⟩

    · exact ⟨Witness.rising, case_25_18_5_checked⟩

    · exact ⟨Witness.linear .positive case_25_18_6, case_25_18_6_checked⟩

    · exact ⟨Witness.linear .positive case_25_18_7, case_25_18_7_checked⟩

    · exact ⟨Witness.linear .positive case_25_18_8, case_25_18_8_checked⟩

    · exact ⟨Witness.linear .conditional case_25_18_9, case_25_18_9_checked⟩

    · exact ⟨Witness.linear .conditional case_25_18_10, case_25_18_10_checked⟩

    · exact ⟨Witness.linear .negative case_25_18_11, case_25_18_11_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_25_19_1_checked⟩

    · exact ⟨Witness.rising, case_25_19_2_checked⟩

    · exact ⟨Witness.rising, case_25_19_3_checked⟩

    · exact ⟨Witness.rising, case_25_19_4_checked⟩

    · exact ⟨Witness.rising, case_25_19_5_checked⟩

    · exact ⟨Witness.linear .positive case_25_19_6, case_25_19_6_checked⟩

    · exact ⟨Witness.linear .positive case_25_19_7, case_25_19_7_checked⟩

    · exact ⟨Witness.linear .positive case_25_19_8, case_25_19_8_checked⟩

    · exact ⟨Witness.linear .positive case_25_19_9, case_25_19_9_checked⟩

    · exact ⟨Witness.linear .conditional case_25_19_10, case_25_19_10_checked⟩

    · exact ⟨Witness.linear .negative case_25_19_11, case_25_19_11_checked⟩

    · exact ⟨Witness.linear .negative case_25_19_12, case_25_19_12_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_25_20_1_checked⟩

    · exact ⟨Witness.rising, case_25_20_2_checked⟩

    · exact ⟨Witness.rising, case_25_20_3_checked⟩

    · exact ⟨Witness.rising, case_25_20_4_checked⟩

    · exact ⟨Witness.rising, case_25_20_5_checked⟩

    · exact ⟨Witness.linear .positive case_25_20_6, case_25_20_6_checked⟩

    · exact ⟨Witness.linear .positive case_25_20_7, case_25_20_7_checked⟩

    · exact ⟨Witness.linear .positive case_25_20_8, case_25_20_8_checked⟩

    · exact ⟨Witness.linear .positive case_25_20_9, case_25_20_9_checked⟩

    · exact ⟨Witness.linear .positive case_25_20_10, case_25_20_10_checked⟩

    · exact ⟨Witness.linear .negative case_25_20_11, case_25_20_11_checked⟩

    · exact ⟨Witness.linear .negative case_25_20_12, case_25_20_12_checked⟩

  · have hkHi : k ≤ 13 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_25_21_1_checked⟩

    · exact ⟨Witness.rising, case_25_21_2_checked⟩

    · exact ⟨Witness.rising, case_25_21_3_checked⟩

    · exact ⟨Witness.rising, case_25_21_4_checked⟩

    · exact ⟨Witness.rising, case_25_21_5_checked⟩

    · exact ⟨Witness.linear .positive case_25_21_6, case_25_21_6_checked⟩

    · exact ⟨Witness.linear .positive case_25_21_7, case_25_21_7_checked⟩

    · exact ⟨Witness.linear .positive case_25_21_8, case_25_21_8_checked⟩

    · exact ⟨Witness.linear .positive case_25_21_9, case_25_21_9_checked⟩

    · exact ⟨Witness.linear .positive case_25_21_10, case_25_21_10_checked⟩

    · exact ⟨Witness.linear .negative case_25_21_11, case_25_21_11_checked⟩

    · exact ⟨Witness.linear .negative case_25_21_12, case_25_21_12_checked⟩

    · exact ⟨Witness.linear .negative case_25_21_13, case_25_21_13_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_25_22_1_checked⟩

    · exact ⟨Witness.rising, case_25_22_2_checked⟩

    · exact ⟨Witness.rising, case_25_22_3_checked⟩

    · exact ⟨Witness.rising, case_25_22_4_checked⟩

    · exact ⟨Witness.rising, case_25_22_5_checked⟩

    · exact ⟨Witness.linear .positive case_25_22_6, case_25_22_6_checked⟩

    · exact ⟨Witness.linear .positive case_25_22_7, case_25_22_7_checked⟩

    · exact ⟨Witness.linear .positive case_25_22_8, case_25_22_8_checked⟩

    · exact ⟨Witness.linear .positive case_25_22_9, case_25_22_9_checked⟩

    · exact ⟨Witness.linear .positive case_25_22_10, case_25_22_10_checked⟩

    · exact ⟨Witness.linear .positive case_25_22_11, case_25_22_11_checked⟩

    · exact ⟨Witness.linear .negative case_25_22_12, case_25_22_12_checked⟩

    · exact ⟨Witness.linear .negative case_25_22_13, case_25_22_13_checked⟩

    · exact ⟨Witness.linear .negative case_25_22_14, case_25_22_14_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_25_23_1_checked⟩

    · exact ⟨Witness.rising, case_25_23_2_checked⟩

    · exact ⟨Witness.rising, case_25_23_3_checked⟩

    · exact ⟨Witness.rising, case_25_23_4_checked⟩

    · exact ⟨Witness.rising, case_25_23_5_checked⟩

    · exact ⟨Witness.linear .positive case_25_23_6, case_25_23_6_checked⟩

    · exact ⟨Witness.linear .positive case_25_23_7, case_25_23_7_checked⟩

    · exact ⟨Witness.linear .positive case_25_23_8, case_25_23_8_checked⟩

    · exact ⟨Witness.linear .positive case_25_23_9, case_25_23_9_checked⟩

    · exact ⟨Witness.linear .positive case_25_23_10, case_25_23_10_checked⟩

    · exact ⟨Witness.linear .positive case_25_23_11, case_25_23_11_checked⟩

    · exact ⟨Witness.linear .negative case_25_23_12, case_25_23_12_checked⟩

    · exact ⟨Witness.linear .negative case_25_23_13, case_25_23_13_checked⟩

    · exact ⟨Witness.linear .negative case_25_23_14, case_25_23_14_checked⟩

  · have hkHi : k ≤ 15 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_25_24_1_checked⟩

    · exact ⟨Witness.rising, case_25_24_2_checked⟩

    · exact ⟨Witness.rising, case_25_24_3_checked⟩

    · exact ⟨Witness.rising, case_25_24_4_checked⟩

    · exact ⟨Witness.rising, case_25_24_5_checked⟩

    · exact ⟨Witness.linear .positive case_25_24_6, case_25_24_6_checked⟩

    · exact ⟨Witness.linear .positive case_25_24_7, case_25_24_7_checked⟩

    · exact ⟨Witness.linear .positive case_25_24_8, case_25_24_8_checked⟩

    · exact ⟨Witness.linear .positive case_25_24_9, case_25_24_9_checked⟩

    · exact ⟨Witness.linear .positive case_25_24_10, case_25_24_10_checked⟩

    · exact ⟨Witness.linear .positive case_25_24_11, case_25_24_11_checked⟩

    · exact ⟨Witness.linear .positive case_25_24_12, case_25_24_12_checked⟩

    · exact ⟨Witness.linear .negative case_25_24_13, case_25_24_13_checked⟩

    · exact ⟨Witness.linear .negative case_25_24_14, case_25_24_14_checked⟩

    · exact ⟨Witness.linear .negative case_25_24_15, case_25_24_15_checked⟩


#print axioms coverage_25
end ForestUnimodality.FiniteRows.FiniteData
