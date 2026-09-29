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

theorem case_32_16_1_checked :
    (Witness.rising).check 32 16 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_16_2_checked :
    (Witness.rising).check 32 16 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_16_3_checked :
    (Witness.rising).check 32 16 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_16_4_checked :
    (Witness.rising).check 32 16 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_16_5_checked :
    (Witness.rising).check 32 16 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_16_6_checked :
    (Witness.rising).check 32 16 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_16_7_checked :
    (Witness.rising).check 32 16 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_16_8 : Certificate := {
  objectiveScale := 8705088000
  eta := 0
  rows := #[⟨.count 2, 697103447040⟩, ⟨.count 3, 459808188840⟩, ⟨.count 4, 91925729280⟩, ⟨.count 5, 24936450000⟩, ⟨.count 6, 10065258000⟩, ⟨.count 7, 8721410040⟩, ⟨.path 8, 1340859520⟩, ⟨.path 9, 2141209840⟩, ⟨.privateRow 9 0, 267651230⟩, ⟨.hall 7 1, 362863130⟩, ⟨.hall 0 2, 69762212520⟩, ⟨.hall 1 3, 2698123890⟩, ⟨.hall 6 3, 64316610⟩, ⟨.hall 7 3, 8236585⟩, ⟨.hall 0 4, 12727564080⟩, ⟨.hall 6 4, 3670300⟩, ⟨.hall 9 4, 142908528⟩, ⟨.hall 10 4, 714542640⟩, ⟨.hall 11 4, 7859969040⟩, ⟨.hall 5 5, 40481250⟩, ⟨.hall 4 9, 209284824⟩, ⟨.hall 3 12, 2992374000⟩]
  caps := #[0, 0, 317957640, 0, 0, 5636400, 0, 11188800, 0, 16926560, 0, 0, 0, 0, 0, 0, 0] }

theorem case_32_16_8_checked :
    (Witness.linear .positive case_32_16_8).check 32 16 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_16_9 : Certificate := {
  objectiveScale := 8400000
  eta := 302702400
  rows := #[⟨.count 2, 549909360⟩, ⟨.count 3, 889728840⟩, ⟨.count 4, 199584000⟩, ⟨.count 5, 55024200⟩, ⟨.count 6, 18824400⟩, ⟨.count 7, 8414280⟩, ⟨.count 8, 8420160⟩, ⟨.path 10, 2049300⟩, ⟨.path 11, 759000⟩, ⟨.privateRow 10 0, 292680⟩, ⟨.privateRow 11 0, 126000⟩, ⟨.hall 8 1, 189000⟩, ⟨.hall 8 2, 128800⟩, ⟨.hall 1 3, 2231460⟩, ⟨.hall 7 3, 68460⟩, ⟨.hall 0 4, 28302120⟩, ⟨.hall 1 4, 947520⟩, ⟨.hall 7 4, 61152⟩, ⟨.hall 6 5, 119700⟩, ⟨.hall 5 7, 171675⟩, ⟨.hall 4 10, 1512000⟩]
  caps := #[0, 17131800, 0, 221760, 0, 30600, 24900, 15120, 0, 0, 540, 3000, 0, 0, 0, 0, 0] }

theorem case_32_16_9_checked :
    (Witness.linear .positive case_32_16_9).check 32 16 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_16_10 : Certificate := {
  objectiveScale := 6300000
  eta := 1078377300
  rows := #[⟨.count 2, 1003962960⟩, ⟨.count 3, 278378100⟩, ⟨.count 4, 94469760⟩, ⟨.count 5, 35204400⟩, ⟨.count 6, 14515200⟩, ⟨.count 7, 8043840⟩, ⟨.count 8, 6468000⟩, ⟨.count 9, 6482700⟩, ⟨.count 11, 6306300⟩, ⟨.path 9, 1405950⟩, ⟨.hall 9 1, 251370⟩, ⟨.hall 8 2, 11900⟩, ⟨.hall 9 2, 75852⟩, ⟨.hall 8 3, 219072⟩, ⟨.hall 0 4, 1898820⟩, ⟨.hall 7 4, 255738⟩, ⟨.hall 6 6, 382950⟩, ⟨.hall 5 7, 395325⟩, ⟨.hall 4 9, 1025640⟩, ⟨.hall 3 12, 48898080⟩, ⟨.hall 2 13, 22342320⟩, ⟨.assumptionRow 10, 5064780⟩]
  caps := #[0, 7057050, 540540, 221760, 221760, 0, 12600, 3570, 10080, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_32_16_10_checked :
    (Witness.linear .conditional case_32_16_10).check 32 16 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_17_1_checked :
    (Witness.rising).check 32 17 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_17_2_checked :
    (Witness.rising).check 32 17 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_17_3_checked :
    (Witness.rising).check 32 17 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_17_4_checked :
    (Witness.rising).check 32 17 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_17_5_checked :
    (Witness.rising).check 32 17 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_17_6_checked :
    (Witness.rising).check 32 17 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_17_7_checked :
    (Witness.rising).check 32 17 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_17_8 : Certificate := {
  objectiveScale := 2131446240000
  eta := 3136999272078672
  rows := #[⟨.count 2, 695393927308080⟩, ⟨.count 3, 112470023746080⟩, ⟨.count 4, 23042639011392⟩, ⟨.count 5, 6234480252000⟩, ⟨.count 6, 2493792100800⟩, ⟨.count 7, 2133577686240⟩, ⟨.path 8, 366085255536⟩, ⟨.path 9, 486467080176⟩, ⟨.privateRow 5 8, 465507858816⟩, ⟨.privateRow 6 4, 11949420483⟩, ⟨.privateRow 6 5, 201284648136⟩, ⟨.privateRow 6 6, 229983049296⟩, ⟨.privateRow 7 2, 105293444256⟩, ⟨.privateRow 7 3, 96288083892⟩, ⟨.privateRow 8 0, 82433683332⟩, ⟨.privateRow 9 0, 54186099968⟩, ⟨.hall 9 2, 20633160834⟩, ⟨.hall 5 10, 68642257320⟩, ⟨.hall 4 11, 249112779300⟩, ⟨.hall 3 12, 287882263944⟩]
  caps := #[0, 0, 123065102160, 110185403328, 0, 45967832064, 3739394736, 13841466408, 8908151868, 0, 0, 0, 0, 0, 0, 0] }

theorem case_32_17_8_checked :
    (Witness.linear .positive case_32_17_8).check 32 17 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_17_9 : Certificate := {
  objectiveScale := 15120000
  eta := 28802133360
  rows := #[⟨.count 2, 6754587840⟩, ⟨.count 3, 1495632600⟩, ⟨.count 4, 370477800⟩, ⟨.count 5, 101871000⟩, ⟨.count 6, 34677720⟩, ⟨.count 7, 15135120⟩, ⟨.count 8, 15135120⟩, ⟨.path 10, 4410000⟩, ⟨.privateRow 9 0, 12320⟩, ⟨.privateRow 10 0, 550935⟩, ⟨.privateRow 10 5, 152460⟩, ⟨.privateRow 10 6, 1871100⟩, ⟨.privateRow 11 0, 427680⟩, ⟨.privateRow 11 1, 1122660⟩, ⟨.hall 8 2, 344960⟩, ⟨.hall 9 2, 93555⟩, ⟨.hall 7 3, 155001⟩, ⟨.hall 6 5, 69660⟩, ⟨.hall 10 5, 702900⟩, ⟨.hall 5 7, 193725⟩, ⟨.hall 7 7, 21560⟩]
  caps := #[0, 26666640, 2162160, 1247400, 0, 189000, 0, 0, 1008, 0, 33705, 0, 0, 0, 0, 0] }

theorem case_32_17_9_checked :
    (Witness.linear .positive case_32_17_9).check 32 17 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_17_10 : Certificate := {
  objectiveScale := 3148727400000
  eta := 4021793938562400
  rows := #[⟨.count 2, 1034175584201760⟩, ⟨.count 3, 290776158953280⟩, ⟨.count 4, 86867091511200⟩, ⟨.count 5, 28678609159200⟩, ⟨.count 6, 11055811646880⟩, ⟨.count 7, 5366271150240⟩, ⟨.count 8, 3782251352880⟩, ⟨.count 9, 2867860915920⟩, ⟨.count 11, 3200366529360⟩, ⟨.path 8, 939906087120⟩, ⟨.privateRow 6 7, 2434218178392⟩, ⟨.privateRow 7 5, 1226884138480⟩, ⟨.privateRow 7 6, 2829992221056⟩, ⟨.privateRow 8 3, 164521006650⟩, ⟨.privateRow 8 4, 2643400384625⟩, ⟨.privateRow 9 1, 449690751510⟩, ⟨.privateRow 9 2, 404416549680⟩, ⟨.privateRow 10 0, 225999909135⟩, ⟨.hall 6 8, 200007164448⟩, ⟨.hall 5 9, 759473048880⟩, ⟨.hall 4 10, 1123982650560⟩, ⟨.hall 6 10, 2950987319280⟩, ⟨.hall 3 12, 6305274716400⟩, ⟨.hall 2 14, 55473019842240⟩, ⟨.assumptionRow 10, 2847849004000⟩]
  caps := #[0, 0, 0, 0, 31818433920, 6516619200, 0, 29203823376, 5503738240, 0, 0, 0, 0, 0, 0, 0] }

theorem case_32_17_10_checked :
    (Witness.linear .conditional case_32_17_10).check 32 17 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_18_1_checked :
    (Witness.rising).check 32 18 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_18_2_checked :
    (Witness.rising).check 32 18 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_18_3_checked :
    (Witness.rising).check 32 18 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_18_4_checked :
    (Witness.rising).check 32 18 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_18_5_checked :
    (Witness.rising).check 32 18 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_18_6_checked :
    (Witness.rising).check 32 18 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_18_7_checked :
    (Witness.rising).check 32 18 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_18_8 : Certificate := {
  objectiveScale := 950400000
  eta := 1679513996160
  rows := #[⟨.count 2, 296345649600⟩, ⟨.count 3, 50112382320⟩, ⟨.count 4, 10412962560⟩, ⟨.count 5, 2784862080⟩, ⟨.count 6, 1130088960⟩, ⟨.count 7, 953512560⟩, ⟨.path 8, 172806480⟩, ⟨.path 9, 207355680⟩, ⟨.privateRow 4 11, 355675320⟩, ⟨.privateRow 5 9, 774918144⟩, ⟨.privateRow 5 10, 31783752⟩, ⟨.privateRow 5 11, 26234208⟩, ⟨.privateRow 6 7, 372772400⟩, ⟨.privateRow 7 4, 84819735⟩, ⟨.privateRow 7 7, 38342304⟩, ⟨.privateRow 8 3, 37207170⟩, ⟨.privateRow 8 5, 10090080⟩, ⟨.privateRow 9 0, 20852832⟩, ⟨.hall 9 1, 32960928⟩, ⟨.hall 10 3, 11891880⟩, ⟨.hall 11 3, 42810768⟩, ⟨.hall 3 12, 25247376⟩, ⟨.hall 4 12, 3991680⟩]
  caps := #[0, 814207680, 183783600, 69735600, 4540536, 14519520, 0, 2392434, 12631230, 0, 26906880, 0, 0, 0, 0] }

theorem case_32_18_8_checked :
    (Witness.linear .positive case_32_18_8).check 32 18 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_18_9 : Certificate := {
  objectiveScale := 32400000
  eta := 81162081000
  rows := #[⟨.count 2, 16838902080⟩, ⟨.count 3, 3888644760⟩, ⟨.count 4, 947026080⟩, ⟨.count 5, 248107860⟩, ⟨.count 6, 83243160⟩, ⟨.count 7, 34999965⟩, ⟨.count 8, 32432400⟩, ⟨.path 9, 2945160⟩, ⟨.path 10, 6873120⟩, ⟨.privateRow 9 1, 640640⟩, ⟨.privateRow 10 0, 756756⟩, ⟨.hall 8 3, 30030⟩, ⟨.hall 7 4, 41769⟩]
  caps := #[0, 0, 9729720, 0, 1406160, 0, 210600, 345195, 753840, 0, 62316, 0, 0, 0, 0] }

theorem case_32_18_9_checked :
    (Witness.linear .positive case_32_18_9).check 32 18 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_18_10 : Certificate := {
  objectiveScale := 728000000
  eta := 1715998284000
  rows := #[⟨.count 2, 419545526400⟩, ⟨.count 3, 108275567400⟩, ⟨.count 4, 32043211200⟩, ⟨.count 5, 10248638400⟩, ⟨.count 6, 3718915200⟩, ⟨.count 7, 1645944300⟩, ⟨.count 8, 1059458400⟩, ⟨.count 9, 616215600⟩, ⟨.count 11, 713512800⟩, ⟨.path 8, 270210600⟩, ⟨.privateRow 4 11, 632431800⟩, ⟨.privateRow 4 12, 5367562200⟩, ⟨.privateRow 5 9, 851026176⟩, ⟨.privateRow 5 10, 2450267820⟩, ⟨.privateRow 5 11, 4402157760⟩, ⟨.privateRow 6 7, 596395800⟩, ⟨.privateRow 6 8, 1011890880⟩, ⟨.privateRow 6 9, 2724321600⟩, ⟨.privateRow 6 10, 1262461200⟩, ⟨.privateRow 7 5, 360617400⟩, ⟨.privateRow 7 6, 754954200⟩, ⟨.privateRow 7 7, 1027026000⟩, ⟨.privateRow 8 3, 220945725⟩, ⟨.privateRow 8 4, 481852800⟩, ⟨.privateRow 8 5, 33333300⟩, ⟨.privateRow 9 1, 158158000⟩, ⟨.privateRow 9 2, 56306250⟩, ⟨.privateRow 10 0, 53333280⟩, ⟨.hall 4 13, 6945166800⟩, ⟨.hall 3 14, 19550250720⟩, ⟨.hall 2 15, 26221595400⟩, ⟨.assumptionRow 10, 785011500⟩]
  caps := #[0, 0, 240039800, 145945800, 81501420, 6893600, 6590100, 10200300, 7222875, 10637900, 0, 14487200, 0, 0, 0] }

theorem case_32_18_10_checked :
    (Witness.linear .conditional case_32_18_10).check 32 18 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_18_11 : Certificate := {
  objectiveScale := 1155092400000
  eta := 3487242437078400
  rows := #[⟨.count 2, 841087461614400⟩, ⟨.count 3, 202178132956800⟩, ⟨.count 4, 55740138854400⟩, ⟨.count 5, 15857108467200⟩, ⟨.count 6, 4624989969600⟩, ⟨.count 7, 1261360900800⟩, ⟨.count 8, 480518438400⟩, ⟨.count 9, 510550840800⟩, ⟨.count 10, 540583243200⟩, ⟨.count 12, 1321425705600⟩, ⟨.path 7, 736509866400⟩, ⟨.privateRow 4 11, 7508100600⟩, ⟨.privateRow 4 12, 10180984413600⟩, ⟨.privateRow 5 9, 699154327872⟩, ⟨.privateRow 5 10, 4189520134800⟩, ⟨.privateRow 5 11, 9362100908160⟩, ⟨.privateRow 6 7, 488860772400⟩, ⟨.privateRow 6 8, 1948101835680⟩, ⟨.privateRow 6 9, 4389736150800⟩, ⟨.privateRow 6 10, 5477020348800⟩, ⟨.privateRow 7 5, 219880089000⟩, ⟨.privateRow 7 6, 966459393900⟩, ⟨.privateRow 7 7, 2265944761080⟩, ⟨.privateRow 7 8, 2868720104250⟩, ⟨.privateRow 8 3, 47238466275⟩, ⟨.privateRow 8 4, 487311481800⟩, ⟨.privateRow 8 5, 1307660854500⟩, ⟨.privateRow 8 6, 739798179120⟩, ⟨.privateRow 9 2, 160589929500⟩, ⟨.privateRow 9 3, 776075414400⟩, ⟨.privateRow 10 1, 303327264240⟩, ⟨.privateRow 11 0, 82589106600⟩, ⟨.hall 5 12, 4028962291200⟩, ⟨.hall 4 13, 21022681680000⟩, ⟨.hall 3 14, 44675200730160⟩, ⟨.hall 2 15, 52567966350900⟩, ⟨.assumptionRow 11, 522516612800⟩]
  caps := #[0, 0, 196927931200, 102656654100, 19992537600, 0, 805912800, 2697427675, 0, 11965772000, 10264117360, 0, 0, 0, 0] }

theorem case_32_18_11_checked :
    (Witness.linear .conditional case_32_18_11).check 32 18 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_19_1_checked :
    (Witness.rising).check 32 19 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_19_2_checked :
    (Witness.rising).check 32 19 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_19_3_checked :
    (Witness.rising).check 32 19 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_19_4_checked :
    (Witness.rising).check 32 19 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_19_5_checked :
    (Witness.rising).check 32 19 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_19_6_checked :
    (Witness.rising).check 32 19 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_19_7_checked :
    (Witness.rising).check 32 19 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_19_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_32_19_8_checked :
    (Witness.linear .positive case_32_19_8).check 32 19 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_19_9 : Certificate := {
  objectiveScale := 880000
  eta := 2854051200
  rows := #[⟨.count 2, 628948320⟩, ⟨.count 3, 154954800⟩, ⟨.count 4, 36900864⟩, ⟨.count 5, 10250240⟩, ⟨.count 6, 2942940⟩, ⟨.count 7, 1201200⟩, ⟨.count 8, 880880⟩, ⟨.path 9, 293355⟩, ⟨.hall 8 7, 4914⟩, ⟨.hall 5 9, 27696⟩]
  caps := #[0, 0, 391105, 0, 64596, 75075, 0, 0, 32505, 0, 0, 0, 0, 0] }

theorem case_32_19_9_checked :
    (Witness.linear .positive case_32_19_9).check 32 19 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_19_10 : Certificate := {
  objectiveScale := 8568000000
  eta := 37784070324000
  rows := #[⟨.count 2, 8207775576000⟩, ⟨.count 3, 2076387112800⟩, ⟨.count 4, 544955130720⟩, ⟨.count 5, 169816046400⟩, ⟨.count 6, 59178319200⟩, ⟨.count 7, 24443218800⟩, ⟨.count 8, 14580165600⟩, ⟨.count 9, 4631346720⟩, ⟨.path 8, 4086534375⟩, ⟨.privateRow 2 17, 42454011600⟩, ⟨.privateRow 3 15, 230280850800⟩, ⟨.privateRow 4 12, 49401031680⟩, ⟨.privateRow 4 13, 108965296440⟩, ⟨.privateRow 5 9, 1829667840⟩, ⟨.privateRow 5 10, 38148574464⟩, ⟨.privateRow 5 11, 55619043480⟩, ⟨.privateRow 5 12, 78218300160⟩, ⟨.privateRow 6 7, 4732427700⟩, ⟨.privateRow 6 8, 20029859850⟩, ⟨.privateRow 6 9, 31990598640⟩, ⟨.privateRow 6 10, 27686233575⟩, ⟨.privateRow 7 5, 4548644100⟩, ⟨.privateRow 7 6, 11801532600⟩, ⟨.privateRow 7 7, 15070255200⟩, ⟨.privateRow 8 3, 3692689000⟩, ⟨.privateRow 8 4, 6566434875⟩, ⟨.privateRow 9 1, 2898879984⟩, ⟨.privateRow 10 0, 926269344⟩, ⟨.privateRow 11 0, 1000599600⟩, ⟨.hall 4 14, 34580722176⟩, ⟨.hall 3 15, 271367971875⟩, ⟨.hall 2 16, 215599784400⟩, ⟨.assumptionRow 10, 10502654400⟩]
  caps := #[0, 53726072400, 0, 1802493000, 0, 1225019796, 0, 553202100, 502001500, 73547712, 767024496, 0, 0, 0] }

theorem case_32_19_10_checked :
    (Witness.linear .conditional case_32_19_10).check 32 19 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_19_11 : Certificate := {
  objectiveScale := 16680468000000
  eta := 52424275575672000
  rows := #[⟨.count 2, 13019482252576800⟩, ⟨.count 3, 3263099872032000⟩, ⟨.count 4, 856993071654720⟩, ⟨.count 5, 247117797326400⟩, ⟨.count 6, 72990391874400⟩, ⟨.count 7, 20036578161600⟩, ⟨.count 8, 9541227696000⟩, ⟨.count 9, 10304525911680⟩, ⟨.path 7, 9804855060000⟩, ⟨.privateRow 2 17, 1700246775427200⟩, ⟨.privateRow 3 14, 232328894397600⟩, ⟨.privateRow 3 15, 649042014020400⟩, ⟨.privateRow 4 12, 169809999919560⟩, ⟨.privateRow 4 13, 311855027243760⟩, ⟨.privateRow 5 9, 2671543754880⟩, ⟨.privateRow 5 10, 86901501855168⟩, ⟨.privateRow 5 11, 151753226504880⟩, ⟨.privateRow 5 12, 239866464277440⟩, ⟨.privateRow 5 13, 57915252114720⟩, ⟨.privateRow 6 7, 3629074105800⟩, ⟨.privateRow 6 8, 39496707149900⟩, ⟨.privateRow 6 9, 78214214037960⟩, ⟨.privateRow 6 10, 127584104097450⟩, ⟨.privateRow 6 11, 44406463901800⟩, ⟨.privateRow 7 5, 1967878212300⟩, ⟨.privateRow 7 6, 19116531205200⟩, ⟨.privateRow 7 7, 41691757450200⟩, ⟨.privateRow 7 8, 59312360455920⟩, ⟨.privateRow 8 3, 79510230800⟩, ⟨.privateRow 8 4, 10063013585625⟩, ⟨.privateRow 8 5, 24858305729400⟩, ⟨.privateRow 8 6, 12224697985500⟩, ⟨.privateRow 9 2, 3434841970560⟩, ⟨.privateRow 9 3, 12737538974160⟩, ⟨.privateRow 10 0, 987517066536⟩, ⟨.privateRow 10 1, 3816491078400⟩, ⟨.privateRow 11 0, 1272163692800⟩, ⟨.hall 4 14, 154567888675200⟩, ⟨.hall 3 15, 881251643071800⟩, ⟨.hall 2 16, 777890681568000⟩, ⟨.assumptionRow 11, 10085487537600⟩]
  caps := #[0, 0, 22198077501600, 0, 345519190080, 251515616352, 0, 447898876920, 385239380000, 296187921504, 5037324999624, 0, 16680468000000, 0] }

theorem case_32_19_11_checked :
    (Witness.linear .conditional case_32_19_11).check 32 19 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_19_12 : Certificate := {
  objectiveScale := 21591360000
  eta := 76417220880000
  rows := #[⟨.count 2, 18679765104000⟩, ⟨.count 3, 5225702882400⟩, ⟨.count 4, 1512906595200⟩, ⟨.count 5, 452842790400⟩, ⟨.count 6, 140226886800⟩, ⟨.count 7, 43740496800⟩, ⟨.count 8, 10291881600⟩, ⟨.path 8, 10795519350⟩, ⟨.privateRow 4 12, 54611296740⟩, ⟨.privateRow 4 13, 347608301040⟩, ⟨.privateRow 5 10, 42059489472⟩, ⟨.privateRow 5 11, 174104330400⟩, ⟨.privateRow 5 12, 362846003520⟩, ⟨.privateRow 6 8, 21441420000⟩, ⟨.privateRow 6 10, 349012714050⟩, ⟨.privateRow 6 11, 152091139200⟩, ⟨.privateRow 7 6, 5749801200⟩, ⟨.privateRow 7 7, 45425179800⟩, ⟨.privateRow 7 8, 38153475360⟩, ⟨.privateRow 7 9, 147853906200⟩, ⟨.privateRow 7 10, 62731468800⟩, ⟨.privateRow 8 4, 2760582825⟩, ⟨.privateRow 8 5, 15590975400⟩, ⟨.privateRow 8 8, 144193549500⟩, ⟨.privateRow 9 2, 533653120⟩, ⟨.privateRow 9 4, 45725359680⟩, ⟨.privateRow 9 6, 1989763776⟩, ⟨.privateRow 10 0, 154378224⟩, ⟨.privateRow 10 1, 943422480⟩, ⟨.privateRow 11 0, 3716512800⟩, ⟨.privateRow 12 0, 1768917150⟩, ⟨.hall 9 3, 1344377034⟩, ⟨.hall 10 3, 61261200⟩, ⟨.hall 10 8, 6861254400⟩, ⟨.hall 5 11, 879648000⟩, ⟨.hall 3 13, 15607822230⟩, ⟨.hall 4 13, 48033681696⟩, ⟨.hall 2 16, 2220927508800⟩]
  caps := #[0, 0, 0, 0, 0, 566773200, 114543450, 1082707560, 503637750, 1188994688, 0, 16149537600, 0, 21591360000] }

theorem case_32_19_12_checked :
    (Witness.linear .negative case_32_19_12).check 32 19 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_20_1_checked :
    (Witness.rising).check 32 20 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_20_2_checked :
    (Witness.rising).check 32 20 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_20_3_checked :
    (Witness.rising).check 32 20 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_20_4_checked :
    (Witness.rising).check 32 20 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_20_5_checked :
    (Witness.rising).check 32 20 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_20_6_checked :
    (Witness.rising).check 32 20 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_20_7_checked :
    (Witness.rising).check 32 20 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_20_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_32_20_8_checked :
    (Witness.linear .positive case_32_20_8).check 32 20 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_20_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_32_20_9_checked :
    (Witness.linear .positive case_32_20_9).check 32 20 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_20_10 : Certificate := {
  objectiveScale := 7250598600000
  eta := 50604835119438600
  rows := #[⟨.count 2, 10451302845984000⟩, ⟨.count 3, 2441125736169120⟩, ⟨.count 4, 604682521803360⟩, ⟨.count 5, 167967367167600⟩, ⟨.count 6, 49323750676200⟩, ⟨.count 7, 17107787396700⟩, ⟨.count 8, 9953621758080⟩, ⟨.path 7, 6934862794860⟩, ⟨.privateRow 2 18, 970478121412800⟩, ⟨.privateRow 3 15, 315405389459160⟩, ⟨.privateRow 3 16, 387258096525300⟩, ⟨.privateRow 4 12, 66316004963208⟩, ⟨.privateRow 4 13, 169056044547390⟩, ⟨.privateRow 4 14, 190155649003320⟩, ⟨.privateRow 4 15, 190985117483160⟩, ⟨.privateRow 5 9, 6843114958680⟩, ⟨.privateRow 5 10, 55107812129370⟩, ⟨.privateRow 5 11, 81992959232184⟩, ⟨.privateRow 5 12, 95103745391655⟩, ⟨.privateRow 5 13, 25298788635120⟩, ⟨.privateRow 6 7, 10497960447975⟩, ⟨.privateRow 6 8, 33390338295600⟩, ⟨.privateRow 6 9, 47250079476600⟩, ⟨.privateRow 6 10, 9642571078140⟩, ⟨.privateRow 7 5, 10146176940900⟩, ⟨.privateRow 7 6, 21995726652900⟩, ⟨.privateRow 7 7, 2539189224000⟩, ⟨.privateRow 8 3, 8989364650266⟩, ⟨.privateRow 8 4, 1624375773020⟩, ⟨.privateRow 9 1, 2940842792160⟩, ⟨.privateRow 10 6, 373260815928⟩, ⟨.privateRow 11 0, 933152039820⟩, ⟨.hall 9 1, 508992021720⟩, ⟨.hall 3 16, 1646738893800⟩, ⟨.hall 2 17, 270614091547800⟩, ⟨.assumptionRow 10, 8824952148012⟩]
  caps := #[0, 3225288234168, 9932179929672, 7651157129616, 653741202114, 0, 1781833395771, 233476322814, 0, 2423771532, 8890580423340, 0, 0] }

theorem case_32_20_10_checked :
    (Witness.linear .conditional case_32_20_10).check 32 20 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_20_11 : Certificate := {
  objectiveScale := 36200014200000
  eta := 329356127594894400
  rows := #[⟨.count 2, 65535781707396000⟩, ⟨.count 3, 13958189715309840⟩, ⟨.count 4, 2915462263633920⟩, ⟨.count 5, 657428457886200⟩, ⟨.count 6, 137549711098800⟩, ⟨.count 7, 25883010153000⟩, ⟨.count 8, 16565126497920⟩, ⟨.path 5, 4754849299200⟩, ⟨.path 6, 72594372872736⟩, ⟨.privateRow 2 18, 6802055068208400⟩, ⟨.privateRow 3 15, 1824234555583440⟩, ⟨.privateRow 3 16, 2689762415099760⟩, ⟨.privateRow 4 12, 279122381489952⟩, ⟨.privateRow 4 13, 1013061017388420⟩, ⟨.privateRow 4 14, 1322449265417280⟩, ⟨.privateRow 4 15, 1579898939739120⟩, ⟨.privateRow 5 10, 250720091682060⟩, ⟨.privateRow 5 11, 477489771302544⟩, ⟨.privateRow 5 12, 668299322150460⟩, ⟨.privateRow 5 13, 713335759816680⟩, ⟨.privateRow 6 7, 10630522027125⟩, ⟨.privateRow 6 8, 143994052402200⟩, ⟨.privateRow 6 9, 263636946272700⟩, ⟨.privateRow 6 10, 358812472178160⟩, ⟨.privateRow 6 11, 109078399930500⟩, ⟨.privateRow 7 5, 8052492047600⟩, ⟨.privateRow 7 6, 81716360625900⟩, ⟨.privateRow 7 7, 167552873888400⟩, ⟨.privateRow 7 8, 88002234520200⟩, ⟨.privateRow 8 3, 1760044690404⟩, ⟨.privateRow 8 4, 51996091507360⟩, ⟨.privateRow 8 5, 70790032768455⟩, ⟨.privateRow 9 2, 31680804427272⟩, ⟨.privateRow 9 3, 8282563248960⟩, ⟨.privateRow 10 0, 10729684208880⟩, ⟨.privateRow 11 0, 3105961218360⟩, ⟨.hall 3 16, 337636254795840⟩, ⟨.hall 2 17, 2153466444729600⟩, ⟨.assumptionRow 11, 25702010082000⟩]
  caps := #[0, 134501590143648, 6463767229920, 15210646616880, 1496753700156, 0, 5628686910561, 0, 3856749512868, 2739617074656, 14103525532320, 0, 36200014200000] }

theorem case_32_20_11_checked :
    (Witness.linear .conditional case_32_20_11).check 32 20 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_20_12 : Certificate := {
  objectiveScale := 95823567000000
  eta := 1719382481453637000
  rows := #[⟨.count 2, 294134527378692000⟩, ⟨.count 3, 50689287083635200⟩, ⟨.count 4, 8323976065204800⟩, ⟨.count 5, 1061203416273000⟩, ⟨.count 6, 22185437274000⟩, ⟨.path 5, 899830465033500⟩, ⟨.path 6, 27651204595872⟩, ⟨.privateRow 2 18, 29506631574420000⟩, ⟨.privateRow 3 14, 396010055340900⟩, ⟨.privateRow 3 15, 8080675769766600⟩, ⟨.privateRow 3 16, 11134870967820600⟩, ⟨.privateRow 4 12, 1614064513141080⟩, ⟨.privateRow 4 13, 3922570188687150⟩, ⟨.privateRow 4 14, 5324997955477200⟩, ⟨.privateRow 4 15, 6701111328611700⟩, ⟨.privateRow 5 9, 179702041919400⟩, ⟨.privateRow 5 10, 974926715763000⟩, ⟨.privateRow 5 11, 1766774273043780⟩, ⟨.privateRow 5 12, 2558535553624050⟩, ⟨.privateRow 5 13, 3550286225986500⟩, ⟨.privateRow 6 6, 9654773628500⟩, ⟨.privateRow 6 7, 145591932110625⟩, ⟨.privateRow 6 8, 496002990483000⟩, ⟨.privateRow 6 9, 914224894332750⟩, ⟨.privateRow 6 10, 1332235508303700⟩, ⟨.privateRow 6 11, 1059816826443375⟩, ⟨.privateRow 7 4, 6470752538250⟩, ⟨.privateRow 7 5, 90385114820000⟩, ⟨.privateRow 7 6, 277780162534875⟩, ⟨.privateRow 7 7, 544071437910000⟩, ⟨.privateRow 7 8, 675115181490750⟩, ⟨.privateRow 8 2, 5176602030600⟩, ⟨.privateRow 8 3, 56683792235070⟩, ⟨.privateRow 8 4, 184344550089700⟩, ⟨.privateRow 8 5, 365597518411125⟩, ⟨.privateRow 9 0, 5176602030600⟩, ⟨.privateRow 9 1, 46589418275400⟩, ⟨.privateRow 9 2, 149086138481280⟩, ⟨.privateRow 9 3, 18405696108800⟩, ⟨.privateRow 10 0, 76237229905200⟩, ⟨.privateRow 11 0, 23294709137700⟩, ⟨.hall 3 16, 1773138448481400⟩, ⟨.hall 2 17, 9300628314978000⟩]
  caps := #[0, 393764106304296, 44142332242320, 32510083904298, 18928669732830, 8665094080500, 6633488784997, 0, 5385396851065, 740704342840, 0, 257765395230000, 670764969000000] }

theorem case_32_20_12_checked :
    (Witness.linear .negative case_32_20_12).check 32 20 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_21_1_checked :
    (Witness.rising).check 32 21 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_21_2_checked :
    (Witness.rising).check 32 21 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_21_3_checked :
    (Witness.rising).check 32 21 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_21_4_checked :
    (Witness.rising).check 32 21 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_21_5_checked :
    (Witness.rising).check 32 21 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_21_6_checked :
    (Witness.rising).check 32 21 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_21_7_checked :
    (Witness.rising).check 32 21 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_21_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_32_21_8_checked :
    (Witness.linear .positive case_32_21_8).check 32 21 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_21_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_32_21_9_checked :
    (Witness.linear .positive case_32_21_9).check 32 21 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_21_10 : Certificate := {
  objectiveScale := 25
  eta := 33033
  rows := #[⟨.assumptionRow 10, 58⟩]
  caps := #[0, 0, 10582, 3531, 1236, 462, 190, 91, 1430, 712, 192, 25] }

theorem case_32_21_10_checked :
    (Witness.linear .conditional case_32_21_10).check 32 21 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_21_11 : Certificate := {
  objectiveScale := 24875575200000
  eta := 622262264872248000
  rows := #[⟨.count 2, 101158436994975360⟩, ⟨.count 3, 16859739499162560⟩, ⟨.count 4, 2709169044341760⟩, ⟨.count 5, 397390867473600⟩, ⟨.count 6, 51833591409600⟩, ⟨.count 7, 24189009324480⟩, ⟨.path 5, 268363263168000⟩, ⟨.privateRow 2 19, 7873522535118240⟩, ⟨.privateRow 3 15, 822426317032320⟩, ⟨.privateRow 3 16, 2757547062990720⟩, ⟨.privateRow 3 17, 3096193193533440⟩, ⟨.privateRow 4 12, 188472697653240⟩, ⟨.privateRow 4 13, 914949277698456⟩, ⟨.privateRow 4 14, 1392379849240380⟩, ⟨.privateRow 4 15, 1499718578117760⟩, ⟨.privateRow 4 16, 849638952522360⟩, ⟨.privateRow 5 9, 11230611472080⟩, ⟨.privateRow 5 10, 230042415208320⟩, ⟨.privateRow 5 11, 531582276345120⟩, ⟨.privateRow 5 12, 709774645035456⟩, ⟨.privateRow 5 13, 574920918051480⟩, ⟨.privateRow 6 7, 18557705566400⟩, ⟨.privateRow 6 8, 172958615779950⟩, ⟨.privateRow 6 9, 320668924633200⟩, ⟨.privateRow 6 10, 301402735233600⟩, ⟨.privateRow 7 5, 14513405594688⟩, ⟨.privateRow 7 6, 132463622491200⟩, ⟨.privateRow 7 7, 153772987848480⟩, ⟨.privateRow 8 3, 10720129132440⟩, ⟨.privateRow 8 4, 91615872816468⟩, ⟨.privateRow 9 1, 7391086182480⟩, ⟨.privateRow 9 2, 24189009324480⟩, ⟨.privateRow 10 0, 9070878496680⟩, ⟨.hall 2 18, 1466617828515840⟩, ⟨.assumptionRow 11, 20164918618845⟩]
  caps := #[0, 192836346573780, 12819066910650, 2297682251865, 2375887474800, 5607366531624, 3950507865780, 0, 0, 19325592527010, 0, 203715258181155] }

theorem case_32_21_11_checked :
    (Witness.linear .conditional case_32_21_11).check 32 21 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_21_12 : Certificate := {
  objectiveScale := 169219373400000
  eta := 7580170324535608800
  rows := #[⟨.count 2, 1023479315285066640⟩, ⟨.count 3, 128467828522313280⟩, ⟨.count 4, 12742568537058360⟩, ⟨.count 5, 304522349531400⟩, ⟨.count 6, 33835816614600⟩, ⟨.path 4, 10380956521535600⟩, ⟨.path 5, 279421297755600⟩, ⟨.privateRow 2 19, 79581840677539200⟩, ⟨.privateRow 3 15, 10445116588927020⟩, ⟨.privateRow 3 16, 25264076405568000⟩, ⟨.privateRow 3 17, 30127411113639840⟩, ⟨.privateRow 4 12, 2548118956217835⟩, ⟨.privateRow 4 13, 8168981205262878⟩, ⟨.privateRow 4 14, 12197811889563300⟩, ⟨.privateRow 4 15, 14439998670557460⟩, ⟨.privateRow 4 16, 11735952992774010⟩, ⟨.privateRow 5 8, 9774791466440⟩, ⟨.privateRow 5 9, 316364885346510⟩, ⟨.privateRow 5 10, 2002113605966760⟩, ⟨.privateRow 5 11, 4258801451224320⟩, ⟨.privateRow 5 12, 6099921019280088⟩, ⟨.privateRow 5 13, 7464181145180760⟩, ⟨.privateRow 5 14, 1071467526129000⟩, ⟨.privateRow 6 7, 289484208813800⟩, ⟨.privateRow 6 8, 1298449462585275⟩, ⟨.privateRow 6 9, 2445846172426800⟩, ⟨.privateRow 6 10, 3620432377762200⟩, ⟨.privateRow 6 11, 1144778462127300⟩, ⟨.privateRow 7 5, 232113701976156⟩, ⟨.privateRow 7 6, 930860910419440⟩, ⟨.privateRow 7 7, 1760308359374565⟩, ⟨.privateRow 7 8, 548140229156520⟩, ⟨.privateRow 8 3, 221778397992060⟩, ⟨.privateRow 8 4, 834898774965255⟩, ⟨.privateRow 8 5, 243429902866150⟩, ⟨.privateRow 9 1, 294747558064960⟩, ⟨.privateRow 9 2, 157900477534800⟩, ⟨.privateRow 10 0, 153952965596430⟩, ⟨.hall 2 18, 15736860224205120⟩, ⟨.assumptionRow 12, 41777699362560⟩]
  caps := #[0, 445541078367840, 139988378990460, 0, 0, 44074528547192, 35355718038355, 436483426176, 0, 0, 0, 5546678774736960] }

theorem case_32_21_12_checked :
    (Witness.linear .conditional case_32_21_12).check 32 21 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_21_13 : Certificate := {
  objectiveScale := 7162724800000
  eta := 341449691285102400
  rows := #[⟨.count 2, 51057178771959360⟩, ⟨.count 3, 7205960439437760⟩, ⟨.count 4, 893265558625440⟩, ⟨.count 5, 73268535225600⟩, ⟨.path 4, 234911106487200⟩, ⟨.path 5, 72338940273600⟩, ⟨.privateRow 6 7, 395740545200⟩, ⟨.hall 9 3, 116563578768⟩, ⟨.hall 6 6, 297173079936⟩, ⟨.hall 8 6, 386884812720⟩, ⟨.hall 10 6, 277532330400⟩, ⟨.hall 7 7, 368619864480⟩, ⟨.hall 9 7, 663764823540⟩, ⟨.hall 6 8, 89759174208⟩, ⟨.hall 5 9, 343223877195⟩, ⟨.hall 4 11, 610686242100⟩, ⟨.hall 3 14, 4079153866788⟩]
  caps := #[0, 0, 4625665684640, 555757266240, 570427397760, 0, 0, 0, 4078455501120, 12686618165760, 0, 115076336636800] }

theorem case_32_21_13_checked :
    (Witness.linear .negative case_32_21_13).check 32 21 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_22_1_checked :
    (Witness.rising).check 32 22 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_22_2_checked :
    (Witness.rising).check 32 22 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_22_3_checked :
    (Witness.rising).check 32 22 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_22_4_checked :
    (Witness.rising).check 32 22 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_22_5_checked :
    (Witness.rising).check 32 22 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_22_6_checked :
    (Witness.rising).check 32 22 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_22_7_checked :
    (Witness.rising).check 32 22 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_22_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_32_22_8_checked :
    (Witness.linear .positive case_32_22_8).check 32 22 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_22_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_32_22_9_checked :
    (Witness.linear .positive case_32_22_9).check 32 22 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_22_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_32_22_10_checked :
    (Witness.linear .positive case_32_22_10).check 32 22 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_22_11 : Certificate := {
  objectiveScale := 915
  eta := 2304744
  rows := #[⟨.assumptionRow 11, 1642⟩]
  caps := #[0, 0, 727727, 236049, 79155, 27676, 10203, 4550, 134589, 83590, 31348] }

theorem case_32_22_11_checked :
    (Witness.linear .conditional case_32_22_11).check 32 22 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_22_12 : Certificate := {
  objectiveScale := 36981000000
  eta := 2593544900506560
  rows := #[⟨.count 2, 324419662607040⟩, ⟨.count 3, 39079882541700⟩, ⟨.count 4, 3495343531680⟩, ⟨.count 5, 17980162200⟩, ⟨.path 4, 3349456110000⟩, ⟨.privateRow 2 19, 5386856595120⟩, ⟨.privateRow 2 20, 23963960180160⟩, ⟨.privateRow 3 16, 6192367861680⟩, ⟨.privateRow 3 17, 9838145417100⟩, ⟨.privateRow 3 18, 9420705984690⟩, ⟨.privateRow 4 12, 268161276240⟩, ⟨.privateRow 4 13, 1255015321560⟩, ⟨.privateRow 4 14, 4035827207412⟩, ⟨.privateRow 4 15, 4691473822035⟩, ⟨.privateRow 4 16, 4354795284840⟩, ⟨.privateRow 5 9, 77914036200⟩, ⟨.privateRow 5 10, 268803424890⟩, ⟨.privateRow 5 11, 1065966759000⟩, ⟨.privateRow 5 12, 2158818141480⟩, ⟨.privateRow 5 13, 2634453365544⟩, ⟨.privateRow 5 14, 89900811000⟩, ⟨.privateRow 6 6, 6211328760⟩, ⟨.privateRow 6 7, 53940486600⟩, ⟨.privateRow 6 8, 272099787960⟩, ⟨.privateRow 6 9, 771798462435⟩, ⟨.privateRow 6 10, 1444063884120⟩, ⟨.privateRow 7 3, 1659707280⟩, ⟨.privateRow 7 4, 2247520275⟩, ⟨.privateRow 7 5, 64238215860⟩, ⟨.privateRow 7 6, 288042198444⟩, ⟨.privateRow 7 7, 622113612120⟩, ⟨.privateRow 8 0, 839074236⟩, ⟨.privateRow 8 1, 2697024330⟩, ⟨.privateRow 8 2, 4840812900⟩, ⟨.privateRow 8 3, 101737751115⟩, ⟨.privateRow 8 4, 243712925820⟩, ⟨.privateRow 9 0, 35960324400⟩, ⟨.privateRow 9 1, 77453006400⟩, ⟨.privateRow 10 0, 34853852880⟩, ⟨.hall 2 19, 2189983755960⟩, ⟨.assumptionRow 12, 16638655880⟩]
  caps := #[0, 0, 58960625360, 0, 28481622741, 4806125896, 3469984756, 54282708774, 0, 171412687600, 579270384000] }

theorem case_32_22_12_checked :
    (Witness.linear .conditional case_32_22_12).check 32 22 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_22_13 : Certificate := {
  objectiveScale := 16
  eta := 2772
  rows := #[⟨.assumptionRow 13, 9⟩]
  caps := #[0, 0, 1365, 533, 286, 115, 68, 4862, 7007, 5291, 3014] }

theorem case_32_22_13_checked :
    (Witness.linear .conditional case_32_22_13).check 32 22 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_22_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 429, 429, 297] }

theorem case_32_22_14_checked :
    (Witness.linear .negative case_32_22_14).check 32 22 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_23_1_checked :
    (Witness.rising).check 32 23 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_23_2_checked :
    (Witness.rising).check 32 23 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_23_3_checked :
    (Witness.rising).check 32 23 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_23_4_checked :
    (Witness.rising).check 32 23 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_23_5_checked :
    (Witness.rising).check 32 23 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_23_6_checked :
    (Witness.rising).check 32 23 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_23_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_32_23_7_checked :
    (Witness.linear .positive case_32_23_7).check 32 23 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_23_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_32_23_8_checked :
    (Witness.linear .positive case_32_23_8).check 32 23 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_23_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_32_23_9_checked :
    (Witness.linear .positive case_32_23_9).check 32 23 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_23_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_32_23_10_checked :
    (Witness.linear .positive case_32_23_10).check 32 23 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_23_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_32_23_11_checked :
    (Witness.linear .positive case_32_23_11).check 32 23 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_23_12 : Certificate := {
  objectiveScale := 518
  eta := 974168
  rows := #[⟨.assumptionRow 12, 591⟩]
  caps := #[0, 0, 334698, 115830, 40535, 14382, 6188, 379652, 310674, 168623] }

theorem case_32_23_12_checked :
    (Witness.linear .conditional case_32_23_12).check 32 23 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_23_13 : Certificate := {
  objectiveScale := 788
  eta := 385588
  rows := #[⟨.assumptionRow 13, 541⟩]
  caps := #[0, 0, 169078, 68185, 27423, 12995, 5304, 735176, 691418, 444171] }

theorem case_32_23_13_checked :
    (Witness.linear .conditional case_32_23_13).check 32 23 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_23_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 1430, 1430, 1001] }

theorem case_32_23_14_checked :
    (Witness.linear .negative case_32_23_14).check 32 23 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_24_1_checked :
    (Witness.rising).check 32 24 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_24_2_checked :
    (Witness.rising).check 32 24 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_24_3_checked :
    (Witness.rising).check 32 24 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_24_4_checked :
    (Witness.rising).check 32 24 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_24_5_checked :
    (Witness.rising).check 32 24 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_24_6_checked :
    (Witness.rising).check 32 24 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_24_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0] }

theorem case_32_24_7_checked :
    (Witness.linear .positive case_32_24_7).check 32 24 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_24_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0] }

theorem case_32_24_8_checked :
    (Witness.linear .positive case_32_24_8).check 32 24 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_24_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1] }

theorem case_32_24_9_checked :
    (Witness.linear .positive case_32_24_9).check 32 24 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_24_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_32_24_10_checked :
    (Witness.linear .positive case_32_24_10).check 32 24 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_24_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_32_24_11_checked :
    (Witness.linear .positive case_32_24_11).check 32 24 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_24_12 : Certificate := {
  objectiveScale := 11
  eta := 45084
  rows := #[⟨.assumptionRow 12, 16⟩]
  caps := #[0, 0, 14872, 5005, 1727, 615, 228, 7140, 7868] }

theorem case_32_24_12_checked :
    (Witness.linear .conditional case_32_24_12).check 32 24 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_24_13 : Certificate := {
  objectiveScale := 11
  eta := 13804
  rows := #[⟨.assumptionRow 13, 9⟩]
  caps := #[0, 0, 4732, 2002, 781, 290, 11934, 22100, 17108] }

theorem case_32_24_13_checked :
    (Witness.linear .conditional case_32_24_13).check 32 24 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_24_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 4862, 4862, 3432] }

theorem case_32_24_14_checked :
    (Witness.linear .negative case_32_24_14).check 32 24 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_24_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 1430] }

theorem case_32_24_15_checked :
    (Witness.linear .negative case_32_24_15).check 32 24 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_25_1_checked :
    (Witness.rising).check 32 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_25_2_checked :
    (Witness.rising).check 32 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_25_3_checked :
    (Witness.rising).check 32 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_25_4_checked :
    (Witness.rising).check 32 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_25_5_checked :
    (Witness.rising).check 32 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_25_6_checked :
    (Witness.rising).check 32 25 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_25_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0] }

theorem case_32_25_7_checked :
    (Witness.linear .positive case_32_25_7).check 32 25 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_25_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1] }

theorem case_32_25_8_checked :
    (Witness.linear .positive case_32_25_8).check 32 25 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_25_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_32_25_9_checked :
    (Witness.linear .positive case_32_25_9).check 32 25 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_25_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_32_25_10_checked :
    (Witness.linear .positive case_32_25_10).check 32 25 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_25_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_32_25_11_checked :
    (Witness.linear .positive case_32_25_11).check 32 25 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_25_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_32_25_12_checked :
    (Witness.linear .positive case_32_25_12).check 32 25 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_25_13 : Certificate := {
  objectiveScale := 8
  eta := 12852
  rows := #[⟨.assumptionRow 13, 7⟩]
  caps := #[0, 0, 5096, 1911, 693, 275, 38760, 36108] }

theorem case_32_25_13_checked :
    (Witness.linear .conditional case_32_25_13).check 32 25 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_25_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 16796, 16796, 11934] }

theorem case_32_25_14_checked :
    (Witness.linear .negative case_32_25_14).check 32 25 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_25_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 4862] }

theorem case_32_25_15_checked :
    (Witness.linear .negative case_32_25_15).check 32 25 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_25_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_32_25_16_checked :
    (Witness.linear .negative case_32_25_16).check 32 25 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_26_1_checked :
    (Witness.rising).check 32 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_26_2_checked :
    (Witness.rising).check 32 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_26_3_checked :
    (Witness.rising).check 32 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_26_4_checked :
    (Witness.rising).check 32 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_26_5_checked :
    (Witness.rising).check 32 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_26_6_checked :
    (Witness.rising).check 32 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_26_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1] }

theorem case_32_26_7_checked :
    (Witness.linear .positive case_32_26_7).check 32 26 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_26_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1] }

theorem case_32_26_8_checked :
    (Witness.linear .positive case_32_26_8).check 32 26 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_26_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_32_26_9_checked :
    (Witness.linear .positive case_32_26_9).check 32 26 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_26_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_32_26_10_checked :
    (Witness.linear .positive case_32_26_10).check 32 26 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_26_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_32_26_11_checked :
    (Witness.linear .positive case_32_26_11).check 32 26 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_26_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_32_26_12_checked :
    (Witness.linear .positive case_32_26_12).check 32 26 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_26_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_32_26_13_checked :
    (Witness.linear .positive case_32_26_13).check 32 26 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_26_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 58786, 58786, 41990] }

theorem case_32_26_14_checked :
    (Witness.linear .negative case_32_26_14).check 32 26 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_26_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 16796] }

theorem case_32_26_15_checked :
    (Witness.linear .negative case_32_26_15).check 32 26 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_26_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_32_26_16_checked :
    (Witness.linear .negative case_32_26_16).check 32 26 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_27_1_checked :
    (Witness.rising).check 32 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_27_2_checked :
    (Witness.rising).check 32 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_27_3_checked :
    (Witness.rising).check 32 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_27_4_checked :
    (Witness.rising).check 32 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_27_5_checked :
    (Witness.rising).check 32 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_27_6_checked :
    (Witness.rising).check 32 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_27_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1] }

theorem case_32_27_7_checked :
    (Witness.linear .positive case_32_27_7).check 32 27 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_27_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2] }

theorem case_32_27_8_checked :
    (Witness.linear .positive case_32_27_8).check 32 27 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_27_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_32_27_9_checked :
    (Witness.linear .positive case_32_27_9).check 32 27 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_27_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_32_27_10_checked :
    (Witness.linear .positive case_32_27_10).check 32 27 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_27_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_32_27_11_checked :
    (Witness.linear .positive case_32_27_11).check 32 27 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_27_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_32_27_12_checked :
    (Witness.linear .positive case_32_27_12).check 32 27 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_27_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_32_27_13_checked :
    (Witness.linear .positive case_32_27_13).check 32 27 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_27_14 : Certificate := {
  objectiveScale := 65
  eta := 131784
  rows := #[⟨.assumptionRow 14, 49⟩]
  caps := #[0, 0, 55692, 21112, 7644, 994840] }

theorem case_32_27_14_checked :
    (Witness.linear .conditional case_32_27_14).check 32 27 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_27_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 58786] }

theorem case_32_27_15_checked :
    (Witness.linear .negative case_32_27_15).check 32 27 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_27_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_32_27_16_checked :
    (Witness.linear .negative case_32_27_16).check 32 27 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_27_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_32_27_17_checked :
    (Witness.linear .negative case_32_27_17).check 32 27 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_28_1_checked :
    (Witness.rising).check 32 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_28_2_checked :
    (Witness.rising).check 32 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_28_3_checked :
    (Witness.rising).check 32 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_28_4_checked :
    (Witness.rising).check 32 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_28_5_checked :
    (Witness.rising).check 32 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_28_6_checked :
    (Witness.rising).check 32 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_28_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2] }

theorem case_32_28_7_checked :
    (Witness.linear .positive case_32_28_7).check 32 28 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_28_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5] }

theorem case_32_28_8_checked :
    (Witness.linear .positive case_32_28_8).check 32 28 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_28_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_32_28_9_checked :
    (Witness.linear .positive case_32_28_9).check 32 28 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_28_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_32_28_10_checked :
    (Witness.linear .positive case_32_28_10).check 32 28 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_28_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_32_28_11_checked :
    (Witness.linear .positive case_32_28_11).check 32 28 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_28_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_32_28_12_checked :
    (Witness.linear .positive case_32_28_12).check 32 28 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_28_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_32_28_13_checked :
    (Witness.linear .positive case_32_28_13).check 32 28 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_28_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_32_28_14_checked :
    (Witness.linear .positive case_32_28_14).check 32 28 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_28_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 208012] }

theorem case_32_28_15_checked :
    (Witness.linear .negative case_32_28_15).check 32 28 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_28_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_32_28_16_checked :
    (Witness.linear .negative case_32_28_16).check 32 28 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_28_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_32_28_17_checked :
    (Witness.linear .negative case_32_28_17).check 32 28 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_28_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_32_28_18_checked :
    (Witness.linear .negative case_32_28_18).check 32 28 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_29_1_checked :
    (Witness.rising).check 32 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_29_2_checked :
    (Witness.rising).check 32 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_29_3_checked :
    (Witness.rising).check 32 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_29_4_checked :
    (Witness.rising).check 32 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_29_5_checked :
    (Witness.rising).check 32 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_29_6_checked :
    (Witness.rising).check 32 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_29_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5] }

theorem case_32_29_7_checked :
    (Witness.linear .positive case_32_29_7).check 32 29 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_29_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14] }

theorem case_32_29_8_checked :
    (Witness.linear .positive case_32_29_8).check 32 29 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_29_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_32_29_9_checked :
    (Witness.linear .positive case_32_29_9).check 32 29 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_29_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_32_29_10_checked :
    (Witness.linear .positive case_32_29_10).check 32 29 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_29_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_32_29_11_checked :
    (Witness.linear .positive case_32_29_11).check 32 29 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_29_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_32_29_12_checked :
    (Witness.linear .positive case_32_29_12).check 32 29 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_29_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_32_29_13_checked :
    (Witness.linear .positive case_32_29_13).check 32 29 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_29_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_32_29_14_checked :
    (Witness.linear .positive case_32_29_14).check 32 29 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_29_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 742900] }

theorem case_32_29_15_checked :
    (Witness.linear .negative case_32_29_15).check 32 29 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_29_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_32_29_16_checked :
    (Witness.linear .negative case_32_29_16).check 32 29 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_29_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_32_29_17_checked :
    (Witness.linear .negative case_32_29_17).check 32 29 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_29_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_32_29_18_checked :
    (Witness.linear .negative case_32_29_18).check 32 29 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_30_1_checked :
    (Witness.rising).check 32 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_30_2_checked :
    (Witness.rising).check 32 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_30_3_checked :
    (Witness.rising).check 32 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_30_4_checked :
    (Witness.rising).check 32 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_30_5_checked :
    (Witness.rising).check 32 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_30_6_checked :
    (Witness.rising).check 32 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_30_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14] }

theorem case_32_30_7_checked :
    (Witness.linear .positive case_32_30_7).check 32 30 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_30_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_32_30_8_checked :
    (Witness.linear .positive case_32_30_8).check 32 30 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_30_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_32_30_9_checked :
    (Witness.linear .positive case_32_30_9).check 32 30 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_30_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_32_30_10_checked :
    (Witness.linear .positive case_32_30_10).check 32 30 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_32_30_11_checked :
    (Witness.linear .positive case_32_30_11).check 32 30 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_30_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_32_30_12_checked :
    (Witness.linear .positive case_32_30_12).check 32 30 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_30_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_32_30_13_checked :
    (Witness.linear .positive case_32_30_13).check 32 30 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_30_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_32_30_14_checked :
    (Witness.linear .positive case_32_30_14).check 32 30 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_30_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_32_30_15_checked :
    (Witness.linear .positive case_32_30_15).check 32 30 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_30_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_32_30_16_checked :
    (Witness.linear .negative case_32_30_16).check 32 30 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_30_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_32_30_17_checked :
    (Witness.linear .negative case_32_30_17).check 32 30 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_30_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_32_30_18_checked :
    (Witness.linear .negative case_32_30_18).check 32 30 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_30_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_32_30_19_checked :
    (Witness.linear .negative case_32_30_19).check 32 30 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_31_1_checked :
    (Witness.rising).check 32 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_31_2_checked :
    (Witness.rising).check 32 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_31_3_checked :
    (Witness.rising).check 32 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_31_4_checked :
    (Witness.rising).check 32 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_31_5_checked :
    (Witness.rising).check 32 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_32_31_6_checked :
    (Witness.rising).check 32 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_31_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0] }

theorem case_32_31_7_checked :
    (Witness.linear .positive case_32_31_7).check 32 31 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_31_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_32_31_8_checked :
    (Witness.linear .positive case_32_31_8).check 32 31 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_31_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_32_31_9_checked :
    (Witness.linear .positive case_32_31_9).check 32 31 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_31_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_32_31_10_checked :
    (Witness.linear .positive case_32_31_10).check 32 31 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_32_31_11_checked :
    (Witness.linear .positive case_32_31_11).check 32 31 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_32_31_12_checked :
    (Witness.linear .positive case_32_31_12).check 32 31 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_31_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_32_31_13_checked :
    (Witness.linear .positive case_32_31_13).check 32 31 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_31_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_32_31_14_checked :
    (Witness.linear .positive case_32_31_14).check 32 31 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_31_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_32_31_15_checked :
    (Witness.linear .positive case_32_31_15).check 32 31 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_31_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_32_31_16_checked :
    (Witness.linear .negative case_32_31_16).check 32 31 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_31_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_32_31_17_checked :
    (Witness.linear .negative case_32_31_17).check 32 31 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_31_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_32_31_18_checked :
    (Witness.linear .negative case_32_31_18).check 32 31 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_31_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_32_31_19_checked :
    (Witness.linear .negative case_32_31_19).check 32 31 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_32_31_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_32_31_20_checked :
    (Witness.linear .negative case_32_31_20).check 32 31 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_32 (a k : ℕ) (h : Domain 32 a k) :
    ∃ w : Witness, w.check 32 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 16 ≤ a := by omega
  have haHi : a ≤ 31 := by omega
  interval_cases a

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_32_16_1_checked⟩

    · exact ⟨Witness.rising, case_32_16_2_checked⟩

    · exact ⟨Witness.rising, case_32_16_3_checked⟩

    · exact ⟨Witness.rising, case_32_16_4_checked⟩

    · exact ⟨Witness.rising, case_32_16_5_checked⟩

    · exact ⟨Witness.rising, case_32_16_6_checked⟩

    · exact ⟨Witness.rising, case_32_16_7_checked⟩

    · exact ⟨Witness.linear .positive case_32_16_8, case_32_16_8_checked⟩

    · exact ⟨Witness.linear .positive case_32_16_9, case_32_16_9_checked⟩

    · exact ⟨Witness.linear .conditional case_32_16_10, case_32_16_10_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_32_17_1_checked⟩

    · exact ⟨Witness.rising, case_32_17_2_checked⟩

    · exact ⟨Witness.rising, case_32_17_3_checked⟩

    · exact ⟨Witness.rising, case_32_17_4_checked⟩

    · exact ⟨Witness.rising, case_32_17_5_checked⟩

    · exact ⟨Witness.rising, case_32_17_6_checked⟩

    · exact ⟨Witness.rising, case_32_17_7_checked⟩

    · exact ⟨Witness.linear .positive case_32_17_8, case_32_17_8_checked⟩

    · exact ⟨Witness.linear .positive case_32_17_9, case_32_17_9_checked⟩

    · exact ⟨Witness.linear .conditional case_32_17_10, case_32_17_10_checked⟩

  · have hkHi : k ≤ 11 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_32_18_1_checked⟩

    · exact ⟨Witness.rising, case_32_18_2_checked⟩

    · exact ⟨Witness.rising, case_32_18_3_checked⟩

    · exact ⟨Witness.rising, case_32_18_4_checked⟩

    · exact ⟨Witness.rising, case_32_18_5_checked⟩

    · exact ⟨Witness.rising, case_32_18_6_checked⟩

    · exact ⟨Witness.rising, case_32_18_7_checked⟩

    · exact ⟨Witness.linear .positive case_32_18_8, case_32_18_8_checked⟩

    · exact ⟨Witness.linear .positive case_32_18_9, case_32_18_9_checked⟩

    · exact ⟨Witness.linear .conditional case_32_18_10, case_32_18_10_checked⟩

    · exact ⟨Witness.linear .conditional case_32_18_11, case_32_18_11_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_32_19_1_checked⟩

    · exact ⟨Witness.rising, case_32_19_2_checked⟩

    · exact ⟨Witness.rising, case_32_19_3_checked⟩

    · exact ⟨Witness.rising, case_32_19_4_checked⟩

    · exact ⟨Witness.rising, case_32_19_5_checked⟩

    · exact ⟨Witness.rising, case_32_19_6_checked⟩

    · exact ⟨Witness.rising, case_32_19_7_checked⟩

    · exact ⟨Witness.linear .positive case_32_19_8, case_32_19_8_checked⟩

    · exact ⟨Witness.linear .positive case_32_19_9, case_32_19_9_checked⟩

    · exact ⟨Witness.linear .conditional case_32_19_10, case_32_19_10_checked⟩

    · exact ⟨Witness.linear .conditional case_32_19_11, case_32_19_11_checked⟩

    · exact ⟨Witness.linear .negative case_32_19_12, case_32_19_12_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_32_20_1_checked⟩

    · exact ⟨Witness.rising, case_32_20_2_checked⟩

    · exact ⟨Witness.rising, case_32_20_3_checked⟩

    · exact ⟨Witness.rising, case_32_20_4_checked⟩

    · exact ⟨Witness.rising, case_32_20_5_checked⟩

    · exact ⟨Witness.rising, case_32_20_6_checked⟩

    · exact ⟨Witness.rising, case_32_20_7_checked⟩

    · exact ⟨Witness.linear .positive case_32_20_8, case_32_20_8_checked⟩

    · exact ⟨Witness.linear .positive case_32_20_9, case_32_20_9_checked⟩

    · exact ⟨Witness.linear .conditional case_32_20_10, case_32_20_10_checked⟩

    · exact ⟨Witness.linear .conditional case_32_20_11, case_32_20_11_checked⟩

    · exact ⟨Witness.linear .negative case_32_20_12, case_32_20_12_checked⟩

  · have hkHi : k ≤ 13 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_32_21_1_checked⟩

    · exact ⟨Witness.rising, case_32_21_2_checked⟩

    · exact ⟨Witness.rising, case_32_21_3_checked⟩

    · exact ⟨Witness.rising, case_32_21_4_checked⟩

    · exact ⟨Witness.rising, case_32_21_5_checked⟩

    · exact ⟨Witness.rising, case_32_21_6_checked⟩

    · exact ⟨Witness.rising, case_32_21_7_checked⟩

    · exact ⟨Witness.linear .positive case_32_21_8, case_32_21_8_checked⟩

    · exact ⟨Witness.linear .positive case_32_21_9, case_32_21_9_checked⟩

    · exact ⟨Witness.linear .conditional case_32_21_10, case_32_21_10_checked⟩

    · exact ⟨Witness.linear .conditional case_32_21_11, case_32_21_11_checked⟩

    · exact ⟨Witness.linear .conditional case_32_21_12, case_32_21_12_checked⟩

    · exact ⟨Witness.linear .negative case_32_21_13, case_32_21_13_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_32_22_1_checked⟩

    · exact ⟨Witness.rising, case_32_22_2_checked⟩

    · exact ⟨Witness.rising, case_32_22_3_checked⟩

    · exact ⟨Witness.rising, case_32_22_4_checked⟩

    · exact ⟨Witness.rising, case_32_22_5_checked⟩

    · exact ⟨Witness.rising, case_32_22_6_checked⟩

    · exact ⟨Witness.rising, case_32_22_7_checked⟩

    · exact ⟨Witness.linear .positive case_32_22_8, case_32_22_8_checked⟩

    · exact ⟨Witness.linear .positive case_32_22_9, case_32_22_9_checked⟩

    · exact ⟨Witness.linear .positive case_32_22_10, case_32_22_10_checked⟩

    · exact ⟨Witness.linear .conditional case_32_22_11, case_32_22_11_checked⟩

    · exact ⟨Witness.linear .conditional case_32_22_12, case_32_22_12_checked⟩

    · exact ⟨Witness.linear .conditional case_32_22_13, case_32_22_13_checked⟩

    · exact ⟨Witness.linear .negative case_32_22_14, case_32_22_14_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_32_23_1_checked⟩

    · exact ⟨Witness.rising, case_32_23_2_checked⟩

    · exact ⟨Witness.rising, case_32_23_3_checked⟩

    · exact ⟨Witness.rising, case_32_23_4_checked⟩

    · exact ⟨Witness.rising, case_32_23_5_checked⟩

    · exact ⟨Witness.rising, case_32_23_6_checked⟩

    · exact ⟨Witness.linear .positive case_32_23_7, case_32_23_7_checked⟩

    · exact ⟨Witness.linear .positive case_32_23_8, case_32_23_8_checked⟩

    · exact ⟨Witness.linear .positive case_32_23_9, case_32_23_9_checked⟩

    · exact ⟨Witness.linear .positive case_32_23_10, case_32_23_10_checked⟩

    · exact ⟨Witness.linear .positive case_32_23_11, case_32_23_11_checked⟩

    · exact ⟨Witness.linear .conditional case_32_23_12, case_32_23_12_checked⟩

    · exact ⟨Witness.linear .conditional case_32_23_13, case_32_23_13_checked⟩

    · exact ⟨Witness.linear .negative case_32_23_14, case_32_23_14_checked⟩

  · have hkHi : k ≤ 15 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_32_24_1_checked⟩

    · exact ⟨Witness.rising, case_32_24_2_checked⟩

    · exact ⟨Witness.rising, case_32_24_3_checked⟩

    · exact ⟨Witness.rising, case_32_24_4_checked⟩

    · exact ⟨Witness.rising, case_32_24_5_checked⟩

    · exact ⟨Witness.rising, case_32_24_6_checked⟩

    · exact ⟨Witness.linear .positive case_32_24_7, case_32_24_7_checked⟩

    · exact ⟨Witness.linear .positive case_32_24_8, case_32_24_8_checked⟩

    · exact ⟨Witness.linear .positive case_32_24_9, case_32_24_9_checked⟩

    · exact ⟨Witness.linear .positive case_32_24_10, case_32_24_10_checked⟩

    · exact ⟨Witness.linear .positive case_32_24_11, case_32_24_11_checked⟩

    · exact ⟨Witness.linear .conditional case_32_24_12, case_32_24_12_checked⟩

    · exact ⟨Witness.linear .conditional case_32_24_13, case_32_24_13_checked⟩

    · exact ⟨Witness.linear .negative case_32_24_14, case_32_24_14_checked⟩

    · exact ⟨Witness.linear .negative case_32_24_15, case_32_24_15_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_32_25_1_checked⟩

    · exact ⟨Witness.rising, case_32_25_2_checked⟩

    · exact ⟨Witness.rising, case_32_25_3_checked⟩

    · exact ⟨Witness.rising, case_32_25_4_checked⟩

    · exact ⟨Witness.rising, case_32_25_5_checked⟩

    · exact ⟨Witness.rising, case_32_25_6_checked⟩

    · exact ⟨Witness.linear .positive case_32_25_7, case_32_25_7_checked⟩

    · exact ⟨Witness.linear .positive case_32_25_8, case_32_25_8_checked⟩

    · exact ⟨Witness.linear .positive case_32_25_9, case_32_25_9_checked⟩

    · exact ⟨Witness.linear .positive case_32_25_10, case_32_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_32_25_11, case_32_25_11_checked⟩

    · exact ⟨Witness.linear .positive case_32_25_12, case_32_25_12_checked⟩

    · exact ⟨Witness.linear .conditional case_32_25_13, case_32_25_13_checked⟩

    · exact ⟨Witness.linear .negative case_32_25_14, case_32_25_14_checked⟩

    · exact ⟨Witness.linear .negative case_32_25_15, case_32_25_15_checked⟩

    · exact ⟨Witness.linear .negative case_32_25_16, case_32_25_16_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_32_26_1_checked⟩

    · exact ⟨Witness.rising, case_32_26_2_checked⟩

    · exact ⟨Witness.rising, case_32_26_3_checked⟩

    · exact ⟨Witness.rising, case_32_26_4_checked⟩

    · exact ⟨Witness.rising, case_32_26_5_checked⟩

    · exact ⟨Witness.rising, case_32_26_6_checked⟩

    · exact ⟨Witness.linear .positive case_32_26_7, case_32_26_7_checked⟩

    · exact ⟨Witness.linear .positive case_32_26_8, case_32_26_8_checked⟩

    · exact ⟨Witness.linear .positive case_32_26_9, case_32_26_9_checked⟩

    · exact ⟨Witness.linear .positive case_32_26_10, case_32_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_32_26_11, case_32_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_32_26_12, case_32_26_12_checked⟩

    · exact ⟨Witness.linear .positive case_32_26_13, case_32_26_13_checked⟩

    · exact ⟨Witness.linear .negative case_32_26_14, case_32_26_14_checked⟩

    · exact ⟨Witness.linear .negative case_32_26_15, case_32_26_15_checked⟩

    · exact ⟨Witness.linear .negative case_32_26_16, case_32_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_32_27_1_checked⟩

    · exact ⟨Witness.rising, case_32_27_2_checked⟩

    · exact ⟨Witness.rising, case_32_27_3_checked⟩

    · exact ⟨Witness.rising, case_32_27_4_checked⟩

    · exact ⟨Witness.rising, case_32_27_5_checked⟩

    · exact ⟨Witness.rising, case_32_27_6_checked⟩

    · exact ⟨Witness.linear .positive case_32_27_7, case_32_27_7_checked⟩

    · exact ⟨Witness.linear .positive case_32_27_8, case_32_27_8_checked⟩

    · exact ⟨Witness.linear .positive case_32_27_9, case_32_27_9_checked⟩

    · exact ⟨Witness.linear .positive case_32_27_10, case_32_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_32_27_11, case_32_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_32_27_12, case_32_27_12_checked⟩

    · exact ⟨Witness.linear .positive case_32_27_13, case_32_27_13_checked⟩

    · exact ⟨Witness.linear .conditional case_32_27_14, case_32_27_14_checked⟩

    · exact ⟨Witness.linear .negative case_32_27_15, case_32_27_15_checked⟩

    · exact ⟨Witness.linear .negative case_32_27_16, case_32_27_16_checked⟩

    · exact ⟨Witness.linear .negative case_32_27_17, case_32_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_32_28_1_checked⟩

    · exact ⟨Witness.rising, case_32_28_2_checked⟩

    · exact ⟨Witness.rising, case_32_28_3_checked⟩

    · exact ⟨Witness.rising, case_32_28_4_checked⟩

    · exact ⟨Witness.rising, case_32_28_5_checked⟩

    · exact ⟨Witness.rising, case_32_28_6_checked⟩

    · exact ⟨Witness.linear .positive case_32_28_7, case_32_28_7_checked⟩

    · exact ⟨Witness.linear .positive case_32_28_8, case_32_28_8_checked⟩

    · exact ⟨Witness.linear .positive case_32_28_9, case_32_28_9_checked⟩

    · exact ⟨Witness.linear .positive case_32_28_10, case_32_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_32_28_11, case_32_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_32_28_12, case_32_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_32_28_13, case_32_28_13_checked⟩

    · exact ⟨Witness.linear .positive case_32_28_14, case_32_28_14_checked⟩

    · exact ⟨Witness.linear .negative case_32_28_15, case_32_28_15_checked⟩

    · exact ⟨Witness.linear .negative case_32_28_16, case_32_28_16_checked⟩

    · exact ⟨Witness.linear .negative case_32_28_17, case_32_28_17_checked⟩

    · exact ⟨Witness.linear .negative case_32_28_18, case_32_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_32_29_1_checked⟩

    · exact ⟨Witness.rising, case_32_29_2_checked⟩

    · exact ⟨Witness.rising, case_32_29_3_checked⟩

    · exact ⟨Witness.rising, case_32_29_4_checked⟩

    · exact ⟨Witness.rising, case_32_29_5_checked⟩

    · exact ⟨Witness.rising, case_32_29_6_checked⟩

    · exact ⟨Witness.linear .positive case_32_29_7, case_32_29_7_checked⟩

    · exact ⟨Witness.linear .positive case_32_29_8, case_32_29_8_checked⟩

    · exact ⟨Witness.linear .positive case_32_29_9, case_32_29_9_checked⟩

    · exact ⟨Witness.linear .positive case_32_29_10, case_32_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_32_29_11, case_32_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_32_29_12, case_32_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_32_29_13, case_32_29_13_checked⟩

    · exact ⟨Witness.linear .positive case_32_29_14, case_32_29_14_checked⟩

    · exact ⟨Witness.linear .negative case_32_29_15, case_32_29_15_checked⟩

    · exact ⟨Witness.linear .negative case_32_29_16, case_32_29_16_checked⟩

    · exact ⟨Witness.linear .negative case_32_29_17, case_32_29_17_checked⟩

    · exact ⟨Witness.linear .negative case_32_29_18, case_32_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_32_30_1_checked⟩

    · exact ⟨Witness.rising, case_32_30_2_checked⟩

    · exact ⟨Witness.rising, case_32_30_3_checked⟩

    · exact ⟨Witness.rising, case_32_30_4_checked⟩

    · exact ⟨Witness.rising, case_32_30_5_checked⟩

    · exact ⟨Witness.rising, case_32_30_6_checked⟩

    · exact ⟨Witness.linear .positive case_32_30_7, case_32_30_7_checked⟩

    · exact ⟨Witness.linear .positive case_32_30_8, case_32_30_8_checked⟩

    · exact ⟨Witness.linear .positive case_32_30_9, case_32_30_9_checked⟩

    · exact ⟨Witness.linear .positive case_32_30_10, case_32_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_32_30_11, case_32_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_32_30_12, case_32_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_32_30_13, case_32_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_32_30_14, case_32_30_14_checked⟩

    · exact ⟨Witness.linear .positive case_32_30_15, case_32_30_15_checked⟩

    · exact ⟨Witness.linear .negative case_32_30_16, case_32_30_16_checked⟩

    · exact ⟨Witness.linear .negative case_32_30_17, case_32_30_17_checked⟩

    · exact ⟨Witness.linear .negative case_32_30_18, case_32_30_18_checked⟩

    · exact ⟨Witness.linear .negative case_32_30_19, case_32_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_32_31_1_checked⟩

    · exact ⟨Witness.rising, case_32_31_2_checked⟩

    · exact ⟨Witness.rising, case_32_31_3_checked⟩

    · exact ⟨Witness.rising, case_32_31_4_checked⟩

    · exact ⟨Witness.rising, case_32_31_5_checked⟩

    · exact ⟨Witness.rising, case_32_31_6_checked⟩

    · exact ⟨Witness.linear .positive case_32_31_7, case_32_31_7_checked⟩

    · exact ⟨Witness.linear .positive case_32_31_8, case_32_31_8_checked⟩

    · exact ⟨Witness.linear .positive case_32_31_9, case_32_31_9_checked⟩

    · exact ⟨Witness.linear .positive case_32_31_10, case_32_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_32_31_11, case_32_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_32_31_12, case_32_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_32_31_13, case_32_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_32_31_14, case_32_31_14_checked⟩

    · exact ⟨Witness.linear .positive case_32_31_15, case_32_31_15_checked⟩

    · exact ⟨Witness.linear .negative case_32_31_16, case_32_31_16_checked⟩

    · exact ⟨Witness.linear .negative case_32_31_17, case_32_31_17_checked⟩

    · exact ⟨Witness.linear .negative case_32_31_18, case_32_31_18_checked⟩

    · exact ⟨Witness.linear .negative case_32_31_19, case_32_31_19_checked⟩

    · exact ⟨Witness.linear .negative case_32_31_20, case_32_31_20_checked⟩


#print axioms coverage_32
end ForestUnimodality.FiniteRows.FiniteData
