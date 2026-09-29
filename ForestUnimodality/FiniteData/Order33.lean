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

theorem case_33_17_1_checked :
    (Witness.rising).check 33 17 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_17_2_checked :
    (Witness.rising).check 33 17 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_17_3_checked :
    (Witness.rising).check 33 17 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_17_4_checked :
    (Witness.rising).check 33 17 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_17_5_checked :
    (Witness.rising).check 33 17 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_17_6_checked :
    (Witness.rising).check 33 17 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_17_7_checked :
    (Witness.rising).check 33 17 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_17_8 : Certificate := {
  objectiveScale := 795009600000
  eta := 1288009760637600
  rows := #[⟨.count 2, 301052883811680⟩, ⟨.count 3, 47441323369440⟩, ⟨.count 4, 9583761227040⟩, ⟨.count 5, 2458467811800⟩, ⟨.count 6, 953415262800⟩, ⟨.count 7, 797613256440⟩, ⟨.path 8, 160835875200⟩, ⟨.path 9, 169072041600⟩, ⟨.privateRow 6 5, 184555800⟩, ⟨.privateRow 8 0, 29119214124⟩, ⟨.privateRow 9 0, 18756337600⟩, ⟨.hall 6 3, 3957883020⟩, ⟨.hall 6 4, 479845080⟩, ⟨.hall 5 6, 2570964825⟩, ⟨.hall 4 9, 7679792736⟩, ⟨.hall 7 9, 14650039404⟩, ⟨.hall 3 13, 973845589860⟩]
  caps := #[0, 0, 300040060320, 104668363800, 19313545680, 4474701000, 8326998900, 1136628360, 0, 265003200, 0, 0, 0, 0, 0, 0, 0] }

theorem case_33_17_8_checked :
    (Witness.linear .positive case_33_17_8).check 33 17 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_17_9 : Certificate := {
  objectiveScale := 2162160000
  eta := 4853492443800
  rows := #[⟨.count 2, 1380837538080⟩, ⟨.count 3, 264820275720⟩, ⟨.count 4, 58365347040⟩, ⟨.count 5, 14983768800⟩, ⟨.count 6, 5027022000⟩, ⟨.count 7, 2156754600⟩, ⟨.count 8, 2159277120⟩, ⟨.path 10, 694969275⟩, ⟨.privateRow 9 0, 74274200⟩, ⟨.privateRow 10 0, 86756670⟩, ⟨.privateRow 11 0, 130501800⟩, ⟨.hall 7 3, 15081066⟩, ⟨.hall 8 3, 7847840⟩, ⟨.hall 7 5, 6270264⟩, ⟨.hall 5 7, 24894870⟩, ⟨.hall 6 7, 47592090⟩, ⟨.hall 4 10, 119584080⟩]
  caps := #[0, 5067262200, 0, 190270080, 49549500, 0, 4954950, 5405400, 2882880, 5195190, 16321305, 0, 0, 0, 0, 0, 0] }

theorem case_33_17_9_checked :
    (Witness.linear .positive case_33_17_9).check 33 17 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_17_10 : Certificate := {
  objectiveScale := 2457000000
  eta := 4593773784600
  rows := #[⟨.count 2, 1144926422640⟩, ⟨.count 3, 287081875080⟩, ⟨.count 4, 87619371840⟩, ⟨.count 5, 29194565400⟩, ⟨.count 6, 11124313200⟩, ⟨.count 7, 5221616400⟩, ⟨.count 8, 3491167680⟩, ⟨.count 9, 3496212720⟩, ⟨.count 11, 2437835400⟩, ⟨.path 9, 701981280⟩, ⟨.privateRow 3 14, 10203233040⟩, ⟨.privateRow 10 0, 168243075⟩, ⟨.hall 8 2, 79359280⟩, ⟨.hall 7 4, 81099018⟩, ⟨.hall 8 4, 25817792⟩, ⟨.hall 6 6, 86289840⟩, ⟨.hall 5 8, 3783780⟩, ⟨.hall 4 10, 589271760⟩, ⟨.hall 5 10, 2821168350⟩, ⟨.hall 6 10, 1963634400⟩, ⟨.hall 3 13, 31371628860⟩, ⟨.assumptionRow 10, 2788007040⟩]
  caps := #[0, 0, 1658376720, 0, 0, 8877960, 7534800, 3341520, 2411136, 0, 8734635, 19164600, 0, 0, 0, 0, 0] }

theorem case_33_17_10_checked :
    (Witness.linear .conditional case_33_17_10).check 33 17 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_18_1_checked :
    (Witness.rising).check 33 18 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_18_2_checked :
    (Witness.rising).check 33 18 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_18_3_checked :
    (Witness.rising).check 33 18 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_18_4_checked :
    (Witness.rising).check 33 18 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_18_5_checked :
    (Witness.rising).check 33 18 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_18_6_checked :
    (Witness.rising).check 33 18 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_18_7_checked :
    (Witness.rising).check 33 18 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_18_8 : Certificate := {
  objectiveScale := 3964831200000
  eta := 7262608097384640
  rows := #[⟨.count 2, 1296894303104400⟩, ⟨.count 3, 218969301030480⟩, ⟨.count 4, 45208194791760⟩, ⟨.count 5, 11939188060800⟩, ⟨.count 6, 4752715247280⟩, ⟨.count 7, 3964422702240⟩, ⟨.path 8, 773707334400⟩, ⟨.path 9, 833245320600⟩, ⟨.privateRow 4 11, 1152303847695⟩, ⟨.privateRow 5 8, 849519150480⟩, ⟨.privateRow 5 9, 1102078897920⟩, ⟨.privateRow 5 10, 1044678955320⟩, ⟨.privateRow 6 5, 375969624030⟩, ⟨.privateRow 6 6, 536279463720⟩, ⟨.privateRow 6 7, 375012958320⟩, ⟨.privateRow 7 2, 176026490640⟩, ⟨.privateRow 7 3, 199836837200⟩, ⟨.privateRow 8 0, 135759561210⟩, ⟨.privateRow 9 0, 83421249912⟩, ⟨.hall 4 12, 131830637400⟩, ⟨.hall 3 13, 779327220672⟩]
  caps := #[0, 1359639412560, 0, 85107179520, 105419769840, 29524603680, 0, 16984874280, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_33_18_8_checked :
    (Witness.linear .positive case_33_18_8).check 33 18 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_18_9 : Certificate := {
  objectiveScale := 118800000
  eta := 321401840760
  rows := #[⟨.count 2, 68021553600⟩, ⟨.count 3, 13592418840⟩, ⟨.count 4, 3103780680⟩, ⟨.count 5, 816215400⟩, ⟨.count 6, 275675400⟩, ⟨.count 7, 118558440⟩, ⟨.count 8, 118558440⟩, ⟨.path 10, 36958680⟩, ⟨.privateRow 8 6, 10216206⟩, ⟨.privateRow 9 0, 4144140⟩, ⟨.privateRow 10 0, 4084080⟩, ⟨.hall 10 2, 2471040⟩, ⟨.hall 7 4, 348348⟩, ⟨.hall 8 4, 124124⟩, ⟨.hall 6 5, 607230⟩, ⟨.hall 5 7, 650475⟩, ⟨.hall 9 8, 5045040⟩, ⟨.hall 4 10, 1737450⟩, ⟨.hall 3 13, 64725804⟩]
  caps := #[0, 0, 0, 0, 748440, 0, 0, 1974060, 241560, 0, 2364120, 0, 0, 0, 0, 0] }

theorem case_33_18_9_checked :
    (Witness.linear .positive case_33_18_9).check 33 18 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_18_10 : Certificate := {
  objectiveScale := 873600000
  eta := 2830933385280
  rows := #[⟨.count 2, 629508559680⟩, ⟨.count 3, 164964159360⟩, ⟨.count 4, 44142658560⟩, ⟨.count 5, 14443228800⟩, ⟨.count 6, 5292967680⟩, ⟨.count 7, 2361078720⟩, ⟨.count 8, 1473151680⟩, ⟨.count 9, 1375133760⟩, ⟨.path 9, 291202560⟩, ⟨.privateRow 3 15, 11416204800⟩, ⟨.privateRow 5 10, 2270268000⟩, ⟨.privateRow 6 7, 203963760⟩, ⟨.privateRow 6 8, 1036107072⟩, ⟨.privateRow 6 9, 2162160000⟩, ⟨.privateRow 7 5, 184504320⟩, ⟨.privateRow 7 6, 582822240⟩, ⟨.privateRow 7 7, 1073007936⟩, ⟨.privateRow 7 8, 787026240⟩, ⟨.privateRow 8 3, 132116985⟩, ⟨.privateRow 8 4, 372972600⟩, ⟨.privateRow 8 5, 408648240⟩, ⟨.privateRow 9 1, 102182080⟩, ⟨.privateRow 9 2, 185225040⟩, ⟨.privateRow 10 0, 114834720⟩, ⟨.privateRow 11 0, 109189080⟩, ⟨.hall 5 10, 7308000⟩, ⟨.hall 5 11, 529452000⟩, ⟨.hall 4 12, 1515365280⟩, ⟨.hall 3 13, 1985604192⟩, ⟨.hall 2 15, 5101616520⟩, ⟨.assumptionRow 10, 1176789600⟩]
  caps := #[0, 757648320, 267764640, 0, 147315168, 0, 14272944, 0, 20407815, 0, 4361280, 87360, 0, 0, 0, 0] }

theorem case_33_18_10_checked :
    (Witness.linear .conditional case_33_18_10).check 33 18 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_18_11 : Certificate := {
  objectiveScale := 193265800000
  eta := 300967032366000
  rows := #[⟨.count 2, 81300185366400⟩, ⟨.count 3, 23055096944880⟩, ⟨.count 4, 6987486345840⟩, ⟨.count 5, 2306931026400⟩, ⟨.count 6, 856079143920⟩, ⟨.count 7, 359706306960⟩, ⟨.count 8, 165822056400⟩, ⟨.count 9, 111519888480⟩, ⟨.count 10, 114799885200⟩, ⟨.count 12, 180399819600⟩, ⟨.path 8, 54118864800⟩, ⟨.privateRow 2 16, 4924915075080⟩, ⟨.privateRow 5 9, 1749331584⟩, ⟨.privateRow 5 10, 560879439120⟩, ⟨.privateRow 6 8, 233207766792⟩, ⟨.privateRow 6 9, 608712724620⟩, ⟨.privateRow 7 6, 94876942160⟩, ⟨.privateRow 7 7, 293231706768⟩, ⟨.privateRow 7 8, 439064005380⟩, ⟨.privateRow 8 4, 37674406770⟩, ⟨.privateRow 8 5, 137494121765⟩, ⟨.privateRow 8 6, 273415059918⟩, ⟨.privateRow 9 2, 11571099540⟩, ⟨.privateRow 9 3, 81323093280⟩, ⟨.privateRow 9 4, 71613261720⟩, ⟨.privateRow 10 1, 47628285705⟩, ⟨.privateRow 10 2, 2030474160⟩, ⟨.privateRow 11 0, 13393319940⟩, ⟨.hall 6 10, 15008469840⟩, ⟨.hall 5 11, 287735609700⟩, ⟨.hall 6 11, 592039407960⟩, ⟨.hall 4 12, 568094230440⟩, ⟨.hall 3 13, 791010256608⟩, ⟨.hall 2 15, 9732570267420⟩, ⟨.assumptionRow 11, 112204601600⟩]
  caps := #[0, 0, 76506029600, 8203134940, 10179160992, 0, 61810980, 388996608, 1441924211, 684713120, 0, 2711243080, 12865980400, 0, 0, 0] }

theorem case_33_18_11_checked :
    (Witness.linear .conditional case_33_18_11).check 33 18 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_19_1_checked :
    (Witness.rising).check 33 19 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_19_2_checked :
    (Witness.rising).check 33 19 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_19_3_checked :
    (Witness.rising).check 33 19 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_19_4_checked :
    (Witness.rising).check 33 19 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_19_5_checked :
    (Witness.rising).check 33 19 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_19_6_checked :
    (Witness.rising).check 33 19 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_19_7_checked :
    (Witness.rising).check 33 19 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_19_8 : Certificate := {
  objectiveScale := 3267000000
  eta := 8224424208000
  rows := #[⟨.count 2, 1315241928000⟩, ⟨.count 3, 220594374000⟩, ⟨.count 4, 45102657600⟩, ⟨.count 5, 11351340000⟩, ⟨.count 6, 4136932800⟩, ⟨.count 7, 3266663400⟩, ⟨.path 8, 853966575⟩, ⟨.path 9, 556920000⟩, ⟨.privateRow 3 16, 11376565200⟩, ⟨.privateRow 5 10, 3977509536⟩, ⟨.privateRow 6 8, 2062860800⟩, ⟨.privateRow 9 0, 50450400⟩, ⟨.privateRow 9 6, 50450400⟩, ⟨.privateRow 10 8, 741620880⟩, ⟨.privateRow 12 6, 3607203600⟩, ⟨.hall 9 1, 81729648⟩, ⟨.hall 10 1, 201801600⟩, ⟨.hall 7 2, 23696400⟩, ⟨.hall 6 3, 23814000⟩, ⟨.hall 11 5, 74324250⟩, ⟨.hall 8 6, 1703520⟩, ⟨.hall 7 8, 9096360⟩, ⟨.hall 8 8, 18957120⟩, ⟨.hall 10 8, 1513512000⟩, ⟨.hall 9 9, 529729200⟩, ⟨.hall 3 13, 44594550⟩]
  caps := #[0, 1493434800, 4751346600, 42233400, 195810615, 0, 0, 85625100, 0, 27190800, 75675600, 0, 0, 0, 0] }

theorem case_33_19_8_checked :
    (Witness.linear .positive case_33_19_8).check 33 19 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_19_9 : Certificate := {
  objectiveScale := 2200000
  eta := 9842512680
  rows := #[⟨.count 2, 2164322160⟩, ⟨.count 3, 471711240⟩, ⟨.count 4, 115675560⟩, ⟨.count 5, 28828800⟩, ⟨.count 6, 8288280⟩, ⟨.count 7, 3048045⟩, ⟨.count 8, 2162160⟩, ⟨.path 9, 825000⟩, ⟨.privateRow 10 5, 144144⟩, ⟨.hall 6 6, 19140⟩, ⟨.hall 8 7, 11466⟩]
  caps := #[0, 3037320, 0, 188760, 0, 46200, 0, 0, 47960, 0, 0, 0, 0, 0, 0] }

theorem case_33_19_9_checked :
    (Witness.linear .positive case_33_19_9).check 33 19 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_19_10 : Certificate := {
  objectiveScale := 1836000000
  eta := 7437538508400
  rows := #[⟨.count 2, 1710290181600⟩, ⟨.count 3, 432626594400⟩, ⟨.count 4, 117621504000⟩, ⟨.count 5, 35654018400⟩, ⟨.count 6, 12864852000⟩, ⟨.count 7, 5574769200⟩, ⟨.count 8, 3308104800⟩, ⟨.count 9, 2756754000⟩, ⟨.path 9, 673567200⟩, ⟨.privateRow 4 12, 5858102250⟩, ⟨.privateRow 4 13, 20399979600⟩, ⟨.privateRow 5 10, 5469399936⟩, ⟨.privateRow 5 11, 9630260640⟩, ⟨.privateRow 5 12, 15229534320⟩, ⟨.privateRow 6 7, 236293200⟩, ⟨.privateRow 6 8, 3226423200⟩, ⟨.privateRow 6 9, 5252126880⟩, ⟨.privateRow 6 10, 7387079700⟩, ⟨.privateRow 6 11, 2001199200⟩, ⟨.privateRow 7 5, 363738375⟩, ⟨.privateRow 7 6, 1754695800⟩, ⟨.privateRow 7 7, 2991588600⟩, ⟨.privateRow 7 8, 1681619940⟩, ⟨.privateRow 8 3, 340340000⟩, ⟨.privateRow 8 4, 1133332200⟩, ⟨.privateRow 8 5, 743886000⟩, ⟨.privateRow 9 1, 306306000⟩, ⟨.privateRow 9 2, 319919600⟩, ⟨.privateRow 10 0, 213188976⟩, ⟨.privateRow 11 0, 204204000⟩, ⟨.hall 4 14, 17716739040⟩, ⟨.hall 3 15, 64439124750⟩, ⟨.hall 2 16, 100605304800⟩, ⟨.assumptionRow 10, 2694513600⟩]
  caps := #[0, 10248123600, 0, 133293600, 89047530, 0, 0, 81002790, 59976000, 114416800, 0, 0, 0, 0, 0] }

theorem case_33_19_10_checked :
    (Witness.linear .conditional case_33_19_10).check 33 19 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_19_11 : Certificate := {
  objectiveScale := 30670584000000
  eta := 153252110390979600
  rows := #[⟨.count 2, 33781029008126400⟩, ⟨.count 3, 8564663202895800⟩, ⟨.count 4, 2210490330048000⟩, ⟨.count 5, 588148319959200⟩, ⟨.count 6, 168418310860800⟩, ⟨.count 7, 55262258251200⟩, ⟨.count 8, 21052288857600⟩, ⟨.count 9, 17762868723600⟩, ⟨.count 10, 19736520804000⟩, ⟨.count 12, 43420345768800⟩, ⟨.path 7, 21467578532400⟩, ⟨.privateRow 2 17, 1259190027295200⟩, ⟨.privateRow 4 12, 141116123748600⟩, ⟨.privateRow 4 13, 497031382247400⟩, ⟨.privateRow 5 10, 103340422929744⟩, ⟨.privateRow 5 11, 225785797997760⟩, ⟨.privateRow 5 12, 403677638844480⟩, ⟨.privateRow 6 8, 54421628661400⟩, ⟨.privateRow 6 9, 113199911544720⟩, ⟨.privateRow 6 10, 198187563073500⟩, ⟨.privateRow 6 11, 203797851857600⟩, ⟨.privateRow 7 6, 25211055741300⟩, ⟨.privateRow 7 7, 36402916149600⟩, ⟨.privateRow 7 8, 155096159318100⟩, ⟨.privateRow 7 9, 19942109562375⟩, ⟨.privateRow 8 4, 10608379932150⟩, ⟨.privateRow 8 5, 32894201340000⟩, ⟨.privateRow 8 6, 46545294896100⟩, ⟨.privateRow 9 2, 3289420134000⟩, ⟨.privateRow 9 3, 19297931452800⟩, ⟨.privateRow 9 4, 8176558618800⟩, ⟨.privateRow 10 1, 8815645959120⟩, ⟨.privateRow 11 0, 2192946756000⟩, ⟨.hall 4 13, 26296564385520⟩, ⟨.hall 5 13, 8881434361800⟩, ⟨.hall 4 14, 350520609479040⟩, ⟨.hall 3 15, 1907781442216650⟩, ⟨.hall 2 16, 3018991099924800⟩, ⟨.assumptionRow 11, 21475542916800⟩]
  caps := #[0, 32828044813200, 3626213791200, 16043069842800, 0, 3923490707136, 390980970200, 0, 423254059200, 2684990553600, 1739022112800, 0, 0, 0, 0] }

theorem case_33_19_11_checked :
    (Witness.linear .conditional case_33_19_11).check 33 19 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_19_12 : Certificate := {
  objectiveScale := 344657620641600000
  eta := 2332856119569525950400
  rows := #[⟨.count 2, 502569747348582513600⟩, ⟨.count 3, 122254021604212898400⟩, ⟨.count 4, 29473051771545782400⟩, ⟨.count 5, 6973974624872455200⟩, ⟨.count 6, 1626439311807710400⟩, ⟨.count 7, 301876993479461400⟩, ⟨.path 6, 117690847206332400⟩, ⟨.path 7, 301851560310300000⟩, ⟨.privateRow 2 17, 22228003928038708800⟩, ⟨.privateRow 4 12, 1872869510566454400⟩, ⟨.privateRow 4 13, 7364155772907133200⟩, ⟨.privateRow 5 10, 1296222845470993440⟩, ⟨.privateRow 5 11, 3162931601068479240⟩, ⟨.privateRow 5 12, 6415399507685968800⟩, ⟨.privateRow 6 8, 628397006834797200⟩, ⟨.privateRow 6 9, 1470914475257747520⟩, ⟨.privateRow 6 10, 2980436348321031600⟩, ⟨.privateRow 6 11, 3713794365738256800⟩, ⟨.privateRow 7 5, 5390660597847525⟩, ⟨.privateRow 7 6, 250830738022293000⟩, ⟨.privateRow 7 7, 701983802297477700⟩, ⟨.privateRow 7 8, 1522527911331106680⟩, ⟨.privateRow 7 9, 2026888384790669400⟩, ⟨.privateRow 8 3, 1597232769732600⟩, ⟨.privateRow 8 4, 88047456431509575⟩, ⟨.privateRow 8 5, 326813382639572400⟩, ⟨.privateRow 8 6, 847788336563067900⟩, ⟨.privateRow 8 7, 654682894702396560⟩, ⟨.privateRow 9 1, 547622663908320⟩, ⟨.privateRow 9 2, 15820210290684800⟩, ⟨.privateRow 9 3, 110209061111549400⟩, ⟨.privateRow 9 4, 567180616190760000⟩, ⟨.privateRow 9 5, 56131323050602800⟩, ⟨.privateRow 10 0, 4435743577657392⟩, ⟨.privateRow 10 1, 21904906556332800⟩, ⟨.privateRow 10 2, 245198047764950280⟩, ⟨.privateRow 11 0, 69821889648310800⟩, ⟨.privateRow 11 1, 16942076164663650⟩, ⟨.privateRow 12 0, 22589434886218200⟩, ⟨.hall 5 13, 2518868674455447600⟩, ⟨.hall 4 14, 13763948034671714880⟩, ⟨.hall 3 15, 31749450732579680100⟩, ⟨.hall 2 16, 47900232281081980800⟩]
  caps := #[0, 0, 49175875584763200, 0, 0, 24257451660361920, 1813314997664640, 373875023271750, 14064863178087645, 4480670640693760, 12288767463976248, 0, 147843758521053000, 344657620641600000, 0] }

theorem case_33_19_12_checked :
    (Witness.linear .negative case_33_19_12).check 33 19 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_20_1_checked :
    (Witness.rising).check 33 20 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_20_2_checked :
    (Witness.rising).check 33 20 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_20_3_checked :
    (Witness.rising).check 33 20 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_20_4_checked :
    (Witness.rising).check 33 20 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_20_5_checked :
    (Witness.rising).check 33 20 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_20_6_checked :
    (Witness.rising).check 33 20 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_20_7_checked :
    (Witness.rising).check 33 20 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_20_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_33_20_8_checked :
    (Witness.linear .positive case_33_20_8).check 33 20 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_20_9 : Certificate := {
  objectiveScale := 100980000
  eta := 936818522640
  rows := #[⟨.count 2, 192458185920⟩, ⟨.count 3, 43290226980⟩, ⟨.count 4, 9905936040⟩, ⟨.count 5, 2358556200⟩, ⟨.count 6, 675404730⟩, ⟨.count 7, 235855620⟩, ⟨.count 8, 171531360⟩, ⟨.path 8, 67318020⟩, ⟨.hall 5 9, 2118676⟩, ⟨.hall 7 10, 6909735⟩]
  caps := #[0, 414825840, 67104180, 27644760, 0, 3183180, 0, 4131270, 0, 0, 0, 0, 0, 0] }

theorem case_33_20_9_checked :
    (Witness.linear .positive case_33_20_9).check 33 20 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_20_10 : Certificate := {
  objectiveScale := 4133601000
  eta := 35336253492540
  rows := #[⟨.count 2, 8840959597470⟩, ⟨.count 3, 2192999338530⟩, ⟨.count 4, 535648551984⟩, ⟨.count 5, 148791264440⟩, ⟨.count 6, 42631204980⟩, ⟨.count 7, 13165519185⟩, ⟨.count 8, 5015435880⟩, ⟨.count 9, 4513892292⟩, ⟨.path 7, 1417584168⟩, ⟨.path 8, 915471045⟩]
  caps := #[0, 16161476292, 0, 0, 358280586, 37884784, 274370703, 181151163, 33636165, 0, 0, 0, 0, 0] }

theorem case_33_20_10_checked :
    (Witness.linear .positive case_33_20_10).check 33 20 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_20_11 : Certificate := {
  objectiveScale := 324074318400000
  eta := 2564647350204139200
  rows := #[⟨.count 2, 565078828801687200⟩, ⟨.count 3, 127419054397034400⟩, ⟨.count 4, 33033024904239360⟩, ⟨.count 5, 8805099230928000⟩, ⟨.count 6, 2467744916036400⟩, ⟨.count 7, 764653354264800⟩, ⟨.count 8, 278055765187200⟩, ⟨.count 9, 83416729556160⟩, ⟨.count 10, 208541823890400⟩, ⟨.path 7, 275951075400000⟩, ⟨.privateRow 2 18, 43202914515961200⟩, ⟨.privateRow 3 15, 7878246680304000⟩, ⟨.privateRow 3 16, 21618835743304800⟩, ⟨.privateRow 4 13, 6798463458827040⟩, ⟨.privateRow 4 14, 10183792399981200⟩, ⟨.privateRow 4 15, 14107854386185560⟩, ⟨.privateRow 5 10, 603998912156640⟩, ⟨.privateRow 5 11, 3218032055766528⟩, ⟨.privateRow 5 12, 5123177473574160⟩, ⟨.privateRow 5 13, 7158391199319360⟩, ⟨.privateRow 5 14, 3582285108161760⟩, ⟨.privateRow 6 8, 537905498130000⟩, ⟨.privateRow 6 9, 1557305379329700⟩, ⟨.privateRow 6 10, 2585918616240960⟩, ⟨.privateRow 6 11, 3519143278150500⟩, ⟨.privateRow 7 6, 338880463821900⟩, ⟨.privateRow 7 7, 876726851457600⟩, ⟨.privateRow 7 8, 1428345984265200⟩, ⟨.privateRow 7 9, 613708796020320⟩, ⟨.privateRow 8 4, 185370510124800⟩, ⟨.privateRow 8 5, 569869497922725⟩, ⟨.privateRow 8 6, 407980631658600⟩, ⟨.privateRow 9 2, 85270434657408⟩, ⟨.privateRow 9 3, 286294454526080⟩, ⟨.privateRow 10 1, 104270911945200⟩, ⟨.privateRow 11 0, 20854182389040⟩, ⟨.hall 3 16, 7482971327832000⟩, ⟨.hall 2 17, 21835101338450400⟩, ⟨.assumptionRow 11, 269259462259200⟩]
  caps := #[0, 0, 0, 28276577128800, 8881867088640, 0, 0, 7140191521320, 501302461275, 15301863388224, 0, 237916846036800, 324074318400000, 0] }

theorem case_33_20_11_checked :
    (Witness.linear .conditional case_33_20_11).check 33 20 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_20_12 : Certificate := {
  objectiveScale := 89429508000000
  eta := 983357855473593600
  rows := #[⟨.count 2, 201039924732847200⟩, ⟨.count 3, 41350076076909600⟩, ⟨.count 4, 8504810600045760⟩, ⟨.count 5, 1613614371969600⟩, ⟨.count 6, 246390218474400⟩, ⟨.count 7, 7246771131600⟩, ⟨.path 6, 226390262258160⟩, ⟨.privateRow 2 18, 23436057839594400⟩, ⟨.privateRow 3 15, 4406036848012800⟩, ⟨.privateRow 3 16, 8601917333209200⟩, ⟨.privateRow 4 12, 393064866177984⟩, ⟨.privateRow 4 13, 2570792058935100⟩, ⟨.privateRow 4 14, 3982825413927360⟩, ⟨.privateRow 4 15, 5715528391492920⟩, ⟨.privateRow 5 10, 388426932653760⟩, ⟨.privateRow 5 11, 1108466112289536⟩, ⟨.privateRow 5 12, 1857589000066800⟩, ⟨.privateRow 5 13, 2896775980338240⟩, ⟨.privateRow 5 14, 2159537797216800⟩, ⟨.privateRow 6 7, 5133129551550⟩, ⟨.privateRow 6 8, 219991266495000⟩, ⟨.privateRow 6 9, 514923348739800⟩, ⟨.privateRow 6 10, 654383433183480⟩, ⟨.privateRow 6 11, 1961157437489250⟩, ⟨.privateRow 6 12, 314429347432200⟩, ⟨.privateRow 7 5, 3910955848800⟩, ⟨.privateRow 7 6, 101584202469750⟩, ⟨.privateRow 7 7, 269017891599600⟩, ⟨.privateRow 7 8, 473110629591600⟩, ⟨.privateRow 7 9, 684923397238080⟩, ⟨.privateRow 8 4, 43078028393400⟩, ⟨.privateRow 8 5, 150823424176425⟩, ⟨.privateRow 8 6, 298670495923800⟩, ⟨.privateRow 8 7, 119773022869500⟩, ⟨.privateRow 9 2, 13334058882144⟩, ⟨.privateRow 9 3, 87390691868480⟩, ⟨.privateRow 9 4, 127301612878440⟩, ⟨.privateRow 10 1, 50437527075936⟩, ⟨.privateRow 10 2, 26571494149200⟩, ⟨.privateRow 11 0, 23189667621120⟩, ⟨.privateRow 12 0, 8857164716400⟩, ⟨.hall 4 15, 30436438752720⟩, ⟨.hall 3 16, 3506584666384800⟩, ⟨.hall 2 17, 9477166246548000⟩, ⟨.assumptionRow 12, 19263910952160⟩]
  caps := #[0, 810431939903040, 63598871765520, 0, 0, 5621151279744, 0, 501924127590, 11781695939475, 282738565984, 0, 100947631165920, 0, 89429508000000] }

theorem case_33_20_12_checked :
    (Witness.linear .conditional case_33_20_12).check 33 20 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_21_1_checked :
    (Witness.rising).check 33 21 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_21_2_checked :
    (Witness.rising).check 33 21 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_21_3_checked :
    (Witness.rising).check 33 21 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_21_4_checked :
    (Witness.rising).check 33 21 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_21_5_checked :
    (Witness.rising).check 33 21 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_21_6_checked :
    (Witness.rising).check 33 21 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_21_7_checked :
    (Witness.rising).check 33 21 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_21_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_33_21_8_checked :
    (Witness.linear .positive case_33_21_8).check 33 21 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_21_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_33_21_9_checked :
    (Witness.linear .positive case_33_21_9).check 33 21 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_21_10 : Certificate := {
  objectiveScale := 1472780000
  eta := 73119252256050
  rows := #[⟨.count 2, 9952010402880⟩, ⟨.count 3, 1435386115800⟩, ⟨.count 4, 240598053696⟩, ⟨.count 5, 52402985180⟩, ⟨.count 6, 11229211110⟩, ⟨.count 7, 2847988325⟩, ⟨.count 8, 1822712528⟩, ⟨.count 9, 2050551594⟩, ⟨.path 3, 302600514216⟩, ⟨.path 6, 3963168690⟩]
  caps := #[0, 0, 0, 680643756, 0, 0, 97857580, 97571675, 0, 0, 0, 0, 0] }

theorem case_33_21_10_checked :
    (Witness.linear .positive case_33_21_10).check 33 21 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_21_11 : Certificate := {
  objectiveScale := 4142717250000
  eta := 76477576333158000
  rows := #[⟨.count 2, 17368471323403200⟩, ⟨.count 3, 1898930116203120⟩, ⟨.count 4, 593735561939520⟩, ⟨.count 5, 123694908737400⟩, ⟨.count 6, 25592050083600⟩, ⟨.count 7, 7108902801000⟩, ⟨.count 8, 4549697792640⟩, ⟨.path 6, 12560322574800⟩, ⟨.privateRow 2 19, 1322255920986000⟩, ⟨.privateRow 3 0, 20832826734720⟩, ⟨.privateRow 3 16, 406060527993120⟩, ⟨.privateRow 3 17, 512694070008120⟩, ⟨.privateRow 4 13, 93268804749120⟩, ⟨.privateRow 4 14, 206442537341040⟩, ⟨.privateRow 4 15, 246631534509360⟩, ⟨.privateRow 4 16, 269569594213920⟩, ⟨.privateRow 5 10, 11130510671280⟩, ⟨.privateRow 5 11, 63221842243560⟩, ⟨.privateRow 5 12, 97989116208984⟩, ⟨.privateRow 5 13, 121420059841080⟩, ⟨.privateRow 5 14, 75733511173320⟩, ⟨.privateRow 6 8, 12034356884550⟩, ⟨.privateRow 6 9, 35486482145400⟩, ⟨.privateRow 6 10, 54636995813400⟩, ⟨.privateRow 6 11, 43425240538680⟩, ⟨.privateRow 7 6, 9094881996200⟩, ⟨.privateRow 7 7, 22418432761725⟩, ⟨.privateRow 7 8, 22052106648000⟩, ⟨.privateRow 8 4, 6426448132104⟩, ⟨.privateRow 8 5, 11627005470080⟩, ⟨.privateRow 9 2, 4911605571600⟩, ⟨.privateRow 9 3, 454969779264⟩, ⟨.privateRow 10 0, 1421780560200⟩, ⟨.hall 3 17, 22179776739120⟩, ⟨.hall 2 18, 358288701170400⟩, ⟨.assumptionRow 11, 3763536777000⟩]
  caps := #[0, 9037359895200, 0, 3832594605840, 0, 826089960696, 126517234200, 38990280000, 0, 1667941793952, 0, 33520918473000, 4142717250000] }

theorem case_33_21_11_checked :
    (Witness.linear .conditional case_33_21_11).check 33 21 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_21_12 : Certificate := {
  objectiveScale := 35592555600000
  eta := 987220357243520400
  rows := #[⟨.count 2, 163248174848959200⟩, ⟨.count 3, 26763864894486720⟩, ⟨.count 4, 4294379457688320⟩, ⟨.count 5, 534422222334000⟩, ⟨.count 6, 50897354508000⟩, ⟨.count 7, 11876049385200⟩, ⟨.path 5, 378934388632800⟩, ⟨.path 6, 15035866045200⟩, ⟨.privateRow 2 19, 15676385188464000⟩, ⟨.privateRow 3 15, 416849333420520⟩, ⟨.privateRow 3 16, 4363260544122480⟩, ⟨.privateRow 3 17, 5896458519751800⟩, ⟨.privateRow 4 13, 995212938479760⟩, ⟨.privateRow 4 14, 2117499605381160⟩, ⟨.privateRow 4 15, 2797997235153120⟩, ⟨.privateRow 4 16, 3439303901953920⟩, ⟨.privateRow 5 10, 106545128770080⟩, ⟨.privateRow 5 11, 572227646210220⟩, ⟨.privateRow 5 12, 974548612549512⟩, ⟨.privateRow 5 13, 1350900617566500⟩, ⟨.privateRow 5 14, 1638103078531920⟩, ⟨.privateRow 6 8, 88010008836750⟩, ⟨.privateRow 6 9, 292538604243600⟩, ⟨.privateRow 6 10, 516325385175600⟩, ⟨.privateRow 6 11, 716974067169360⟩, ⟨.privateRow 6 12, 369854109424800⟩, ⟨.privateRow 7 6, 52216915550800⟩, ⟨.privateRow 7 7, 168279378342075⟩, ⟨.privateRow 7 8, 315321229594800⟩, ⟨.privateRow 7 9, 255617824862400⟩, ⟨.privateRow 8 4, 29808883956852⟩, ⟨.privateRow 8 5, 114273986306480⟩, ⟨.privateRow 8 6, 155576246946120⟩, ⟨.privateRow 9 2, 18785750845680⟩, ⟨.privateRow 9 3, 85507555573440⟩, ⟨.privateRow 10 0, 19001679016320⟩, ⟨.privateRow 10 1, 14251259262240⟩, ⟨.privateRow 11 0, 9716767678800⟩, ⟨.hall 3 17, 694748889034200⟩, ⟨.hall 2 18, 4515398987299200⟩, ⟨.assumptionRow 12, 14305241304900⟩]
  caps := #[0, 12483233380800, 29416150272600, 13170485568240, 0, 5595665803728, 128023000350, 2429191919700, 21592817064, 18174745307880, 0, 38431061909100, 270435203495100] }

theorem case_33_21_12_checked :
    (Witness.linear .conditional case_33_21_12).check 33 21 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_21_13 : Certificate := {
  objectiveScale := 13608487200000
  eta := 646989218718242400
  rows := #[⟨.count 2, 86994241265131200⟩, ⟨.count 3, 12180276468360000⟩, ⟨.count 4, 1811703344330880⟩, ⟨.count 5, 329318585996400⟩, ⟨.count 6, 42534298778400⟩, ⟨.path 3, 2708164850751360⟩, ⟨.path 6, 43032877430400⟩, ⟨.privateRow 6 8, 483344304300⟩, ⟨.privateRow 6 12, 838763482728600⟩, ⟨.privateRow 7 6, 1933377217200⟩, ⟨.privateRow 7 7, 7894623636900⟩, ⟨.privateRow 8 4, 270672810408⟩, ⟨.privateRow 8 5, 2004983780800⟩, ⟨.privateRow 9 2, 164044127520⟩, ⟨.privateRow 9 4, 1002491890400⟩, ⟨.privateRow 10 1, 492132382560⟩, ⟨.privateRow 10 2, 541345620816⟩, ⟨.privateRow 10 8, 14887004572440⟩, ⟨.privateRow 11 0, 2460661912800⟩, ⟨.hall 8 4, 1254306636576⟩, ⟨.hall 7 5, 905397396120⟩, ⟨.hall 9 6, 515567257920⟩, ⟨.hall 6 7, 603698413120⟩, ⟨.hall 10 7, 820220637600⟩, ⟨.hall 5 10, 434615537025⟩, ⟨.hall 4 12, 2779397425728⟩, ⟨.hall 3 14, 8775637098228⟩]
  caps := #[0, 35259219182880, 0, 4725989885760, 2299755237120, 1528490256150, 4445890470450, 80219381040, 0, 5951939922880, 0, 84937991426400, 367429154400000] }

theorem case_33_21_13_checked :
    (Witness.linear .negative case_33_21_13).check 33 21 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_22_1_checked :
    (Witness.rising).check 33 22 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_22_2_checked :
    (Witness.rising).check 33 22 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_22_3_checked :
    (Witness.rising).check 33 22 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_22_4_checked :
    (Witness.rising).check 33 22 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_22_5_checked :
    (Witness.rising).check 33 22 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_22_6_checked :
    (Witness.rising).check 33 22 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_22_7_checked :
    (Witness.rising).check 33 22 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_22_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_33_22_8_checked :
    (Witness.linear .positive case_33_22_8).check 33 22 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_22_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_33_22_9_checked :
    (Witness.linear .positive case_33_22_9).check 33 22 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_22_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_33_22_10_checked :
    (Witness.linear .positive case_33_22_10).check 33 22 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_22_11 : Certificate := {
  objectiveScale := 17571400000
  eta := 873178672766400
  rows := #[⟨.count 2, 133367347713600⟩, ⟨.count 3, 20927769342480⟩, ⟨.count 4, 3271274566560⟩, ⟨.count 5, 434372538600⟩, ⟨.count 6, 59913453600⟩, ⟨.count 7, 41939417520⟩, ⟨.path 5, 301445944800⟩, ⟨.privateRow 2 20, 9121823310600⟩, ⟨.privateRow 3 16, 1534283690940⟩, ⟨.privateRow 3 17, 3303894113520⟩, ⟨.privateRow 3 18, 3453012042480⟩, ⟨.privateRow 4 13, 452596214070⟩, ⟨.privateRow 4 14, 1279152234360⟩, ⟨.privateRow 4 15, 1609425147330⟩, ⟨.privateRow 4 16, 1586707962840⟩, ⟨.privateRow 4 17, 395803252845⟩, ⟨.privateRow 5 10, 78636407850⟩, ⟨.privateRow 5 11, 403559905320⟩, ⟨.privateRow 5 12, 693498225420⟩, ⟨.privateRow 5 13, 819016910712⟩, ⟨.privateRow 5 14, 184233869820⟩, ⟨.privateRow 6 7, 499278780⟩, ⟨.privateRow 6 8, 93476082700⟩, ⟨.privateRow 6 9, 283340707650⟩, ⟨.privateRow 6 10, 420107430600⟩, ⟨.privateRow 6 11, 18722954250⟩, ⟨.privateRow 7 6, 89271045864⟩, ⟨.privateRow 7 7, 197048691840⟩, ⟨.privateRow 8 4, 91504183680⟩, ⟨.privateRow 9 2, 26794627860⟩, ⟨.privateRow 10 0, 4839163560⟩, ⟨.hall 2 19, 1365128040276⟩, ⟨.assumptionRow 11, 17389360296⟩]
  caps := #[0, 125999857984, 5333127800, 69805844108, 0, 7381178640, 6810610092, 0, 17389360296, 0, 172033845984, 158324639704] }

theorem case_33_22_11_checked :
    (Witness.linear .conditional case_33_22_11).check 33 22 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_22_12 : Certificate := {
  objectiveScale := 1263087000000
  eta := 95407351824985200
  rows := #[⟨.count 2, 12318613471644480⟩, ⟨.count 3, 1478783861755200⟩, ⟨.count 4, 144439353938880⟩, ⟨.count 5, 7983467692200⟩, ⟨.count 6, 2456451597600⟩, ⟨.count 7, 859758059160⟩, ⟨.path 4, 107909693325720⟩, ⟨.path 5, 2848836390400⟩, ⟨.privateRow 2 20, 907904510472960⟩, ⟨.privateRow 3 16, 142003372771260⟩, ⟨.privateRow 3 17, 293464084193280⟩, ⟨.privateRow 3 18, 338458089289320⟩, ⟨.privateRow 4 13, 35142610668165⟩, ⟨.privateRow 4 14, 102870051778494⟩, ⟨.privateRow 4 15, 141107791459635⟩, ⟨.privateRow 4 16, 159843352498830⟩, ⟨.privateRow 4 17, 106072650548865⟩, ⟨.privateRow 5 10, 4237379005860⟩, ⟨.privateRow 5 11, 27143790153480⟩, ⟨.privateRow 5 12, 53202647518020⟩, ⟨.privateRow 5 13, 71703822133944⟩, ⟨.privateRow 5 14, 73877781797820⟩, ⟨.privateRow 6 8, 3809774468500⟩, ⟨.privateRow 6 9, 17860450157550⟩, ⟨.privateRow 6 10, 31100431833900⟩, ⟨.privateRow 6 11, 40190277527400⟩, ⟨.privateRow 7 6, 3070564497000⟩, ⟨.privateRow 7 7, 13060134327240⟩, ⟨.privateRow 7 8, 19820493828135⟩, ⟨.privateRow 8 4, 2872373515830⟩, ⟨.privateRow 8 5, 10252614855483⟩, ⟨.privateRow 9 2, 3582325246500⟩, ⟨.privateRow 9 3, 833704784640⟩, ⟨.privateRow 10 0, 1388839941720⟩, ⟨.hall 2 19, 158625361915020⟩, ⟨.assumptionRow 12, 691033962080⟩]
  caps := #[0, 0, 2986094221760, 0, 0, 2991724736, 0, 447339102210, 0, 139437319840, 0, 48665488379200] }

theorem case_33_22_12_checked :
    (Witness.linear .conditional case_33_22_12).check 33 22 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_22_13 : Certificate := {
  objectiveScale := 948855600000
  eta := 73557124994152800
  rows := #[⟨.count 2, 11398127135915520⟩, ⟨.count 3, 1727568486483840⟩, ⟨.count 4, 238257830931120⟩, ⟨.count 5, 24474645795600⟩, ⟨.path 5, 24671096850400⟩, ⟨.privateRow 3 17, 420736236560640⟩, ⟨.privateRow 4 13, 10790662632750⟩, ⟨.privateRow 4 14, 64425236223348⟩, ⟨.privateRow 4 15, 163802258765145⟩, ⟨.privateRow 5 11, 17237956507200⟩, ⟨.privateRow 5 13, 151970475056400⟩, ⟨.privateRow 5 14, 65768495853060⟩, ⟨.privateRow 5 16, 137171852017200⟩, ⟨.privateRow 6 7, 113835561840⟩, ⟨.privateRow 6 11, 7462553498400⟩, ⟨.privateRow 6 14, 295845976826400⟩, ⟨.privateRow 7 6, 79684893288⟩, ⟨.privateRow 7 7, 101187166080⟩, ⟨.hall 9 4, 56838175632⟩, ⟨.hall 10 4, 48293874720⟩, ⟨.hall 7 5, 79472612520⟩, ⟨.hall 8 5, 53866244880⟩, ⟨.hall 6 6, 45602457840⟩, ⟨.hall 6 7, 15602636448⟩, ⟨.hall 3 15, 633202970400⟩, ⟨.hall 2 18, 30938708304504⟩]
  caps := #[0, 2285426035200, 1064172389280, 0, 196926265536, 196451054800, 196578782400, 118158728688, 491760228960, 91279908720, 3491788608000, 0] }

theorem case_33_22_13_checked :
    (Witness.linear .negative case_33_22_13).check 33 22 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_22_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 429, 429, 297, 165] }

theorem case_33_22_14_checked :
    (Witness.linear .negative case_33_22_14).check 33 22 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_23_1_checked :
    (Witness.rising).check 33 23 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_23_2_checked :
    (Witness.rising).check 33 23 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_23_3_checked :
    (Witness.rising).check 33 23 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_23_4_checked :
    (Witness.rising).check 33 23 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_23_5_checked :
    (Witness.rising).check 33 23 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_23_6_checked :
    (Witness.rising).check 33 23 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_23_7_checked :
    (Witness.rising).check 33 23 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_23_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_33_23_8_checked :
    (Witness.linear .positive case_33_23_8).check 33 23 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_23_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_33_23_9_checked :
    (Witness.linear .positive case_33_23_9).check 33 23 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_23_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_33_23_10_checked :
    (Witness.linear .positive case_33_23_10).check 33 23 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_23_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_33_23_11_checked :
    (Witness.linear .positive case_33_23_11).check 33 23 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_23_12 : Certificate := {
  objectiveScale := 22037400000
  eta := 1790886200463360
  rows := #[⟨.count 2, 230251862000160⟩, ⟨.count 3, 27140527994580⟩, ⟨.count 4, 2516953158720⟩, ⟨.count 5, 61690028400⟩, ⟨.path 4, 2164691456928⟩, ⟨.privateRow 2 20, 23016549596040⟩, ⟨.privateRow 2 21, 23059732615920⟩, ⟨.privateRow 3 16, 2483023643100⟩, ⟨.privateRow 3 17, 6310118779965⟩, ⟨.privateRow 3 18, 11594640837780⟩, ⟨.privateRow 3 19, 8237161042110⟩, ⟨.privateRow 4 13, 939891646980⟩, ⟨.privateRow 4 14, 1705729285260⟩, ⟨.privateRow 4 15, 4060437669288⟩, ⟨.privateRow 4 16, 4675333027365⟩, ⟨.privateRow 4 17, 2708192246760⟩, ⟨.privateRow 5 10, 210431541320⟩, ⟨.privateRow 5 11, 540558873855⟩, ⟨.privateRow 5 12, 1337792330160⟩, ⟨.privateRow 5 13, 2163263662560⟩, ⟨.privateRow 5 14, 1492898687280⟩, ⟨.privateRow 6 7, 26919285120⟩, ⟨.privateRow 6 8, 146822267592⟩, ⟨.privateRow 6 9, 514083570000⟩, ⟨.privateRow 6 10, 987811579755⟩, ⟨.privateRow 6 11, 536703247080⟩, ⟨.privateRow 7 4, 2847232080⟩, ⟨.privateRow 7 5, 21591509940⟩, ⟨.privateRow 7 6, 186752540520⟩, ⟨.privateRow 7 7, 545956751340⟩, ⟨.privateRow 7 8, 45239354160⟩, ⟨.privateRow 8 1, 1439433996⟩, ⟨.privateRow 8 2, 4626752130⟩, ⟨.privateRow 8 3, 38200363740⟩, ⟨.privateRow 8 4, 233908024350⟩, ⟨.privateRow 9 0, 23030943936⟩, ⟨.privateRow 9 1, 61690028400⟩, ⟨.hall 2 20, 1217349893760⟩, ⟨.assumptionRow 12, 14782687920⟩]
  caps := #[0, 68441012640, 104717853240, 16731965250, 16622635887, 11608754300, 402906000, 13990209660, 0, 0, 3622904485200] }

theorem case_33_23_12_checked :
    (Witness.linear .conditional case_33_23_12).check 33 23 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_23_13 : Certificate := {
  objectiveScale := 251697600000
  eta := 47780196180837120
  rows := #[⟨.count 2, 4475879271864000⟩, ⟨.count 3, 313496502719400⟩, ⟨.path 3, 313655383641600⟩, ⟨.privateRow 2 19, 42416045992320⟩, ⟨.privateRow 2 20, 435011076339840⟩, ⟨.privateRow 2 21, 435011076339840⟩, ⟨.privateRow 3 15, 12330245928000⟩, ⟨.privateRow 3 16, 68284901949264⟩, ⟨.privateRow 3 17, 107966715907050⟩, ⟨.privateRow 3 18, 207333085279320⟩, ⟨.privateRow 3 19, 150089918558580⟩, ⟨.privateRow 4 9, 36029939400⟩, ⟨.privateRow 4 10, 285357120048⟩, ⟨.privateRow 4 11, 1259446548360⟩, ⟨.privateRow 4 12, 7480716167925⟩, ⟨.privateRow 4 13, 19646611241400⟩, ⟨.privateRow 4 14, 30319194005100⟩, ⟨.privateRow 4 15, 66836978784576⟩, ⟨.privateRow 4 16, 81029532213630⟩, ⟨.privateRow 4 17, 54614182142520⟩, ⟨.privateRow 5 5, 11323695240⟩, ⟨.privateRow 5 6, 52843911120⟩, ⟨.privateRow 5 7, 96880503720⟩, ⟨.privateRow 5 8, 672558868800⟩, ⟨.privateRow 5 9, 2784874116024⟩, ⟨.privateRow 5 10, 5654298489840⟩, ⟨.privateRow 5 11, 9696857690520⟩, ⟨.privateRow 5 12, 22081205718000⟩, ⟨.privateRow 5 13, 34736064242880⟩, ⟨.privateRow 5 14, 30247854725088⟩, ⟨.privateRow 6 1, 6216930720⟩, ⟨.privateRow 6 2, 16513722225⟩, ⟨.privateRow 6 5, 654451514640⟩, ⟨.privateRow 6 6, 1105318474260⟩, ⟨.privateRow 6 7, 2296308137760⟩, ⟨.privateRow 6 8, 3693789387288⟩, ⟨.privateRow 6 9, 4779438183520⟩, ⟨.privateRow 6 10, 23634439248420⟩, ⟨.privateRow 6 11, 4854090692880⟩, ⟨.privateRow 7 2, 602420586768⟩, ⟨.privateRow 7 3, 792658666800⟩, ⟨.privateRow 7 4, 1402396102800⟩, ⟨.privateRow 7 5, 2292104644830⟩, ⟨.privateRow 7 6, 4676686134120⟩, ⟨.privateRow 7 7, 5088868640856⟩, ⟨.privateRow 8 0, 2335040322615⟩, ⟨.privateRow 8 1, 924768444600⟩, ⟨.privateRow 8 2, 1704216133620⟩, ⟨.privateRow 9 0, 2071481315904⟩, ⟨.privateRow 10 0, 951190400160⟩, ⟨.hall 2 20, 22899028152000⟩]
  caps := #[0, 4903685740800, 0, 189245658693, 109127823597, 219630323328, 0, 815381296884, 61627370805, 2187836082432, 0] }

theorem case_33_23_13_checked :
    (Witness.linear .negative case_33_23_13).check 33 23 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_23_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 1430, 1430, 1001, 572] }

theorem case_33_23_14_checked :
    (Witness.linear .negative case_33_23_14).check 33 23 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_24_1_checked :
    (Witness.rising).check 33 24 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_24_2_checked :
    (Witness.rising).check 33 24 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_24_3_checked :
    (Witness.rising).check 33 24 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_24_4_checked :
    (Witness.rising).check 33 24 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_24_5_checked :
    (Witness.rising).check 33 24 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_24_6_checked :
    (Witness.rising).check 33 24 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_24_7_checked :
    (Witness.rising).check 33 24 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_24_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_33_24_8_checked :
    (Witness.linear .positive case_33_24_8).check 33 24 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_24_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_33_24_9_checked :
    (Witness.linear .positive case_33_24_9).check 33 24 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_24_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_33_24_10_checked :
    (Witness.linear .positive case_33_24_10).check 33 24 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_24_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_33_24_11_checked :
    (Witness.linear .positive case_33_24_11).check 33 24 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_24_12 : Certificate := {
  objectiveScale := 11
  eta := 45084
  rows := #[⟨.assumptionRow 12, 16⟩]
  caps := #[0, 0, 14872, 5005, 1727, 615, 228, 7140, 7868, 4410] }

theorem case_33_24_12_checked :
    (Witness.linear .conditional case_33_24_12).check 33 24 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_24_13 : Certificate := {
  objectiveScale := 820
  eta := 1575900
  rows := #[⟨.assumptionRow 13, 737⟩]
  caps := #[0, 0, 593320, 215397, 76395, 31405, 13260, 1238484, 1106924, 672490] }

theorem case_33_24_13_checked :
    (Witness.linear .conditional case_33_24_13).check 33 24 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_24_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 4862, 4862, 3432, 2002] }

theorem case_33_24_14_checked :
    (Witness.linear .negative case_33_24_14).check 33 24 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_24_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 1430, 1430] }

theorem case_33_24_15_checked :
    (Witness.linear .negative case_33_24_15).check 33 24 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_25_1_checked :
    (Witness.rising).check 33 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_25_2_checked :
    (Witness.rising).check 33 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_25_3_checked :
    (Witness.rising).check 33 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_25_4_checked :
    (Witness.rising).check 33 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_25_5_checked :
    (Witness.rising).check 33 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_25_6_checked :
    (Witness.rising).check 33 25 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_25_7_checked :
    (Witness.rising).check 33 25 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_25_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0] }

theorem case_33_25_8_checked :
    (Witness.linear .positive case_33_25_8).check 33 25 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_25_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1] }

theorem case_33_25_9_checked :
    (Witness.linear .positive case_33_25_9).check 33 25 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_25_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_33_25_10_checked :
    (Witness.linear .positive case_33_25_10).check 33 25 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_25_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_33_25_11_checked :
    (Witness.linear .positive case_33_25_11).check 33 25 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_25_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_33_25_12_checked :
    (Witness.linear .positive case_33_25_12).check 33 25 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_25_13 : Certificate := {
  objectiveScale := 620
  eta := 2699940
  rows := #[⟨.assumptionRow 13, 671⟩]
  caps := #[0, 0, 908752, 327782, 117832, 42515, 15504, 1513884, 1281392] }

theorem case_33_25_13_checked :
    (Witness.linear .conditional case_33_25_13).check 33 25 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_25_14 : Certificate := {
  objectiveScale := 33
  eta := 5640
  rows := #[⟨.assumptionRow 14, 16⟩]
  caps := #[0, 0, 3010, 1183, 682, 308, 151164, 181662, 134368] }

theorem case_33_25_14_checked :
    (Witness.linear .conditional case_33_25_14).check 33 25 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_25_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 4862, 4862] }

theorem case_33_25_15_checked :
    (Witness.linear .negative case_33_25_15).check 33 25 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_25_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_33_25_16_checked :
    (Witness.linear .negative case_33_25_16).check 33 25 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_26_1_checked :
    (Witness.rising).check 33 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_26_2_checked :
    (Witness.rising).check 33 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_26_3_checked :
    (Witness.rising).check 33 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_26_4_checked :
    (Witness.rising).check 33 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_26_5_checked :
    (Witness.rising).check 33 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_26_6_checked :
    (Witness.rising).check 33 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_26_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0] }

theorem case_33_26_7_checked :
    (Witness.linear .positive case_33_26_7).check 33 26 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_26_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1] }

theorem case_33_26_8_checked :
    (Witness.linear .positive case_33_26_8).check 33 26 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_26_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_33_26_9_checked :
    (Witness.linear .positive case_33_26_9).check 33 26 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_26_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_33_26_10_checked :
    (Witness.linear .positive case_33_26_10).check 33 26 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_26_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_33_26_11_checked :
    (Witness.linear .positive case_33_26_11).check 33 26 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_26_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_33_26_12_checked :
    (Witness.linear .positive case_33_26_12).check 33 26 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_26_13 : Certificate := {
  objectiveScale := 5
  eta := 261630
  rows := #[⟨.assumptionRow 13, 12⟩]
  caps := #[0, 0, 76908, 22984, 7150, 2288, 759, 264] }

theorem case_33_26_13_checked :
    (Witness.linear .conditional case_33_26_13).check 33 26 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_26_14 : Certificate := {
  objectiveScale := 491
  eta := 484296
  rows := #[⟨.assumptionRow 14, 319⟩]
  caps := #[0, 0, 194152, 75712, 34723, 13566, 5161540, 4951590] }

theorem case_33_26_14_checked :
    (Witness.linear .conditional case_33_26_14).check 33 26 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_26_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 16796, 16796] }

theorem case_33_26_15_checked :
    (Witness.linear .negative case_33_26_15).check 33 26 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_26_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_33_26_16_checked :
    (Witness.linear .negative case_33_26_16).check 33 26 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_27_1_checked :
    (Witness.rising).check 33 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_27_2_checked :
    (Witness.rising).check 33 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_27_3_checked :
    (Witness.rising).check 33 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_27_4_checked :
    (Witness.rising).check 33 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_27_5_checked :
    (Witness.rising).check 33 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_27_6_checked :
    (Witness.rising).check 33 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_27_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1] }

theorem case_33_27_7_checked :
    (Witness.linear .positive case_33_27_7).check 33 27 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_27_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1] }

theorem case_33_27_8_checked :
    (Witness.linear .positive case_33_27_8).check 33 27 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_27_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_33_27_9_checked :
    (Witness.linear .positive case_33_27_9).check 33 27 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_27_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_33_27_10_checked :
    (Witness.linear .positive case_33_27_10).check 33 27 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_27_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_33_27_11_checked :
    (Witness.linear .positive case_33_27_11).check 33 27 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_27_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_33_27_12_checked :
    (Witness.linear .positive case_33_27_12).check 33 27 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_27_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_33_27_13_checked :
    (Witness.linear .positive case_33_27_13).check 33 27 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_27_14 : Certificate := {
  objectiveScale := 829
  eta := 3333360
  rows := #[⟨.assumptionRow 14, 696⟩]
  caps := #[0, 0, 1150016, 421148, 168623, 63954, 14276600] }

theorem case_33_27_14_checked :
    (Witness.linear .conditional case_33_27_14).check 33 27 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_27_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 58786, 58786] }

theorem case_33_27_15_checked :
    (Witness.linear .negative case_33_27_15).check 33 27 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_27_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_33_27_16_checked :
    (Witness.linear .negative case_33_27_16).check 33 27 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_27_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_33_27_17_checked :
    (Witness.linear .negative case_33_27_17).check 33 27 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_28_1_checked :
    (Witness.rising).check 33 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_28_2_checked :
    (Witness.rising).check 33 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_28_3_checked :
    (Witness.rising).check 33 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_28_4_checked :
    (Witness.rising).check 33 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_28_5_checked :
    (Witness.rising).check 33 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_28_6_checked :
    (Witness.rising).check 33 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_28_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1] }

theorem case_33_28_7_checked :
    (Witness.linear .positive case_33_28_7).check 33 28 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_28_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2] }

theorem case_33_28_8_checked :
    (Witness.linear .positive case_33_28_8).check 33 28 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_28_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_33_28_9_checked :
    (Witness.linear .positive case_33_28_9).check 33 28 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_28_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_33_28_10_checked :
    (Witness.linear .positive case_33_28_10).check 33 28 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_28_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_33_28_11_checked :
    (Witness.linear .positive case_33_28_11).check 33 28 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_28_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_33_28_12_checked :
    (Witness.linear .positive case_33_28_12).check 33 28 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_28_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_33_28_13_checked :
    (Witness.linear .positive case_33_28_13).check 33 28 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_28_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_33_28_14_checked :
    (Witness.linear .positive case_33_28_14).check 33 28 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_28_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 208012, 208012] }

theorem case_33_28_15_checked :
    (Witness.linear .negative case_33_28_15).check 33 28 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_28_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_33_28_16_checked :
    (Witness.linear .negative case_33_28_16).check 33 28 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_28_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_33_28_17_checked :
    (Witness.linear .negative case_33_28_17).check 33 28 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_28_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_33_28_18_checked :
    (Witness.linear .negative case_33_28_18).check 33 28 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_29_1_checked :
    (Witness.rising).check 33 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_29_2_checked :
    (Witness.rising).check 33 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_29_3_checked :
    (Witness.rising).check 33 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_29_4_checked :
    (Witness.rising).check 33 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_29_5_checked :
    (Witness.rising).check 33 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_29_6_checked :
    (Witness.rising).check 33 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_29_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2] }

theorem case_33_29_7_checked :
    (Witness.linear .positive case_33_29_7).check 33 29 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_29_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5] }

theorem case_33_29_8_checked :
    (Witness.linear .positive case_33_29_8).check 33 29 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_29_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_33_29_9_checked :
    (Witness.linear .positive case_33_29_9).check 33 29 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_29_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_33_29_10_checked :
    (Witness.linear .positive case_33_29_10).check 33 29 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_29_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_33_29_11_checked :
    (Witness.linear .positive case_33_29_11).check 33 29 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_29_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_33_29_12_checked :
    (Witness.linear .positive case_33_29_12).check 33 29 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_29_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_33_29_13_checked :
    (Witness.linear .positive case_33_29_13).check 33 29 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_29_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_33_29_14_checked :
    (Witness.linear .positive case_33_29_14).check 33 29 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_29_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 742900, 742900] }

theorem case_33_29_15_checked :
    (Witness.linear .negative case_33_29_15).check 33 29 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_29_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_33_29_16_checked :
    (Witness.linear .negative case_33_29_16).check 33 29 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_29_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_33_29_17_checked :
    (Witness.linear .negative case_33_29_17).check 33 29 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_29_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_33_29_18_checked :
    (Witness.linear .negative case_33_29_18).check 33 29 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_30_1_checked :
    (Witness.rising).check 33 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_30_2_checked :
    (Witness.rising).check 33 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_30_3_checked :
    (Witness.rising).check 33 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_30_4_checked :
    (Witness.rising).check 33 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_30_5_checked :
    (Witness.rising).check 33 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_30_6_checked :
    (Witness.rising).check 33 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_30_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5] }

theorem case_33_30_7_checked :
    (Witness.linear .positive case_33_30_7).check 33 30 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_30_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14] }

theorem case_33_30_8_checked :
    (Witness.linear .positive case_33_30_8).check 33 30 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_30_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_33_30_9_checked :
    (Witness.linear .positive case_33_30_9).check 33 30 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_30_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_33_30_10_checked :
    (Witness.linear .positive case_33_30_10).check 33 30 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_33_30_11_checked :
    (Witness.linear .positive case_33_30_11).check 33 30 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_30_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_33_30_12_checked :
    (Witness.linear .positive case_33_30_12).check 33 30 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_30_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_33_30_13_checked :
    (Witness.linear .positive case_33_30_13).check 33 30 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_30_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_33_30_14_checked :
    (Witness.linear .positive case_33_30_14).check 33 30 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_30_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_33_30_15_checked :
    (Witness.linear .positive case_33_30_15).check 33 30 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_30_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_33_30_16_checked :
    (Witness.linear .negative case_33_30_16).check 33 30 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_30_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_33_30_17_checked :
    (Witness.linear .negative case_33_30_17).check 33 30 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_30_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_33_30_18_checked :
    (Witness.linear .negative case_33_30_18).check 33 30 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_30_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_33_30_19_checked :
    (Witness.linear .negative case_33_30_19).check 33 30 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_31_1_checked :
    (Witness.rising).check 33 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_31_2_checked :
    (Witness.rising).check 33 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_31_3_checked :
    (Witness.rising).check 33 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_31_4_checked :
    (Witness.rising).check 33 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_31_5_checked :
    (Witness.rising).check 33 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_31_6_checked :
    (Witness.rising).check 33 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_31_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14] }

theorem case_33_31_7_checked :
    (Witness.linear .positive case_33_31_7).check 33 31 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_31_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_33_31_8_checked :
    (Witness.linear .positive case_33_31_8).check 33 31 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_31_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_33_31_9_checked :
    (Witness.linear .positive case_33_31_9).check 33 31 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_31_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_33_31_10_checked :
    (Witness.linear .positive case_33_31_10).check 33 31 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_33_31_11_checked :
    (Witness.linear .positive case_33_31_11).check 33 31 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_33_31_12_checked :
    (Witness.linear .positive case_33_31_12).check 33 31 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_31_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_33_31_13_checked :
    (Witness.linear .positive case_33_31_13).check 33 31 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_31_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_33_31_14_checked :
    (Witness.linear .positive case_33_31_14).check 33 31 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_31_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_33_31_15_checked :
    (Witness.linear .positive case_33_31_15).check 33 31 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_31_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_33_31_16_checked :
    (Witness.linear .negative case_33_31_16).check 33 31 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_31_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_33_31_17_checked :
    (Witness.linear .negative case_33_31_17).check 33 31 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_31_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_33_31_18_checked :
    (Witness.linear .negative case_33_31_18).check 33 31 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_31_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_33_31_19_checked :
    (Witness.linear .negative case_33_31_19).check 33 31 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_31_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_33_31_20_checked :
    (Witness.linear .negative case_33_31_20).check 33 31 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_32_1_checked :
    (Witness.rising).check 33 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_32_2_checked :
    (Witness.rising).check 33 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_32_3_checked :
    (Witness.rising).check 33 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_32_4_checked :
    (Witness.rising).check 33 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_32_5_checked :
    (Witness.rising).check 33 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_33_32_6_checked :
    (Witness.rising).check 33 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_32_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0] }

theorem case_33_32_7_checked :
    (Witness.linear .positive case_33_32_7).check 33 32 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_32_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_33_32_8_checked :
    (Witness.linear .positive case_33_32_8).check 33 32 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_32_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_33_32_9_checked :
    (Witness.linear .positive case_33_32_9).check 33 32 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_32_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_33_32_10_checked :
    (Witness.linear .positive case_33_32_10).check 33 32 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_33_32_11_checked :
    (Witness.linear .positive case_33_32_11).check 33 32 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_33_32_12_checked :
    (Witness.linear .positive case_33_32_12).check 33 32 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_32_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_33_32_13_checked :
    (Witness.linear .positive case_33_32_13).check 33 32 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_32_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_33_32_14_checked :
    (Witness.linear .positive case_33_32_14).check 33 32 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_32_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_33_32_15_checked :
    (Witness.linear .positive case_33_32_15).check 33 32 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_32_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_33_32_16_checked :
    (Witness.linear .positive case_33_32_16).check 33 32 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_32_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_33_32_17_checked :
    (Witness.linear .negative case_33_32_17).check 33 32 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_32_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_33_32_18_checked :
    (Witness.linear .negative case_33_32_18).check 33 32 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_32_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_33_32_19_checked :
    (Witness.linear .negative case_33_32_19).check 33 32 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_33_32_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_33_32_20_checked :
    (Witness.linear .negative case_33_32_20).check 33 32 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_33 (a k : ℕ) (h : Domain 33 a k) :
    ∃ w : Witness, w.check 33 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 17 ≤ a := by omega
  have haHi : a ≤ 32 := by omega
  interval_cases a

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_33_17_1_checked⟩

    · exact ⟨Witness.rising, case_33_17_2_checked⟩

    · exact ⟨Witness.rising, case_33_17_3_checked⟩

    · exact ⟨Witness.rising, case_33_17_4_checked⟩

    · exact ⟨Witness.rising, case_33_17_5_checked⟩

    · exact ⟨Witness.rising, case_33_17_6_checked⟩

    · exact ⟨Witness.rising, case_33_17_7_checked⟩

    · exact ⟨Witness.linear .positive case_33_17_8, case_33_17_8_checked⟩

    · exact ⟨Witness.linear .positive case_33_17_9, case_33_17_9_checked⟩

    · exact ⟨Witness.linear .conditional case_33_17_10, case_33_17_10_checked⟩

  · have hkHi : k ≤ 11 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_33_18_1_checked⟩

    · exact ⟨Witness.rising, case_33_18_2_checked⟩

    · exact ⟨Witness.rising, case_33_18_3_checked⟩

    · exact ⟨Witness.rising, case_33_18_4_checked⟩

    · exact ⟨Witness.rising, case_33_18_5_checked⟩

    · exact ⟨Witness.rising, case_33_18_6_checked⟩

    · exact ⟨Witness.rising, case_33_18_7_checked⟩

    · exact ⟨Witness.linear .positive case_33_18_8, case_33_18_8_checked⟩

    · exact ⟨Witness.linear .positive case_33_18_9, case_33_18_9_checked⟩

    · exact ⟨Witness.linear .conditional case_33_18_10, case_33_18_10_checked⟩

    · exact ⟨Witness.linear .conditional case_33_18_11, case_33_18_11_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_33_19_1_checked⟩

    · exact ⟨Witness.rising, case_33_19_2_checked⟩

    · exact ⟨Witness.rising, case_33_19_3_checked⟩

    · exact ⟨Witness.rising, case_33_19_4_checked⟩

    · exact ⟨Witness.rising, case_33_19_5_checked⟩

    · exact ⟨Witness.rising, case_33_19_6_checked⟩

    · exact ⟨Witness.rising, case_33_19_7_checked⟩

    · exact ⟨Witness.linear .positive case_33_19_8, case_33_19_8_checked⟩

    · exact ⟨Witness.linear .positive case_33_19_9, case_33_19_9_checked⟩

    · exact ⟨Witness.linear .conditional case_33_19_10, case_33_19_10_checked⟩

    · exact ⟨Witness.linear .conditional case_33_19_11, case_33_19_11_checked⟩

    · exact ⟨Witness.linear .negative case_33_19_12, case_33_19_12_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_33_20_1_checked⟩

    · exact ⟨Witness.rising, case_33_20_2_checked⟩

    · exact ⟨Witness.rising, case_33_20_3_checked⟩

    · exact ⟨Witness.rising, case_33_20_4_checked⟩

    · exact ⟨Witness.rising, case_33_20_5_checked⟩

    · exact ⟨Witness.rising, case_33_20_6_checked⟩

    · exact ⟨Witness.rising, case_33_20_7_checked⟩

    · exact ⟨Witness.linear .positive case_33_20_8, case_33_20_8_checked⟩

    · exact ⟨Witness.linear .positive case_33_20_9, case_33_20_9_checked⟩

    · exact ⟨Witness.linear .positive case_33_20_10, case_33_20_10_checked⟩

    · exact ⟨Witness.linear .conditional case_33_20_11, case_33_20_11_checked⟩

    · exact ⟨Witness.linear .conditional case_33_20_12, case_33_20_12_checked⟩

  · have hkHi : k ≤ 13 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_33_21_1_checked⟩

    · exact ⟨Witness.rising, case_33_21_2_checked⟩

    · exact ⟨Witness.rising, case_33_21_3_checked⟩

    · exact ⟨Witness.rising, case_33_21_4_checked⟩

    · exact ⟨Witness.rising, case_33_21_5_checked⟩

    · exact ⟨Witness.rising, case_33_21_6_checked⟩

    · exact ⟨Witness.rising, case_33_21_7_checked⟩

    · exact ⟨Witness.linear .positive case_33_21_8, case_33_21_8_checked⟩

    · exact ⟨Witness.linear .positive case_33_21_9, case_33_21_9_checked⟩

    · exact ⟨Witness.linear .positive case_33_21_10, case_33_21_10_checked⟩

    · exact ⟨Witness.linear .conditional case_33_21_11, case_33_21_11_checked⟩

    · exact ⟨Witness.linear .conditional case_33_21_12, case_33_21_12_checked⟩

    · exact ⟨Witness.linear .negative case_33_21_13, case_33_21_13_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_33_22_1_checked⟩

    · exact ⟨Witness.rising, case_33_22_2_checked⟩

    · exact ⟨Witness.rising, case_33_22_3_checked⟩

    · exact ⟨Witness.rising, case_33_22_4_checked⟩

    · exact ⟨Witness.rising, case_33_22_5_checked⟩

    · exact ⟨Witness.rising, case_33_22_6_checked⟩

    · exact ⟨Witness.rising, case_33_22_7_checked⟩

    · exact ⟨Witness.linear .positive case_33_22_8, case_33_22_8_checked⟩

    · exact ⟨Witness.linear .positive case_33_22_9, case_33_22_9_checked⟩

    · exact ⟨Witness.linear .positive case_33_22_10, case_33_22_10_checked⟩

    · exact ⟨Witness.linear .conditional case_33_22_11, case_33_22_11_checked⟩

    · exact ⟨Witness.linear .conditional case_33_22_12, case_33_22_12_checked⟩

    · exact ⟨Witness.linear .negative case_33_22_13, case_33_22_13_checked⟩

    · exact ⟨Witness.linear .negative case_33_22_14, case_33_22_14_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_33_23_1_checked⟩

    · exact ⟨Witness.rising, case_33_23_2_checked⟩

    · exact ⟨Witness.rising, case_33_23_3_checked⟩

    · exact ⟨Witness.rising, case_33_23_4_checked⟩

    · exact ⟨Witness.rising, case_33_23_5_checked⟩

    · exact ⟨Witness.rising, case_33_23_6_checked⟩

    · exact ⟨Witness.rising, case_33_23_7_checked⟩

    · exact ⟨Witness.linear .positive case_33_23_8, case_33_23_8_checked⟩

    · exact ⟨Witness.linear .positive case_33_23_9, case_33_23_9_checked⟩

    · exact ⟨Witness.linear .positive case_33_23_10, case_33_23_10_checked⟩

    · exact ⟨Witness.linear .positive case_33_23_11, case_33_23_11_checked⟩

    · exact ⟨Witness.linear .conditional case_33_23_12, case_33_23_12_checked⟩

    · exact ⟨Witness.linear .negative case_33_23_13, case_33_23_13_checked⟩

    · exact ⟨Witness.linear .negative case_33_23_14, case_33_23_14_checked⟩

  · have hkHi : k ≤ 15 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_33_24_1_checked⟩

    · exact ⟨Witness.rising, case_33_24_2_checked⟩

    · exact ⟨Witness.rising, case_33_24_3_checked⟩

    · exact ⟨Witness.rising, case_33_24_4_checked⟩

    · exact ⟨Witness.rising, case_33_24_5_checked⟩

    · exact ⟨Witness.rising, case_33_24_6_checked⟩

    · exact ⟨Witness.rising, case_33_24_7_checked⟩

    · exact ⟨Witness.linear .positive case_33_24_8, case_33_24_8_checked⟩

    · exact ⟨Witness.linear .positive case_33_24_9, case_33_24_9_checked⟩

    · exact ⟨Witness.linear .positive case_33_24_10, case_33_24_10_checked⟩

    · exact ⟨Witness.linear .positive case_33_24_11, case_33_24_11_checked⟩

    · exact ⟨Witness.linear .conditional case_33_24_12, case_33_24_12_checked⟩

    · exact ⟨Witness.linear .conditional case_33_24_13, case_33_24_13_checked⟩

    · exact ⟨Witness.linear .negative case_33_24_14, case_33_24_14_checked⟩

    · exact ⟨Witness.linear .negative case_33_24_15, case_33_24_15_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_33_25_1_checked⟩

    · exact ⟨Witness.rising, case_33_25_2_checked⟩

    · exact ⟨Witness.rising, case_33_25_3_checked⟩

    · exact ⟨Witness.rising, case_33_25_4_checked⟩

    · exact ⟨Witness.rising, case_33_25_5_checked⟩

    · exact ⟨Witness.rising, case_33_25_6_checked⟩

    · exact ⟨Witness.rising, case_33_25_7_checked⟩

    · exact ⟨Witness.linear .positive case_33_25_8, case_33_25_8_checked⟩

    · exact ⟨Witness.linear .positive case_33_25_9, case_33_25_9_checked⟩

    · exact ⟨Witness.linear .positive case_33_25_10, case_33_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_33_25_11, case_33_25_11_checked⟩

    · exact ⟨Witness.linear .positive case_33_25_12, case_33_25_12_checked⟩

    · exact ⟨Witness.linear .conditional case_33_25_13, case_33_25_13_checked⟩

    · exact ⟨Witness.linear .conditional case_33_25_14, case_33_25_14_checked⟩

    · exact ⟨Witness.linear .negative case_33_25_15, case_33_25_15_checked⟩

    · exact ⟨Witness.linear .negative case_33_25_16, case_33_25_16_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_33_26_1_checked⟩

    · exact ⟨Witness.rising, case_33_26_2_checked⟩

    · exact ⟨Witness.rising, case_33_26_3_checked⟩

    · exact ⟨Witness.rising, case_33_26_4_checked⟩

    · exact ⟨Witness.rising, case_33_26_5_checked⟩

    · exact ⟨Witness.rising, case_33_26_6_checked⟩

    · exact ⟨Witness.linear .positive case_33_26_7, case_33_26_7_checked⟩

    · exact ⟨Witness.linear .positive case_33_26_8, case_33_26_8_checked⟩

    · exact ⟨Witness.linear .positive case_33_26_9, case_33_26_9_checked⟩

    · exact ⟨Witness.linear .positive case_33_26_10, case_33_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_33_26_11, case_33_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_33_26_12, case_33_26_12_checked⟩

    · exact ⟨Witness.linear .conditional case_33_26_13, case_33_26_13_checked⟩

    · exact ⟨Witness.linear .conditional case_33_26_14, case_33_26_14_checked⟩

    · exact ⟨Witness.linear .negative case_33_26_15, case_33_26_15_checked⟩

    · exact ⟨Witness.linear .negative case_33_26_16, case_33_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_33_27_1_checked⟩

    · exact ⟨Witness.rising, case_33_27_2_checked⟩

    · exact ⟨Witness.rising, case_33_27_3_checked⟩

    · exact ⟨Witness.rising, case_33_27_4_checked⟩

    · exact ⟨Witness.rising, case_33_27_5_checked⟩

    · exact ⟨Witness.rising, case_33_27_6_checked⟩

    · exact ⟨Witness.linear .positive case_33_27_7, case_33_27_7_checked⟩

    · exact ⟨Witness.linear .positive case_33_27_8, case_33_27_8_checked⟩

    · exact ⟨Witness.linear .positive case_33_27_9, case_33_27_9_checked⟩

    · exact ⟨Witness.linear .positive case_33_27_10, case_33_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_33_27_11, case_33_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_33_27_12, case_33_27_12_checked⟩

    · exact ⟨Witness.linear .positive case_33_27_13, case_33_27_13_checked⟩

    · exact ⟨Witness.linear .conditional case_33_27_14, case_33_27_14_checked⟩

    · exact ⟨Witness.linear .negative case_33_27_15, case_33_27_15_checked⟩

    · exact ⟨Witness.linear .negative case_33_27_16, case_33_27_16_checked⟩

    · exact ⟨Witness.linear .negative case_33_27_17, case_33_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_33_28_1_checked⟩

    · exact ⟨Witness.rising, case_33_28_2_checked⟩

    · exact ⟨Witness.rising, case_33_28_3_checked⟩

    · exact ⟨Witness.rising, case_33_28_4_checked⟩

    · exact ⟨Witness.rising, case_33_28_5_checked⟩

    · exact ⟨Witness.rising, case_33_28_6_checked⟩

    · exact ⟨Witness.linear .positive case_33_28_7, case_33_28_7_checked⟩

    · exact ⟨Witness.linear .positive case_33_28_8, case_33_28_8_checked⟩

    · exact ⟨Witness.linear .positive case_33_28_9, case_33_28_9_checked⟩

    · exact ⟨Witness.linear .positive case_33_28_10, case_33_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_33_28_11, case_33_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_33_28_12, case_33_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_33_28_13, case_33_28_13_checked⟩

    · exact ⟨Witness.linear .positive case_33_28_14, case_33_28_14_checked⟩

    · exact ⟨Witness.linear .negative case_33_28_15, case_33_28_15_checked⟩

    · exact ⟨Witness.linear .negative case_33_28_16, case_33_28_16_checked⟩

    · exact ⟨Witness.linear .negative case_33_28_17, case_33_28_17_checked⟩

    · exact ⟨Witness.linear .negative case_33_28_18, case_33_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_33_29_1_checked⟩

    · exact ⟨Witness.rising, case_33_29_2_checked⟩

    · exact ⟨Witness.rising, case_33_29_3_checked⟩

    · exact ⟨Witness.rising, case_33_29_4_checked⟩

    · exact ⟨Witness.rising, case_33_29_5_checked⟩

    · exact ⟨Witness.rising, case_33_29_6_checked⟩

    · exact ⟨Witness.linear .positive case_33_29_7, case_33_29_7_checked⟩

    · exact ⟨Witness.linear .positive case_33_29_8, case_33_29_8_checked⟩

    · exact ⟨Witness.linear .positive case_33_29_9, case_33_29_9_checked⟩

    · exact ⟨Witness.linear .positive case_33_29_10, case_33_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_33_29_11, case_33_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_33_29_12, case_33_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_33_29_13, case_33_29_13_checked⟩

    · exact ⟨Witness.linear .positive case_33_29_14, case_33_29_14_checked⟩

    · exact ⟨Witness.linear .negative case_33_29_15, case_33_29_15_checked⟩

    · exact ⟨Witness.linear .negative case_33_29_16, case_33_29_16_checked⟩

    · exact ⟨Witness.linear .negative case_33_29_17, case_33_29_17_checked⟩

    · exact ⟨Witness.linear .negative case_33_29_18, case_33_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_33_30_1_checked⟩

    · exact ⟨Witness.rising, case_33_30_2_checked⟩

    · exact ⟨Witness.rising, case_33_30_3_checked⟩

    · exact ⟨Witness.rising, case_33_30_4_checked⟩

    · exact ⟨Witness.rising, case_33_30_5_checked⟩

    · exact ⟨Witness.rising, case_33_30_6_checked⟩

    · exact ⟨Witness.linear .positive case_33_30_7, case_33_30_7_checked⟩

    · exact ⟨Witness.linear .positive case_33_30_8, case_33_30_8_checked⟩

    · exact ⟨Witness.linear .positive case_33_30_9, case_33_30_9_checked⟩

    · exact ⟨Witness.linear .positive case_33_30_10, case_33_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_33_30_11, case_33_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_33_30_12, case_33_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_33_30_13, case_33_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_33_30_14, case_33_30_14_checked⟩

    · exact ⟨Witness.linear .positive case_33_30_15, case_33_30_15_checked⟩

    · exact ⟨Witness.linear .negative case_33_30_16, case_33_30_16_checked⟩

    · exact ⟨Witness.linear .negative case_33_30_17, case_33_30_17_checked⟩

    · exact ⟨Witness.linear .negative case_33_30_18, case_33_30_18_checked⟩

    · exact ⟨Witness.linear .negative case_33_30_19, case_33_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_33_31_1_checked⟩

    · exact ⟨Witness.rising, case_33_31_2_checked⟩

    · exact ⟨Witness.rising, case_33_31_3_checked⟩

    · exact ⟨Witness.rising, case_33_31_4_checked⟩

    · exact ⟨Witness.rising, case_33_31_5_checked⟩

    · exact ⟨Witness.rising, case_33_31_6_checked⟩

    · exact ⟨Witness.linear .positive case_33_31_7, case_33_31_7_checked⟩

    · exact ⟨Witness.linear .positive case_33_31_8, case_33_31_8_checked⟩

    · exact ⟨Witness.linear .positive case_33_31_9, case_33_31_9_checked⟩

    · exact ⟨Witness.linear .positive case_33_31_10, case_33_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_33_31_11, case_33_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_33_31_12, case_33_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_33_31_13, case_33_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_33_31_14, case_33_31_14_checked⟩

    · exact ⟨Witness.linear .positive case_33_31_15, case_33_31_15_checked⟩

    · exact ⟨Witness.linear .negative case_33_31_16, case_33_31_16_checked⟩

    · exact ⟨Witness.linear .negative case_33_31_17, case_33_31_17_checked⟩

    · exact ⟨Witness.linear .negative case_33_31_18, case_33_31_18_checked⟩

    · exact ⟨Witness.linear .negative case_33_31_19, case_33_31_19_checked⟩

    · exact ⟨Witness.linear .negative case_33_31_20, case_33_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_33_32_1_checked⟩

    · exact ⟨Witness.rising, case_33_32_2_checked⟩

    · exact ⟨Witness.rising, case_33_32_3_checked⟩

    · exact ⟨Witness.rising, case_33_32_4_checked⟩

    · exact ⟨Witness.rising, case_33_32_5_checked⟩

    · exact ⟨Witness.rising, case_33_32_6_checked⟩

    · exact ⟨Witness.linear .positive case_33_32_7, case_33_32_7_checked⟩

    · exact ⟨Witness.linear .positive case_33_32_8, case_33_32_8_checked⟩

    · exact ⟨Witness.linear .positive case_33_32_9, case_33_32_9_checked⟩

    · exact ⟨Witness.linear .positive case_33_32_10, case_33_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_33_32_11, case_33_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_33_32_12, case_33_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_33_32_13, case_33_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_33_32_14, case_33_32_14_checked⟩

    · exact ⟨Witness.linear .positive case_33_32_15, case_33_32_15_checked⟩

    · exact ⟨Witness.linear .positive case_33_32_16, case_33_32_16_checked⟩

    · exact ⟨Witness.linear .negative case_33_32_17, case_33_32_17_checked⟩

    · exact ⟨Witness.linear .negative case_33_32_18, case_33_32_18_checked⟩

    · exact ⟨Witness.linear .negative case_33_32_19, case_33_32_19_checked⟩

    · exact ⟨Witness.linear .negative case_33_32_20, case_33_32_20_checked⟩


#print axioms coverage_33
end ForestUnimodality.FiniteRows.FiniteData
