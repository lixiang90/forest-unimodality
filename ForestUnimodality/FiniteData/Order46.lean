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

theorem case_46_23_1_checked :
    (Witness.rising).check 46 23 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_23_2_checked :
    (Witness.rising).check 46 23 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_23_3_checked :
    (Witness.rising).check 46 23 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_23_4_checked :
    (Witness.rising).check 46 23 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_23_5_checked :
    (Witness.rising).check 46 23 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_23_6_checked :
    (Witness.rising).check 46 23 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_23_7_checked :
    (Witness.rising).check 46 23 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_23_8_checked :
    (Witness.rising).check 46 23 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_23_9_checked :
    (Witness.rising).check 46 23 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_23_10 : Certificate := {
  objectiveScale := 84284200000
  eta := 0
  rows := #[⟨.count 2, 154358926722000⟩, ⟨.count 3, 204635834282880⟩, ⟨.count 4, 30695375142432⟩, ⟨.count 5, 5385153533760⟩, ⟨.count 6, 1114169696640⟩, ⟨.count 7, 286734848400⟩, ⟨.count 8, 105136111080⟩, ⟨.count 9, 84108888864⟩, ⟨.count 11, 15019444440⟩, ⟨.path 10, 21146954400⟩, ⟨.path 11, 14546804580⟩, ⟨.hall 9 1, 724714452⟩, ⟨.hall 8 3, 133039368⟩, ⟨.hall 9 3, 10980522⟩, ⟨.hall 0 4, 1801241009568⟩, ⟨.hall 1 4, 89752558896⟩, ⟨.hall 8 4, 19945296⟩, ⟨.hall 7 5, 75325320⟩, ⟨.hall 0 6, 48244276080⟩, ⟨.hall 7 6, 9150435⟩, ⟨.hall 6 8, 57077496⟩, ⟨.hall 6 9, 1989225⟩, ⟨.hall 5 13, 617682780⟩, ⟨.hall 4 17, 89752558896⟩]
  caps := #[0, 0, 0, 281451747720, 16850701868, 0, 2408245840, 0, 295043320, 352988636, 354042260, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_23_10_checked :
    (Witness.linear .positive case_46_23_10).check 46 23 10 = true := by
  change case_46_23_10.check 46 23 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_23_11 : Certificate := {
  objectiveScale := 64350000
  eta := 107550162720
  rows := #[⟨.count 3, 280747827360⟩, ⟨.count 4, 48886437600⟩, ⟨.count 5, 9336206880⟩, ⟨.count 6, 2033871840⟩, ⟨.count 7, 534774240⟩, ⟨.count 8, 166486320⟩, ⟨.count 9, 69621552⟩, ⟨.count 10, 64864800⟩, ⟨.path 11, 5215320⟩, ⟨.path 12, 16323120⟩, ⟨.privateRow 10 2, 2090088⟩, ⟨.privateRow 12 0, 1359435⟩, ⟨.hall 10 1, 2065140⟩, ⟨.hall 10 2, 80640⟩, ⟨.hall 9 3, 232848⟩, ⟨.hall 0 4, 1308539232⟩, ⟨.hall 1 4, 121705584⟩, ⟨.hall 8 4, 244944⟩, ⟨.hall 12 4, 71280⟩, ⟨.hall 13 4, 154440⟩, ⟨.hall 0 5, 445164720⟩, ⟨.hall 1 5, 480480⟩, ⟨.hall 8 5, 26040⟩, ⟨.hall 7 6, 110250⟩, ⟨.hall 7 7, 39004⟩, ⟨.hall 6 9, 62748⟩, ⟨.hall 6 10, 124740⟩, ⟨.hall 5 14, 4018014⟩, ⟨.hall 4 17, 142942800⟩]
  caps := #[0, 122216094000, 0, 99768240, 6177600, 21003840, 11437020, 2882880, 2642640, 0, 0, 1358280, 175065, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_23_11_checked :
    (Witness.linear .positive case_46_23_11).check 46 23 11 = true := by
  change case_46_23_11.check 46 23 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_23_12 : Certificate := {
  objectiveScale := 33000000
  eta := 0
  rows := #[⟨.count 3, 261891630000⟩, ⟨.count 4, 66811464720⟩, ⟨.count 5, 13477464000⟩, ⟨.count 6, 2981378400⟩, ⟨.count 7, 748347600⟩, ⟨.count 8, 218618400⟩, ⟨.count 9, 75675600⟩, ⟨.count 10, 32432400⟩, ⟨.count 11, 33541200⟩, ⟨.path 13, 8467200⟩, ⟨.path 14, 1102500⟩, ⟨.privateRow 10 4, 2144142⟩, ⟨.privateRow 10 5, 1161160⟩, ⟨.privateRow 11 2, 478800⟩, ⟨.privateRow 13 0, 768600⟩, ⟨.privateRow 14 0, 810810⟩, ⟨.hall 11 1, 912450⟩, ⟨.hall 11 2, 140910⟩, ⟨.hall 14 2, 410410⟩, ⟨.hall 1 3, 3063060⟩, ⟨.hall 10 3, 234360⟩, ⟨.hall 2 5, 900900⟩, ⟨.hall 9 5, 114940⟩, ⟨.hall 0 6, 160960800⟩, ⟨.hall 1 6, 8258250⟩, ⟨.hall 8 6, 107520⟩, ⟨.hall 1 7, 3713710⟩, ⟨.hall 8 7, 39200⟩, ⟨.hall 0 8, 46806760⟩, ⟨.hall 7 9, 181755⟩, ⟨.hall 1 10, 438900⟩, ⟨.hall 7 10, 11550⟩, ⟨.hall 6 12, 838860⟩, ⟨.hall 2 14, 520520⟩, ⟨.hall 5 15, 12537525⟩, ⟨.hall 4 18, 747386640⟩, ⟨.hall 1 20, 193993800⟩]
  caps := #[0, 50803894800, 1816487400, 0, 32380920, 8751600, 10210200, 8408400, 2702700, 0, 2763618, 0, 333300, 12600, 1552950, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_23_12_checked :
    (Witness.linear .positive case_46_23_12).check 46 23 12 = true := by
  change case_46_23_12.check 46 23 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_23_13 : Certificate := {
  objectiveScale := 6000000
  eta := 0
  rows := #[⟨.count 3, 145329069600⟩, ⟨.count 4, 36781224480⟩, ⟨.count 5, 8401536000⟩, ⟨.count 6, 2240409600⟩, ⟨.count 7, 612612000⟩, ⟨.count 8, 188588400⟩, ⟨.count 9, 67747680⟩, ⟨.count 10, 29343600⟩, ⟨.count 11, 17859600⟩, ⟨.count 12, 17859600⟩, ⟨.path 14, 3391290⟩, ⟨.privateRow 8 10, 12987975⟩, ⟨.privateRow 9 7, 770770⟩, ⟨.privateRow 9 8, 5811520⟩, ⟨.privateRow 10 5, 852280⟩, ⟨.privateRow 10 6, 2824965⟩, ⟨.privateRow 11 3, 522720⟩, ⟨.privateRow 14 0, 936936⟩, ⟨.hall 12 1, 1172160⟩, ⟨.hall 0 2, 110853600⟩, ⟨.hall 11 2, 381480⟩, ⟨.hall 1 3, 1750320⟩, ⟨.hall 11 3, 71940⟩, ⟨.hall 12 3, 7590⟩, ⟨.hall 10 4, 190320⟩, ⟨.hall 2 5, 171600⟩, ⟨.hall 0 6, 3432000⟩, ⟨.hall 9 6, 134190⟩, ⟨.hall 0 7, 57957900⟩, ⟨.hall 1 7, 3513510⟩, ⟨.hall 8 8, 174160⟩, ⟨.hall 0 9, 1492920⟩, ⟨.hall 7 11, 710160⟩, ⟨.hall 6 13, 2797080⟩, ⟨.hall 2 15, 250250⟩, ⟨.hall 2 16, 388960⟩, ⟨.hall 5 16, 103532000⟩, ⟨.hall 4 18, 1127206080⟩, ⟨.assumptionRow 13, 17738820⟩]
  caps := #[0, 0, 0, 280157280, 583440, 4667520, 0, 0, 915915, 337710, 172920, 0, 11550, 0, 21930, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_23_13_checked :
    (Witness.linear .conditional case_46_23_13).check 46 23 13 = true := by
  change case_46_23_13.check 46 23 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_23_14 : Certificate := {
  objectiveScale := 30240000
  eta := 0
  rows := #[⟨.count 2, 547528101120⟩, ⟨.count 3, 153643089600⟩, ⟨.count 4, 43858118304⟩, ⟨.count 5, 13011878880⟩, ⟨.count 6, 4067743680⟩, ⟨.count 7, 1341980640⟩, ⟨.count 8, 479278800⟩, ⟨.count 9, 187675488⟩, ⟨.count 10, 77837760⟩, ⟨.count 11, 36590400⟩, ⟨.count 12, 31101840⟩, ⟨.count 13, 25945920⟩, ⟨.path 12, 4924260⟩, ⟨.privateRow 12 3, 4184180⟩, ⟨.privateRow 12 4, 571725⟩, ⟨.privateRow 15 0, 3363360⟩, ⟨.hall 13 1, 3651648⟩, ⟨.hall 12 2, 1511664⟩, ⟨.hall 12 3, 164934⟩, ⟨.hall 13 3, 23166⟩, ⟨.hall 11 4, 669900⟩, ⟨.hall 0 5, 40840800⟩, ⟨.hall 10 5, 847560⟩, ⟨.hall 9 6, 311346⟩, ⟨.hall 0 7, 5675670⟩, ⟨.hall 9 7, 567630⟩, ⟨.hall 8 8, 365568⟩, ⟨.hall 10 8, 10080⟩, ⟨.hall 8 9, 928032⟩, ⟨.hall 7 11, 3758370⟩, ⟨.hall 6 13, 14030874⟩, ⟨.hall 5 15, 76336260⟩, ⟨.hall 4 17, 614245632⟩, ⟨.hall 3 19, 7682154480⟩, ⟨.assumptionRow 14, 26364240⟩]
  caps := #[0, 0, 4279801680, 114884640, 0, 77014080, 0, 10090080, 1377096, 0, 1389960, 684480, 186660, 1663200, 637056, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_23_14_checked :
    (Witness.linear .conditional case_46_23_14).check 46 23 14 = true := by
  change case_46_23_14.check 46 23 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_24_1_checked :
    (Witness.rising).check 46 24 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_24_2_checked :
    (Witness.rising).check 46 24 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_24_3_checked :
    (Witness.rising).check 46 24 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_24_4_checked :
    (Witness.rising).check 46 24 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_24_5_checked :
    (Witness.rising).check 46 24 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_24_6_checked :
    (Witness.rising).check 46 24 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_24_7_checked :
    (Witness.rising).check 46 24 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_24_8_checked :
    (Witness.rising).check 46 24 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_24_9_checked :
    (Witness.rising).check 46 24 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_24_10 : Certificate := {
  objectiveScale := 90921831000000
  eta := 7761826215852508800
  rows := #[⟨.count 2, 1791808743411086400⟩, ⟨.count 3, 274797574101610560⟩, ⟨.count 4, 39329292692289600⟩, ⟨.count 5, 6695847322164000⟩, ⟨.count 6, 1343315499926400⟩, ⟨.count 7, 337383638291700⟩, ⟨.count 8, 116088993820800⟩, ⟨.count 9, 89554366661760⟩, ⟨.count 11, 13155689547000⟩, ⟨.path 10, 26204070677400⟩, ⟨.path 11, 14033135173200⟩, ⟨.privateRow 4 20, 570909087468720⟩, ⟨.privateRow 6 12, 14807269620000⟩, ⟨.privateRow 7 8, 6063576909390⟩, ⟨.privateRow 7 9, 18484408242300⟩, ⟨.privateRow 7 10, 22155377168925⟩, ⟨.privateRow 8 5, 3506855021670⟩, ⟨.privateRow 8 7, 25829801125128⟩, ⟨.privateRow 8 8, 2257285990960⟩, ⟨.privateRow 9 2, 1747257815160⟩, ⟨.privateRow 9 3, 3859002267120⟩, ⟨.privateRow 9 4, 587355028260⟩, ⟨.privateRow 10 0, 937641873168⟩, ⟨.hall 6 9, 24502143120⟩, ⟨.hall 5 12, 104909805000⟩, ⟨.hall 7 16, 29449046226600⟩, ⟨.hall 4 17, 14912635033296⟩]
  caps := #[0, 0, 0, 165853018441440, 141326380602000, 21344116008600, 5093285087520, 10862792669190, 1036907856600, 1377245822040, 0, 877445626200, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_24_10_checked :
    (Witness.linear .positive case_46_24_10).check 46 24 10 = true := by
  change case_46_24_10.check 46 24 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_24_11 : Certificate := {
  objectiveScale := 1977976000000
  eta := 258645430867824000
  rows := #[⟨.count 2, 67916419261891200⟩, ⟨.count 3, 12140499816244800⟩, ⟨.count 4, 1966927659016320⟩, ⟨.count 5, 370419521472000⟩, ⟨.count 6, 77352311836800⟩, ⟨.count 7, 18589067897400⟩, ⟨.count 8, 5592608461440⟩, ⟨.count 9, 2287885279680⟩, ⟨.count 10, 2011327718400⟩, ⟨.path 11, 271912212000⟩, ⟨.path 12, 439038943200⟩, ⟨.privateRow 4 20, 13890732055200⟩, ⟨.privateRow 7 10, 629849370150⟩, ⟨.privateRow 8 7, 187479488196⟩, ⟨.privateRow 8 8, 522541699680⟩, ⟨.privateRow 8 9, 647439757965⟩, ⟨.privateRow 9 4, 40855094280⟩, ⟨.privateRow 9 5, 198085305600⟩, ⟨.privateRow 9 6, 261472603392⟩, ⟨.privateRow 9 7, 395436961920⟩, ⟨.privateRow 10 2, 88962572160⟩, ⟨.privateRow 10 3, 121517716320⟩, ⟨.privateRow 10 4, 20570397120⟩, ⟨.privateRow 11 0, 61357467600⟩, ⟨.privateRow 12 0, 33844456800⟩, ⟨.privateRow 13 0, 36664828200⟩, ⟨.hall 7 8, 422636760⟩, ⟨.hall 7 9, 1024458435⟩, ⟨.hall 6 10, 3077965800⟩, ⟨.hall 5 14, 36262546320⟩, ⟨.hall 8 15, 1414040207580⟩, ⟨.hall 4 18, 5965703872128⟩]
  caps := #[0, 0, 0, 20325229267200, 6011477151680, 4419555666240, 362740778400, 324553329100, 15928679767, 0, 11805785600, 5724461600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_24_11_checked :
    (Witness.linear .positive case_46_24_11).check 46 24 11 = true := by
  change case_46_24_11.check 46 24 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_24_12 : Certificate := {
  objectiveScale := 2543112000000
  eta := 448318746837561600
  rows := #[⟨.count 2, 132196553554665600⟩, ⟨.count 3, 27096187995676800⟩, ⟨.count 4, 5108085201098880⟩, ⟨.count 5, 1051579863734400⟩, ⟨.count 6, 231330622723200⟩, ⟨.count 7, 58944822136200⟩, ⟨.count 8, 16608352400640⟩, ⟨.count 9, 5719713199200⟩, ⟨.count 10, 2639867630400⟩, ⟨.count 11, 2419878661200⟩, ⟨.path 13, 680815535400⟩, ⟨.path 14, 47979620325⟩, ⟨.privateRow 7 11, 340459119000⟩, ⟨.privateRow 8 9, 1149238670580⟩, ⟨.privateRow 8 10, 2076044050080⟩, ⟨.privateRow 9 6, 156762509904⟩, ⟨.privateRow 9 7, 692014683360⟩, ⟨.privateRow 9 8, 1196902947240⟩, ⟨.privateRow 10 4, 202656504960⟩, ⟨.privateRow 10 5, 384247399536⟩, ⟨.privateRow 10 6, 593155442880⟩, ⟨.privateRow 10 7, 351982350720⟩, ⟨.privateRow 11 2, 189434945700⟩, ⟨.privateRow 11 3, 235543744800⟩, ⟨.privateRow 12 0, 107174113200⟩, ⟨.privateRow 13 0, 56219403240⟩, ⟨.privateRow 14 0, 3851658720⟩, ⟨.hall 13 5, 2338507080⟩, ⟨.hall 8 8, 4263160720⟩, ⟨.hall 8 9, 362944764⟩, ⟨.hall 7 10, 10628552025⟩, ⟨.hall 6 12, 9106297200⟩, ⟨.hall 6 13, 60704083440⟩, ⟨.hall 9 14, 2720041388064⟩, ⟨.hall 5 15, 360037177500⟩, ⟨.hall 8 15, 37072215180⟩, ⟨.hall 4 18, 13442329476576⟩]
  caps := #[0, 0, 0, 0, 11037576555720, 463726936530, 3735792210150, 0, 739797638580, 69483094278, 83797681149, 123233338800, 0, 6182696520, 5611374405, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_24_12_checked :
    (Witness.linear .positive case_46_24_12).check 46 24 12 = true := by
  change case_46_24_12.check 46 24 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_24_13 : Certificate := {
  objectiveScale := 39501000000
  eta := 8337288614054400
  rows := #[⟨.count 2, 2616681491424000⟩, ⟨.count 3, 595520615289600⟩, ⟨.count 4, 129931770608640⟩, ⟨.count 5, 31976386041600⟩, ⟨.count 6, 7821830016000⟩, ⟨.count 7, 2224332910800⟩, ⟨.count 8, 664855551360⟩, ⟨.count 9, 217893836160⟩, ⟨.count 10, 83805321600⟩, ⟨.count 11, 41365447200⟩, ⟨.count 12, 38679379200⟩, ⟨.path 14, 1988336700⟩, ⟨.path 15, 7352069760⟩, ⟨.privateRow 4 20, 2991849981120⟩, ⟨.privateRow 8 10, 23512048560⟩, ⟨.privateRow 9 8, 16644668040⟩, ⟨.privateRow 9 9, 49618071360⟩, ⟨.privateRow 10 6, 9526587840⟩, ⟨.privateRow 10 7, 26027998920⟩, ⟨.privateRow 10 8, 44205004800⟩, ⟨.privateRow 11 4, 5318414640⟩, ⟨.privateRow 11 5, 13549720800⟩, ⟨.privateRow 11 6, 22764426300⟩, ⟨.privateRow 11 7, 7290756000⟩, ⟨.privateRow 12 2, 3418632000⟩, ⟨.privateRow 12 3, 7359826320⟩, ⟨.privateRow 12 4, 4715541600⟩, ⟨.privateRow 13 0, 3330724320⟩, ⟨.privateRow 14 0, 931170240⟩, ⟨.privateRow 15 0, 814773960⟩, ⟨.hall 15 1, 1551950400⟩, ⟨.hall 9 8, 12837312⟩, ⟨.hall 8 9, 455817600⟩, ⟨.hall 9 9, 309769920⟩, ⟨.hall 7 11, 1132032825⟩, ⟨.hall 7 12, 84532140⟩, ⟨.hall 10 13, 82884384000⟩, ⟨.hall 6 14, 12579927360⟩, ⟨.hall 5 16, 72805532800⟩, ⟨.hall 4 18, 365920498944⟩, ⟨.hall 4 19, 2478961412928⟩]
  caps := #[0, 0, 4029236303400, 1530780385680, 0, 171917305560, 1010809800, 5431826400, 6364137780, 2549469780, 572162580, 0, 1899032520, 0, 9395947260, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_24_13_checked :
    (Witness.linear .positive case_46_24_13).check 46 24 13 = true := by
  change case_46_24_13.check 46 24 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_24_14 : Certificate := {
  objectiveScale := 493802400000
  eta := 68972114898086400
  rows := #[⟨.count 2, 17829526300185600⟩, ⟨.count 3, 4680250653798720⟩, ⟨.count 4, 1244609592145920⟩, ⟨.count 5, 339551228016000⟩, ⟨.count 6, 103136415782400⟩, ⟨.count 7, 33047231817600⟩, ⟨.count 8, 11185216922880⟩, ⟨.count 9, 4031035968960⟩, ⟨.count 10, 1592301110400⟩, ⟨.count 11, 845036992800⟩, ⟨.count 12, 586637251200⟩, ⟨.count 13, 544734590400⟩, ⟨.count 15, 635523688800⟩, ⟨.path 12, 89243668800⟩, ⟨.privateRow 3 21, 140759418159360⟩, ⟨.privateRow 8 10, 223946442720⟩, ⟨.privateRow 9 8, 92302250040⟩, ⟨.privateRow 9 9, 885409873920⟩, ⟨.privateRow 10 6, 34453298880⟩, ⟨.privateRow 10 7, 395980144560⟩, ⟨.privateRow 10 8, 952986228480⟩, ⟨.privateRow 11 4, 5587021440⟩, ⟨.privateRow 11 5, 188561973600⟩, ⟨.privateRow 11 6, 478388710800⟩, ⟨.privateRow 11 7, 789166778400⟩, ⟨.privateRow 12 3, 50981570640⟩, ⟨.privateRow 12 4, 322805683200⟩, ⟨.privateRow 12 5, 305540235000⟩, ⟨.privateRow 13 1, 49521326400⟩, ⟨.privateRow 13 2, 103080545568⟩, ⟨.privateRow 14 0, 27511848000⟩, ⟨.hall 9 7, 2592462600⟩, ⟨.hall 8 8, 994188832⟩, ⟨.hall 9 8, 6513354432⟩, ⟨.hall 10 8, 516283200⟩, ⟨.hall 8 9, 13491387000⟩, ⟨.hall 10 9, 6614006400⟩, ⟨.hall 7 11, 27400197825⟩, ⟨.hall 7 12, 16288632360⟩, ⟨.hall 6 13, 105166158240⟩, ⟨.hall 5 16, 2357330976000⟩, ⟨.hall 4 18, 22634582338368⟩, ⟨.hall 3 20, 361952789552640⟩, ⟨.assumptionRow 14, 527506229250⟩]
  caps := #[0, 7758782031000, 16547768136900, 0, 0, 473283739500, 479363784900, 0, 97019722800, 34028456904, 31877190150, 37037379060, 31523510850, 0, 37544802750, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_24_14_checked :
    (Witness.linear .conditional case_46_24_14).check 46 24 14 = true := by
  change case_46_24_14.check 46 24 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_24_15 : Certificate := {
  objectiveScale := 190466640000
  eta := 16011383815627200
  rows := #[⟨.count 2, 4222782544780800⟩, ⟨.count 3, 1152467736179760⟩, ⟨.count 4, 333377569324800⟩, ⟨.count 5, 99293010616800⟩, ⟨.count 6, 30141980668800⟩, ⟨.count 7, 9930057637500⟩, ⟨.count 8, 3431827919520⟩, ⟨.count 9, 1252889557920⟩, ⟨.count 10, 460929268800⟩, ⟨.count 11, 192053862000⟩, ⟨.count 12, 125707982400⟩, ⟨.count 13, 108946918080⟩, ⟨.count 14, 127104737760⟩, ⟨.count 16, 181578196800⟩, ⟨.path 11, 29637293400⟩, ⟨.path 12, 5643752400⟩, ⟨.privateRow 3 21, 146624393916000⟩, ⟨.privateRow 9 9, 198006700320⟩, ⟨.privateRow 10 7, 56830483710⟩, ⟨.privateRow 10 8, 286733921760⟩, ⟨.privateRow 11 5, 12027615600⟩, ⟨.privateRow 11 6, 115014074175⟩, ⟨.privateRow 11 7, 289826737200⟩, ⟨.privateRow 12 4, 40932691800⟩, ⟨.privateRow 12 5, 131382301050⟩, ⟨.privateRow 12 6, 275859183600⟩, ⟨.privateRow 12 7, 46267521300⟩, ⟨.privateRow 13 2, 7751992248⟩, ⟨.privateRow 13 3, 67044257280⟩, ⟨.privateRow 13 4, 135659864340⟩, ⟨.privateRow 14 1, 29960402472⟩, ⟨.privateRow 14 2, 22865402560⟩, ⟨.privateRow 15 0, 10592061480⟩, ⟨.hall 10 7, 3097699200⟩, ⟨.hall 9 8, 5071854528⟩, ⟨.hall 10 8, 2023272000⟩, ⟨.hall 8 9, 843343956⟩, ⟨.hall 9 9, 2637509472⟩, ⟨.hall 8 10, 12710121060⟩, ⟨.hall 11 10, 10542816900⟩, ⟨.hall 11 11, 43458341850⟩, ⟨.hall 7 12, 31159968840⟩, ⟨.hall 6 14, 177735978420⟩, ⟨.hall 7 14, 162074117205⟩, ⟨.hall 5 15, 211144383450⟩, ⟨.hall 4 17, 1243938071376⟩, ⟨.hall 3 20, 202760590443840⟩, ⟨.assumptionRow 15, 111932659020⟩]
  caps := #[0, 0, 0, 2911617672600, 601474501680, 141214385520, 21051390360, 11030079060, 12059147100, 0, 3844599330, 5609997900, 0, 30790695936, 0, 0, 8888443200, 0, 0, 0, 0, 0, 0] }

theorem case_46_24_15_checked :
    (Witness.linear .conditional case_46_24_15).check 46 24 15 = true := by
  change case_46_24_15.check 46 24 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_25_1_checked :
    (Witness.rising).check 46 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_25_2_checked :
    (Witness.rising).check 46 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_25_3_checked :
    (Witness.rising).check 46 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_25_4_checked :
    (Witness.rising).check 46 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_25_5_checked :
    (Witness.rising).check 46 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_25_6_checked :
    (Witness.rising).check 46 25 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_25_7_checked :
    (Witness.rising).check 46 25 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_25_8_checked :
    (Witness.rising).check 46 25 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_25_9_checked :
    (Witness.rising).check 46 25 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_25_10 : Certificate := {
  objectiveScale := 96305664000000
  eta := 10444348827424512000
  rows := #[⟨.count 2, 2148551758784471040⟩, ⟨.count 3, 293698230184719360⟩, ⟨.count 4, 42929153075128320⟩, ⟨.count 5, 7390958922547200⟩, ⟨.count 6, 1462793953420800⟩, ⟨.count 7, 359282725401600⟩, ⟨.count 8, 123182648709120⟩, ⟨.count 9, 99493677803520⟩, ⟨.path 10, 28797060944925⟩, ⟨.path 11, 14240477771520⟩, ⟨.privateRow 5 16, 328487063224320⟩, ⟨.privateRow 6 12, 59345807320800⟩, ⟨.privateRow 6 13, 88904143785600⟩, ⟨.privateRow 6 14, 124038083769600⟩, ⟨.privateRow 6 15, 153978310886400⟩, ⟨.privateRow 7 8, 5832511776000⟩, ⟨.privateRow 7 9, 21556963524096⟩, ⟨.privateRow 7 10, 36498562580480⟩, ⟨.privateRow 7 12, 134547714512640⟩, ⟨.privateRow 7 14, 513261036288⟩, ⟨.privateRow 8 5, 3652049681280⟩, ⟨.privateRow 8 6, 9088997517600⟩, ⟨.privateRow 8 7, 13298126849280⟩, ⟨.privateRow 8 8, 16424353161216⟩, ⟨.privateRow 8 9, 1996015141120⟩, ⟨.privateRow 9 3, 8460346752000⟩, ⟨.privateRow 9 4, 121481902080⟩, ⟨.privateRow 10 0, 1998756920160⟩, ⟨.privateRow 11 0, 933201884160⟩, ⟨.hall 5 14, 76362366080⟩, ⟨.hall 5 15, 7945217280⟩, ⟨.hall 4 17, 1487041999872⟩, ⟨.hall 4 18, 9884455646208⟩, ⟨.hall 3 21, 3069767597944320⟩]
  caps := #[0, 47128123656934320, 0, 0, 71816240223000, 0, 23159136298740, 0, 7645420865992, 0, 0, 242449509120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_25_10_checked :
    (Witness.linear .positive case_46_25_10).check 46 25 10 = true := by
  change case_46_25_10.check 46 25 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_25_11 : Certificate := {
  objectiveScale := 26026000000
  eta := 4516031332612800
  rows := #[⟨.count 2, 1032235733168640⟩, ⟨.count 3, 162984589447680⟩, ⟨.count 4, 26752520995200⟩, ⟨.count 5, 5023663444800⟩, ⟨.count 6, 1066771906200⟩, ⟨.count 7, 254209475520⟩, ⟨.count 8, 72631278720⟩, ⟨.count 9, 29331862560⟩, ⟨.count 10, 24443218800⟩, ⟨.path 11, 3900776880⟩, ⟨.path 12, 5550565020⟩, ⟨.privateRow 6 13, 21616452000⟩, ⟨.privateRow 6 14, 76918541700⟩, ⟨.privateRow 6 15, 97598280780⟩, ⟨.privateRow 7 10, 8238270040⟩, ⟨.privateRow 7 11, 24021282285⟩, ⟨.privateRow 7 12, 35234816760⟩, ⟨.privateRow 7 13, 47412084720⟩, ⟨.privateRow 7 14, 54473459040⟩, ⟨.privateRow 8 7, 2407286700⟩, ⟨.privateRow 8 8, 8095361274⟩, ⟨.privateRow 8 9, 12357405060⟩, ⟨.privateRow 8 10, 8322334020⟩, ⟨.privateRow 8 11, 33397418340⟩, ⟨.privateRow 9 4, 501399360⟩, ⟨.privateRow 9 5, 2987504520⟩, ⟨.privateRow 9 6, 4655851200⟩, ⟨.privateRow 9 7, 6192282096⟩, ⟨.privateRow 9 8, 413853440⟩, ⟨.privateRow 10 2, 1272045060⟩, ⟨.privateRow 10 3, 1692222840⟩, ⟨.privateRow 11 0, 719540640⟩, ⟨.privateRow 12 0, 399072960⟩, ⟨.hall 5 16, 1355434080⟩, ⟨.hall 6 16, 304504200⟩, ⟨.hall 5 17, 123883760⟩, ⟨.hall 4 18, 16194894144⟩, ⟨.hall 6 18, 186356570400⟩, ⟨.hall 3 21, 1725818225040⟩]
  caps := #[0, 0, 0, 0, 229265400, 109523356800, 0, 2108230384, 2059728398, 3000232928, 1582781200, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_25_11_checked :
    (Witness.linear .positive case_46_25_11).check 46 25 11 = true := by
  change case_46_25_11.check 46 25 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_25_12 : Certificate := {
  objectiveScale := 80517937500
  eta := 19676993663527200
  rows := #[⟨.count 2, 5096663932520160⟩, ⟨.count 3, 911695047222960⟩, ⟨.count 4, 173171126288160⟩, ⟨.count 5, 35286696244800⟩, ⟨.count 6, 7739770638600⟩, ⟨.count 7, 1922459158620⟩, ⟨.count 8, 532629377280⟩, ⟨.count 9, 184371707520⟩, ⟨.count 10, 76821544800⟩, ⟨.count 11, 76821544800⟩, ⟨.path 13, 23226328125⟩, ⟨.privateRow 4 21, 10752455553840⟩, ⟨.privateRow 7 15, 112351509270⟩, ⟨.privateRow 7 18, 3154164593580⟩, ⟨.privateRow 8 11, 153963179370⟩, ⟨.privateRow 9 10, 89990952480⟩, ⟨.privateRow 10 6, 384107724⟩, ⟨.privateRow 10 10, 94426482150⟩, ⟨.privateRow 11 4, 5713999200⟩, ⟨.privateRow 11 10, 16411875480⟩, ⟨.privateRow 12 1, 2068272360⟩, ⟨.privateRow 12 6, 1440403965⟩, ⟨.privateRow 13 0, 1772804880⟩, ⟨.privateRow 14 0, 2774111340⟩, ⟨.hall 8 7, 83017935⟩, ⟨.hall 7 10, 148443295⟩, ⟨.hall 6 13, 785241600⟩, ⟨.hall 5 15, 4135401270⟩, ⟨.hall 4 18, 95028956880⟩]
  caps := #[0, 62542340160300, 0, 0, 187252515450, 0, 27113486400, 89793603900, 9318278970, 7802149212, 3696392700, 3696392700, 6508669860, 11210650605, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_25_12_checked :
    (Witness.linear .positive case_46_25_12).check 46 25 12 = true := by
  change case_46_25_12.check 46 25 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_25_13 : Certificate := {
  objectiveScale := 9759750000
  eta := 2815188363187200
  rows := #[⟨.count 2, 686202163526880⟩, ⟨.count 3, 163910638251360⟩, ⟨.count 4, 37865106639360⟩, ⟨.count 5, 9744696561600⟩, ⟨.count 6, 2519397480600⟩, ⟨.count 7, 646115750280⟩, ⟨.count 8, 193683409920⟩, ⟨.count 9, 58663725120⟩, ⟨.count 10, 20951330400⟩, ⟨.count 11, 10475665200⟩, ⟨.count 12, 8380532160⟩, ⟨.path 14, 1951950000⟩, ⟨.privateRow 13 0, 71628480⟩, ⟨.privateRow 13 5, 349188840⟩, ⟨.privateRow 14 0, 189143955⟩, ⟨.privateRow 14 3, 84063980⟩, ⟨.privateRow 14 11, 756575820⟩, ⟨.privateRow 15 0, 275118480⟩, ⟨.privateRow 15 3, 189143955⟩, ⟨.privateRow 16 5, 2269727460⟩, ⟨.hall 10 5, 101396160⟩, ⟨.hall 11 6, 4796550⟩, ⟨.hall 9 7, 37808442⟩, ⟨.hall 8 9, 161585424⟩, ⟨.hall 13 9, 9170616⟩, ⟨.hall 7 12, 368207840⟩, ⟨.hall 6 14, 229939710⟩]
  caps := #[0, 27014800612800, 2281832673120, 14122748640, 96416960640, 24813188400, 0, 1433512080, 0, 1846724880, 904263360, 0, 1692222840, 6608244720, 0, 6499674090, 0, 0, 0, 0, 0, 0] }

theorem case_46_25_13_checked :
    (Witness.linear .positive case_46_25_13).check 46 25 13 = true := by
  change case_46_25_13.check 46 25 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_25_14 : Certificate := {
  objectiveScale := 1316700000
  eta := 279714228393600
  rows := #[⟨.count 2, 66770493229440⟩, ⟨.count 3, 17666161793280⟩, ⟨.count 4, 4780628012160⟩, ⟨.count 5, 1312950038400⟩, ⟨.count 6, 377123947200⟩, ⟨.count 7, 112438806480⟩, ⟨.count 8, 36315639360⟩, ⟨.count 9, 12893126400⟩, ⟨.count 10, 5372136000⟩, ⟨.count 11, 2686068000⟩, ⟨.count 12, 1933968960⟩, ⟨.count 13, 1862340480⟩, ⟨.path 12, 263303040⟩, ⟨.privateRow 3 22, 2042056336320⟩, ⟨.privateRow 6 15, 35268072840⟩, ⟨.privateRow 7 13, 15053918880⟩, ⟨.privateRow 7 14, 44323703424⟩, ⟨.privateRow 7 15, 48537248760⟩, ⟨.privateRow 8 11, 6202258920⟩, ⟨.privateRow 8 12, 18235417200⟩, ⟨.privateRow 8 13, 32660796168⟩, ⟨.privateRow 8 14, 34511497020⟩, ⟨.privateRow 9 9, 2551764600⟩, ⟨.privateRow 9 10, 7715410560⟩, ⟨.privateRow 9 11, 14182439040⟩, ⟨.privateRow 9 12, 19511597952⟩, ⟨.privateRow 9 13, 17835491520⟩, ⟨.privateRow 10 7, 1074427200⟩, ⟨.privateRow 10 8, 3391160850⟩, ⟨.privateRow 10 9, 3200258160⟩, ⟨.privateRow 10 10, 15776172720⟩, ⟨.privateRow 10 11, 2524903920⟩, ⟨.privateRow 11 5, 478608480⟩, ⟨.privateRow 11 6, 949620000⟩, ⟨.privateRow 11 7, 4377069900⟩, ⟨.privateRow 11 8, 2030248800⟩, ⟨.privateRow 12 3, 131861520⟩, ⟨.privateRow 12 4, 1004589432⟩, ⟨.privateRow 12 5, 961015440⟩, ⟨.privateRow 13 1, 149226000⟩, ⟨.privateRow 13 2, 338607360⟩, ⟨.privateRow 14 0, 135795660⟩, ⟨.privateRow 15 0, 126977760⟩, ⟨.hall 7 14, 362121760⟩, ⟨.hall 6 15, 210134925⟩, ⟨.hall 7 15, 252952700⟩, ⟨.hall 6 16, 3956752800⟩, ⟨.hall 8 16, 49023374400⟩, ⟨.hall 5 17, 10313663360⟩, ⟨.hall 4 18, 13711306752⟩, ⟨.hall 3 20, 127667067840⟩, ⟨.assumptionRow 14, 1578670632⟩]
  caps := #[0, 1623480987744, 0, 38907396528, 0, 2870627760, 0, 840503664, 77515416, 95773920, 0, 400942224, 553889952, 0, 317289588, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_25_14_checked :
    (Witness.linear .conditional case_46_25_14).check 46 25 14 = true := by
  change case_46_25_14.check 46 25 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_25_15 : Certificate := {
  objectiveScale := 561632400000
  eta := 89030331985795200
  rows := #[⟨.count 2, 23741421862878720⟩, ⟨.count 3, 6474933235330560⟩, ⟨.count 4, 1808058842029440⟩, ⟨.count 5, 517861017273600⟩, ⟨.count 6, 153478970845200⟩, ⟨.count 7, 47261778323760⟩, ⟨.count 8, 15313094596800⟩, ⟨.count 9, 5011558231680⟩, ⟨.count 10, 1766895530400⟩, ⟨.count 11, 803134332000⟩, ⟨.count 12, 385504479360⟩, ⟨.count 13, 556839803520⟩, ⟨.count 14, 487234828080⟩, ⟨.path 11, 114715320720⟩, ⟨.privateRow 6 15, 10127523926520⟩, ⟨.privateRow 6 16, 40414388864850⟩, ⟨.privateRow 7 13, 3596257064400⟩, ⟨.privateRow 7 14, 17262033909120⟩, ⟨.privateRow 7 15, 36386000911260⟩, ⟨.privateRow 8 11, 1193228150400⟩, ⟨.privateRow 8 12, 6386256496620⟩, ⟨.privateRow 8 13, 14909385739248⟩, ⟨.privateRow 8 14, 23195858065380⟩, ⟨.privateRow 9 9, 361410449400⟩, ⟨.privateRow 9 10, 2377277622720⟩, ⟨.privateRow 9 11, 6057417606240⟩, ⟨.privateRow 9 12, 10387204027200⟩, ⟨.privateRow 9 13, 12834086625360⟩, ⟨.privateRow 10 7, 83882919120⟩, ⟨.privateRow 10 8, 885455601030⟩, ⟨.privateRow 10 9, 2537904489120⟩, ⟨.privateRow 10 10, 4730461215480⟩, ⟨.privateRow 10 11, 6621039433008⟩, ⟨.privateRow 10 12, 6878845553580⟩, ⟨.privateRow 11 6, 321253732800⟩, ⟨.privateRow 11 7, 1097008485300⟩, ⟨.privateRow 11 8, 1633387485600⟩, ⟨.privateRow 11 9, 4648444164000⟩, ⟨.privateRow 12 4, 81919701864⟩, ⟨.privateRow 12 5, 380150250480⟩, ⟨.privateRow 12 6, 1339226498610⟩, ⟨.privateRow 12 7, 683811516960⟩, ⟨.privateRow 13 2, 13628946240⟩, ⟨.privateRow 13 3, 201319005888⟩, ⟨.privateRow 13 4, 485450085120⟩, ⟨.privateRow 14 1, 88588150560⟩, ⟨.privateRow 14 2, 76565472984⟩, ⟨.privateRow 15 0, 31638625200⟩, ⟨.hall 8 12, 28138947408⟩, ⟨.hall 8 13, 29011821696⟩, ⟨.hall 7 14, 273512296057⟩, ⟨.hall 7 15, 69064740745⟩, ⟨.hall 9 15, 2734672400460⟩, ⟨.hall 6 16, 51359708400⟩, ⟨.hall 6 17, 23079544488000⟩, ⟨.hall 4 18, 6811448694336⟩, ⟨.hall 5 18, 41667736350240⟩, ⟨.hall 3 20, 67862139171840⟩, ⟨.hall 2 22, 1032235733168640⟩, ⟨.assumptionRow 15, 431842180770⟩]
  caps := #[0, 0, 52697581189680, 39303885533220, 1531326538560, 1692110164680, 337991914260, 102082600620, 0, 81955617744, 112311581382, 45475131030, 46337701410, 22773533076, 127598806692, 0, 561632400000, 0, 0, 0, 0, 0] }

theorem case_46_25_15_checked :
    (Witness.linear .conditional case_46_25_15).check 46 25 15 = true := by
  change case_46_25_15.check 46 25 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_25_16 : Certificate := {
  objectiveScale := 310810500000
  eta := 24280999632489600
  rows := #[⟨.count 2, 6879616562538720⟩, ⟨.count 3, 1959519268586880⟩, ⟨.count 4, 577442876250240⟩, ⟨.count 5, 174012438600000⟩, ⟨.count 6, 53247806211600⟩, ⟨.count 7, 16565984154720⟩, ⟨.count 8, 5150768182560⟩, ⟨.count 9, 1542017917440⟩, ⟨.count 10, 481880599200⟩, ⟨.count 11, 160626866400⟩, ⟨.count 12, 96376119840⟩, ⟨.count 13, 139209950880⟩, ⟨.path 11, 66444378000⟩, ⟨.privateRow 2 23, 1146602760423120⟩, ⟨.privateRow 6 15, 9849104024760⟩, ⟨.privateRow 6 16, 26449890667200⟩, ⟨.privateRow 7 13, 2830602334560⟩, ⟨.privateRow 7 14, 11700596371464⟩, ⟨.privateRow 7 15, 24013716526800⟩, ⟨.privateRow 8 11, 765654729840⟩, ⟨.privateRow 8 12, 3897878624640⟩, ⟨.privateRow 8 13, 9744696561600⟩, ⟨.privateRow 8 14, 16848754367445⟩, ⟨.privateRow 9 9, 182043781920⟩, ⟨.privateRow 9 10, 1268187354720⟩, ⟨.privateRow 9 11, 3655153582080⟩, ⟨.privateRow 9 12, 7146824709024⟩, ⟨.privateRow 9 13, 10472871689280⟩, ⟨.privateRow 10 7, 28555887360⟩, ⟨.privateRow 10 8, 389520151020⟩, ⟨.privateRow 10 9, 1371065038200⟩, ⟨.privateRow 10 10, 3015769416660⟩, ⟨.privateRow 10 11, 4934457335808⟩, ⟨.privateRow 10 12, 6107836594860⟩, ⟨.privateRow 11 6, 96538369200⟩, ⟨.privateRow 11 7, 502871610150⟩, ⟨.privateRow 11 8, 1303789500000⟩, ⟨.privateRow 11 9, 1580714389800⟩, ⟨.privateRow 11 10, 4967750904480⟩, ⟨.privateRow 12 4, 8031343320⟩, ⟨.privateRow 12 5, 164196352320⟩, ⟨.privateRow 12 6, 567213621975⟩, ⟨.privateRow 12 7, 1205848832760⟩, ⟨.privateRow 12 8, 1109663935380⟩, ⟨.privateRow 13 3, 26771144400⟩, ⟨.privateRow 13 4, 234396242080⟩, ⟨.privateRow 13 5, 626444778960⟩, ⟨.privateRow 13 6, 143799289920⟩, ⟨.privateRow 14 2, 62644477896⟩, ⟨.privateRow 14 3, 251351300200⟩, ⟨.privateRow 15 1, 80045721756⟩, ⟨.privateRow 16 0, 17401243860⟩, ⟨.hall 8 14, 322434812700⟩, ⟨.hall 8 15, 1820988989820⟩, ⟨.hall 9 15, 16576692612480⟩, ⟨.hall 7 16, 9653140997500⟩, ⟨.hall 6 17, 18407157869100⟩, ⟨.hall 4 18, 5437770953472⟩, ⟨.hall 5 18, 31739868800640⟩, ⟨.hall 3 20, 61868879598240⟩, ⟨.hall 2 22, 1325484521000640⟩, ⟨.assumptionRow 16, 75848455620⟩]
  caps := #[0, 757707406727040, 0, 7605401307840, 551246470320, 378481399920, 253057764960, 36657468540, 4236115620, 168827685312, 49656624732, 0, 0, 0, 96477860248, 353587872204, 0, 310810500000, 0, 0, 0, 0] }

theorem case_46_25_16_checked :
    (Witness.linear .conditional case_46_25_16).check 46 25 16 = true := by
  change case_46_25_16.check 46 25 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_26_1_checked :
    (Witness.rising).check 46 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_26_2_checked :
    (Witness.rising).check 46 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_26_3_checked :
    (Witness.rising).check 46 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_26_4_checked :
    (Witness.rising).check 46 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_26_5_checked :
    (Witness.rising).check 46 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_26_6_checked :
    (Witness.rising).check 46 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_26_7_checked :
    (Witness.rising).check 46 26 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_26_8_checked :
    (Witness.rising).check 46 26 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_26_9_checked :
    (Witness.rising).check 46 26 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_26_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_26_10_checked :
    (Witness.linear .positive case_46_26_10).check 46 26 10 = true := by
  change case_46_26_10.check 46 26 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_26_11 : Certificate := {
  objectiveScale := 359158800000
  eta := 77429409939161280
  rows := #[⟨.count 2, 15008781644176320⟩, ⟨.count 3, 2269539829196640⟩, ⟨.count 4, 378094226590080⟩, ⟨.count 5, 71867137141800⟩, ⟨.count 6, 15104279670480⟩, ⟨.count 7, 3654261210600⟩, ⟨.count 8, 1049428860480⟩, ⟨.count 9, 449755225920⟩, ⟨.count 10, 408868387200⟩, ⟨.path 11, 56814432675⟩, ⟨.path 12, 74511982545⟩, ⟨.privateRow 4 20, 7795757249280⟩, ⟨.privateRow 5 17, 4385113452720⟩, ⟨.privateRow 5 18, 5846817936960⟩, ⟨.privateRow 5 19, 8201786272680⟩, ⟨.privateRow 6 13, 294371041965⟩, ⟨.privateRow 6 14, 1171683753240⟩, ⟨.privateRow 6 15, 1813596304520⟩, ⟨.privateRow 6 16, 2582344588824⟩, ⟨.privateRow 6 17, 3146724931350⟩, ⟨.privateRow 6 18, 2598585749760⟩, ⟨.privateRow 7 10, 114848209476⟩, ⟨.privateRow 7 11, 382827364920⟩, ⟨.privateRow 7 12, 604693224135⟩, ⟨.privateRow 7 13, 735824026080⟩, ⟨.privateRow 7 14, 1020872973120⟩, ⟨.privateRow 7 15, 1051035129144⟩, ⟨.privateRow 8 7, 32794651890⟩, ⟨.privateRow 8 8, 129474989280⟩, ⟨.privateRow 8 9, 215507712420⟩, ⟨.privateRow 8 10, 289425816680⟩, ⟨.privateRow 8 11, 325604043765⟩, ⟨.privateRow 9 4, 6246600360⟩, ⟨.privateRow 9 5, 47089756560⟩, ⟨.privateRow 9 6, 83288004800⟩, ⟨.privateRow 9 7, 82909422960⟩, ⟨.privateRow 10 2, 19080524736⟩, ⟨.privateRow 10 3, 21903663600⟩, ⟨.privateRow 11 0, 8943995970⟩, ⟨.privateRow 12 0, 4997280288⟩, ⟨.privateRow 14 11, 52203731580⟩, ⟨.hall 12 7, 31201800⟩, ⟨.hall 4 20, 278419901760⟩, ⟨.hall 5 20, 3248232187200⟩, ⟨.hall 4 21, 15591514498560⟩, ⟨.hall 3 22, 51138472825440⟩]
  caps := #[0, 161576349654720, 0, 3225030528720, 0, 649646437440, 0, 3728837970, 18108060425, 0, 0, 5264878710, 0, 44172388260, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_26_11_checked :
    (Witness.linear .positive case_46_26_11).check 46 26 11 = true := by
  change case_46_26_11.check 46 26 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_26_12 : Certificate := {
  objectiveScale := 154326046875
  eta := 50450521458617280
  rows := #[⟨.count 2, 10152581717678400⟩, ⟨.count 3, 1874322778648320⟩, ⟨.count 4, 361389032484480⟩, ⟨.count 5, 73694267747100⟩, ⟨.count 6, 16461576691560⟩, ⟨.count 7, 4019687331660⟩, ⟨.count 8, 1060137318240⟩, ⟨.count 9, 353379106080⟩, ⟨.count 10, 160626866400⟩, ⟨.count 11, 176689553040⟩, ⟨.path 12, 5712121415⟩, ⟨.path 13, 40010717890⟩, ⟨.privateRow 6 16, 816698378496⟩, ⟨.privateRow 7 14, 2821073081970⟩, ⟨.privateRow 7 17, 2242274565960⟩, ⟨.privateRow 8 13, 2353406685630⟩, ⟨.privateRow 9 13, 755838643560⟩, ⟨.privateRow 10 7, 2409402996⟩, ⟨.privateRow 10 11, 111100249260⟩, ⟨.privateRow 10 13, 126493657290⟩, ⟨.privateRow 11 5, 10221709680⟩, ⟨.privateRow 11 11, 17668955304⟩, ⟨.privateRow 12 2, 4530501360⟩, ⟨.privateRow 12 10, 3926434512⟩, ⟨.privateRow 13 0, 3155170590⟩, ⟨.hall 13 2, 1051723530⟩, ⟨.hall 14 2, 2900207310⟩, ⟨.hall 15 3, 1160082924⟩, ⟨.hall 10 4, 52953912⟩, ⟨.hall 12 4, 14709420⟩, ⟨.hall 5 16, 968873620⟩, ⟨.hall 4 18, 67930269264⟩, ⟨.hall 3 21, 3704195214720⟩]
  caps := #[0, 0, 34592706057910, 0, 0, 0, 200528619720, 60940269390, 37239044700, 18132191220, 45846114314, 0, 51405916320, 0, 176689553040, 0, 0, 0, 0, 0, 0] }

theorem case_46_26_12_checked :
    (Witness.linear .positive case_46_26_12).check 46 26 12 = true := by
  change case_46_26_12.check 46 26 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_26_13 : Certificate := {
  objectiveScale := 195195000
  eta := 79177172714640
  rows := #[⟨.count 2, 17749268737200⟩, ⟨.count 3, 4347284661720⟩, ⟨.count 4, 1047100934880⟩, ⟨.count 5, 247778581050⟩, ⟨.count 6, 65065520520⟩, ⟨.count 7, 17401243860⟩, ⟨.count 8, 4655851200⟩, ⟨.count 9, 1396755360⟩, ⟨.count 10, 476166600⟩, ⟨.count 11, 174594420⟩, ⟨.count 12, 232792560⟩, ⟨.path 13, 22521785⟩, ⟨.path 14, 20642622⟩, ⟨.privateRow 11 14, 825355440⟩, ⟨.hall 11 4, 810084⟩, ⟨.hall 12 4, 29070⟩, ⟨.hall 7 15, 89789700⟩]
  caps := #[0, 280327507460, 12054774732, 2389818860, 2150015296, 465428535, 148917054, 0, 0, 40902147, 24953162, 43122365, 0, 0, 20642622, 0, 0, 0, 0, 0, 0] }

theorem case_46_26_13_checked :
    (Witness.linear .positive case_46_26_13).check 46 26 13 = true := by
  change case_46_26_13.check 46 26 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_26_14 : Certificate := {
  objectiveScale := 7977469500000
  eta := 2960258538527690400
  rows := #[⟨.count 2, 713414107623016800⟩, ⟨.count 3, 174936792673843200⟩, ⟨.count 4, 42447898222329600⟩, ⟨.count 5, 11757585445105500⟩, ⟨.count 6, 3336340485277800⟩, ⟨.count 7, 984823396256700⟩, ⟨.count 8, 309206717820000⟩, ⟨.count 9, 102038216880600⟩, ⟨.count 10, 42164552430000⟩, ⟨.count 11, 18552403069200⟩, ⟨.count 12, 12368268712800⟩, ⟨.path 12, 1994633290650⟩, ⟨.privateRow 4 20, 3376537358594400⟩, ⟨.privateRow 5 18, 1617924150993150⟩, ⟨.privateRow 5 19, 3644516514038400⟩, ⟨.privateRow 6 15, 94909284219750⟩, ⟨.privateRow 6 16, 592233933531240⟩, ⟨.privateRow 6 17, 1467185876055900⟩, ⟨.privateRow 6 18, 2221993830556500⟩, ⟨.privateRow 7 13, 68088581332200⟩, ⟨.privateRow 7 14, 244052445136500⟩, ⟨.privateRow 7 15, 567350154811440⟩, ⟨.privateRow 7 16, 896533835222025⟩, ⟨.privateRow 7 17, 1051818185117700⟩, ⟨.privateRow 8 11, 35558772549300⟩, ⟨.privateRow 8 12, 106455455706600⟩, ⟨.privateRow 8 13, 235254777808050⟩, ⟨.privateRow 8 14, 368574407641440⟩, ⟨.privateRow 8 15, 449895774428100⟩, ⟨.privateRow 8 16, 392177187101700⟩, ⟨.privateRow 9 9, 16949108976800⟩, ⟨.privateRow 9 10, 48184713526950⟩, ⟨.privateRow 9 11, 104541318882000⟩, ⟨.privateRow 9 12, 108909477276600⟩, ⟨.privateRow 9 13, 312504922810080⟩, ⟨.privateRow 10 7, 7842606751980⟩, ⟨.privateRow 10 8, 22768858312200⟩, ⟨.privateRow 10 9, 49859583248475⟩, ⟨.privateRow 10 10, 79871709317400⟩, ⟨.privateRow 10 11, 29655735209100⟩, ⟨.privateRow 11 5, 3756478307400⟩, ⟨.privateRow 11 6, 11300100051240⟩, ⟨.privateRow 11 7, 25579828474200⟩, ⟨.privateRow 11 8, 14968416112650⟩, ⟨.privateRow 12 3, 1975487363850⟩, ⟨.privateRow 12 4, 6090435351000⟩, ⟨.privateRow 12 5, 6184134356400⟩, ⟨.privateRow 13 0, 662585823900⟩, ⟨.privateRow 13 1, 594628303500⟩, ⟨.privateRow 13 2, 1803705853950⟩, ⟨.privateRow 14 0, 662585823900⟩, ⟨.privateRow 15 0, 558289907175⟩, ⟨.hall 6 18, 119003901266250⟩, ⟨.hall 7 18, 318401549165700⟩, ⟨.hall 6 19, 341673423191100⟩, ⟨.hall 5 20, 7355070748525500⟩, ⟨.hall 4 21, 15698706160737600⟩, ⟨.hall 3 22, 26620816276454400⟩, ⟨.hall 2 23, 25967180162523600⟩, ⟨.assumptionRow 14, 10394770398012⟩]
  caps := #[0, 4157799665619600, 138359699333856, 0, 207683845469100, 5603200522920, 8294257093122, 0, 0, 4057935625744, 0, 14452240871250, 5426577722412, 523940559912, 5577263179488, 1277990613900, 0, 0, 0, 0, 0] }

theorem case_46_26_14_checked :
    (Witness.linear .conditional case_46_26_14).check 46 26 14 = true := by
  change case_46_26_14.check 46 26 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_26_15 : Certificate := {
  objectiveScale := 188434400000
  eta := 48157315937771040
  rows := #[⟨.count 2, 12374790163575840⟩, ⟨.count 3, 3180668957706240⟩, ⟨.count 4, 836094964985280⟩, ⟨.count 5, 235699848083700⟩, ⟨.count 6, 68700110759280⟩, ⟨.count 7, 20829288900420⟩, ⟨.count 8, 6521450775840⟩, ⟨.count 9, 2023898516640⟩, ⟨.count 10, 766628226000⟩, ⟨.count 11, 337316419440⟩, ⟨.count 12, 224877612960⟩, ⟨.path 11, 42358290975⟩, ⟨.privateRow 2 24, 596375429569920⟩, ⟨.privateRow 4 20, 108166131833760⟩, ⟨.privateRow 5 18, 40836369028455⟩, ⟨.privateRow 5 19, 105364531572300⟩, ⟨.privateRow 6 15, 812058046800⟩, ⟨.privateRow 6 16, 14105448272916⟩, ⟨.privateRow 6 17, 39587829781500⟩, ⟨.privateRow 6 18, 68253478833540⟩, ⟨.privateRow 7 13, 499664287980⟩, ⟨.privateRow 7 14, 5142067560630⟩, ⟨.privateRow 7 15, 14804978276088⟩, ⟨.privateRow 7 16, 26911023629490⟩, ⟨.privateRow 7 17, 37273464348120⟩, ⟨.privateRow 8 11, 203795336745⟩, ⟨.privateRow 8 12, 1927522396800⟩, ⟨.privateRow 8 13, 5762488832100⟩, ⟨.privateRow 8 14, 10929051989856⟩, ⟨.privateRow 8 15, 15706295780175⟩, ⟨.privateRow 8 16, 17278096595760⟩, ⟨.privateRow 9 9, 62466003600⟩, ⟨.privateRow 9 10, 730852242120⟩, ⟨.privateRow 9 11, 2329089562800⟩, ⟨.privateRow 9 12, 4669333769100⟩, ⟨.privateRow 9 13, 3695488772976⟩, ⟨.privateRow 9 14, 14879402057520⟩, ⟨.privateRow 9 15, 662139638160⟩, ⟨.privateRow 10 7, 6133025808⟩, ⟨.privateRow 10 8, 275986161360⟩, ⟨.privateRow 10 9, 977450988150⟩, ⟨.privateRow 10 10, 2113703537400⟩, ⟨.privateRow 10 11, 3396163041180⟩, ⟨.privateRow 10 12, 2756795100696⟩, ⟨.privateRow 11 6, 88928874216⟩, ⟨.privateRow 11 7, 425904570000⟩, ⟨.privateRow 11 8, 1015782399450⟩, ⟨.privateRow 11 9, 1673439899040⟩, ⟨.privateRow 12 4, 25554274200⟩, ⟨.privateRow 12 5, 176154130152⟩, ⟨.privateRow 12 6, 518467829880⟩, ⟨.privateRow 12 7, 285781966470⟩, ⟨.privateRow 13 2, 2342475135⟩, ⟨.privateRow 13 3, 79218250020⟩, ⟨.privateRow 13 4, 188335000854⟩, ⟨.privateRow 14 1, 30452176755⟩, ⟨.privateRow 14 2, 28474762680⟩, ⟨.privateRow 15 0, 10150725585⟩, ⟨.hall 7 18, 31426646411160⟩, ⟨.hall 6 19, 110870285129604⟩, ⟨.hall 5 20, 260235601926300⟩, ⟨.hall 4 21, 503623635933600⟩, ⟨.hall 3 22, 829739728097280⟩, ⟨.hall 2 23, 993959049283200⟩, ⟨.assumptionRow 15, 166264968870⟩]
  caps := #[0, 1170484589021440, 61295830013880, 10187032519510, 0, 885881505600, 146556682272, 376347048220, 0, 62728758015, 316028771786, 15402378145, 0, 199234524398, 342366249645, 33058584020, 188434400000, 0, 0, 0, 0] }

theorem case_46_26_15_checked :
    (Witness.linear .conditional case_46_26_15).check 46 26 15 = true := by
  change case_46_26_15.check 46 26 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_26_16 : Certificate := {
  objectiveScale := 621621000000
  eta := 155803080975141600
  rows := #[⟨.count 2, 38466215207259840⟩, ⟨.count 3, 9542006873118720⟩, ⟨.count 4, 2525825348766720⟩, ⟨.count 5, 676038323961000⟩, ⟨.count 6, 182713060530000⟩, ⟨.count 7, 49697952464160⟩, ⟨.count 8, 13492656777600⟩, ⟨.count 9, 4047797033280⟩, ⟨.count 10, 1226605161600⟩, ⟨.count 11, 674632838880⟩, ⟨.count 12, 449755225920⟩, ⟨.path 10, 165813822720⟩, ⟨.path 11, 55288007775⟩, ⟨.privateRow 2 24, 3130971005242080⟩, ⟨.privateRow 4 20, 438511345272000⟩, ⟨.privateRow 5 17, 7747033766472⟩, ⟨.privateRow 5 18, 142150761092340⟩, ⟨.privateRow 5 19, 398070854541360⟩, ⟨.privateRow 6 15, 4263304745700⟩, ⟨.privateRow 6 16, 47310501806568⟩, ⟨.privateRow 6 17, 140140917426510⟩, ⟨.privateRow 6 18, 264812129061480⟩, ⟨.privateRow 7 13, 1506450539880⟩, ⟨.privateRow 7 14, 15835131912600⟩, ⟨.privateRow 7 15, 50115582316800⟩, ⟨.privateRow 7 16, 100492183291500⟩, ⟨.privateRow 7 17, 155671527571560⟩, ⟨.privateRow 8 11, 358398695655⟩, ⟨.privateRow 8 12, 5204310471360⟩, ⟨.privateRow 8 13, 18186976948140⟩, ⟨.privateRow 8 14, 39286118984112⟩, ⟨.privateRow 8 15, 64118229395220⟩, ⟨.privateRow 8 16, 81593093902320⟩, ⟨.privateRow 9 10, 1616307843150⟩, ⟨.privateRow 9 11, 6644598040080⟩, ⟨.privateRow 9 12, 15866364914400⟩, ⟨.privateRow 9 13, 27787377041424⟩, ⟨.privateRow 9 14, 38023056391320⟩, ⟨.privateRow 9 15, 37866891382320⟩, ⟨.privateRow 10 8, 350945365680⟩, ⟨.privateRow 10 9, 2388046923990⟩, ⟨.privateRow 10 10, 6597383476320⟩, ⟨.privateRow 10 11, 12715806841920⟩, ⟨.privateRow 10 12, 18926517643488⟩, ⟨.privateRow 10 13, 14351280390720⟩, ⟨.privateRow 11 6, 49064206464⟩, ⟨.privateRow 11 7, 732555860400⟩, ⟨.privateRow 11 8, 2782860460380⟩, ⟨.privateRow 11 9, 5291925125760⟩, ⟨.privateRow 11 10, 11806074680400⟩, ⟨.privateRow 12 5, 172406169936⟩, ⟨.privateRow 12 6, 1078579662160⟩, ⟨.privateRow 12 7, 3059272526310⟩, ⟨.privateRow 12 8, 3207183099120⟩, ⟨.privateRow 13 3, 5110854840⟩, ⟨.privateRow 13 4, 365426121060⟩, ⟨.privateRow 13 5, 1467951084600⟩, ⟨.privateRow 13 6, 639495711855⟩, ⟨.privateRow 14 2, 56949525360⟩, ⟨.privateRow 14 3, 657767017908⟩, ⟨.privateRow 15 1, 177176301120⟩, ⟨.hall 7 17, 2955463891380⟩, ⟨.hall 8 17, 29908722523680⟩, ⟨.hall 7 18, 149824709634600⟩, ⟨.hall 6 19, 538418846769804⟩, ⟨.hall 5 20, 1126382515057800⟩, ⟨.hall 4 21, 2050106980259520⟩, ⟨.hall 3 22, 3305994229137600⟩, ⟨.hall 2 23, 4224325959453600⟩, ⟨.assumptionRow 16, 284611317760⟩]
  caps := #[0, 0, 0, 0, 811954583440, 381486103544, 0, 0, 595466145729, 211228456712, 82924108575, 8050086135, 0, 1146785969420, 487964364804, 284611317760, 5309977682240, 621621000000, 0, 0, 0] }

theorem case_46_26_16_checked :
    (Witness.linear .conditional case_46_26_16).check 46 26 16 = true := by
  change case_46_26_16.check 46 26 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_27_1_checked :
    (Witness.rising).check 46 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_27_2_checked :
    (Witness.rising).check 46 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_27_3_checked :
    (Witness.rising).check 46 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_27_4_checked :
    (Witness.rising).check 46 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_27_5_checked :
    (Witness.rising).check 46 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_27_6_checked :
    (Witness.rising).check 46 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_27_7_checked :
    (Witness.rising).check 46 27 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_27_8_checked :
    (Witness.rising).check 46 27 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_27_9_checked :
    (Witness.rising).check 46 27 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_27_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_27_10_checked :
    (Witness.linear .positive case_46_27_10).check 46 27 10 = true := by
  change case_46_27_10.check 46 27 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_27_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_27_11_checked :
    (Witness.linear .positive case_46_27_11).check 46 27 11 = true := by
  change case_46_27_11.check 46 27 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_27_12 : Certificate := {
  objectiveScale := 761852000000
  eta := 424917493568568000
  rows := #[⟨.count 2, 85977457762996800⟩, ⟨.count 3, 17189644734662400⟩, ⟨.count 4, 3727346434812000⟩, ⟨.count 5, 796628943910800⟩, ⟨.count 6, 175404538108800⟩, ⟨.count 7, 42164552430000⟩, ⟨.count 8, 10119492583200⟩, ⟨.count 9, 2759861613600⟩, ⟨.count 10, 919953871200⟩, ⟨.count 11, 1124388064800⟩, ⟨.path 12, 293036848650⟩, ⟨.privateRow 6 17, 109105799002200⟩, ⟨.privateRow 6 18, 29103580355850⟩, ⟨.privateRow 6 19, 60730341071400⟩, ⟨.privateRow 7 16, 101628618371280⟩, ⟨.privateRow 7 17, 51862399488900⟩, ⟨.privateRow 10 13, 809559406656⟩, ⟨.privateRow 12 4, 11712375675⟩, ⟨.privateRow 12 12, 35137127025⟩, ⟨.privateRow 13 0, 16062686640⟩, ⟨.hall 13 2, 11473347600⟩, ⟨.hall 14 4, 4088683872⟩, ⟨.hall 9 7, 1396234665⟩, ⟨.hall 6 14, 13456910610⟩, ⟨.hall 8 15, 70274254050⟩, ⟨.hall 5 16, 49743493800⟩, ⟨.hall 4 19, 606017231820⟩, ⟨.hall 4 20, 4774681220400⟩]
  caps := #[0, 0, 244903172614100, 40781309032100, 12383885213700, 0, 876126262830, 0, 519603575400, 170506872900, 134934977450, 0, 0, 3324976134480, 2088149263200, 0, 0, 0, 0, 0] }

theorem case_46_27_12_checked :
    (Witness.linear .positive case_46_27_12).check 46 27 12 = true := by
  change case_46_27_12.check 46 27 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_27_13 : Certificate := {
  objectiveScale := 743600000
  eta := 441416596420800
  rows := #[⟨.count 2, 100356251835840⟩, ⟨.count 3, 25033580732160⟩, ⟨.count 4, 6158527174800⟩, ⟨.count 5, 1486923678240⟩, ⟨.count 6, 380449555200⟩, ⟨.count 7, 102428726400⟩, ⟨.count 8, 27314327040⟩, ⟨.count 9, 8380532160⟩, ⟨.count 10, 2793510720⟩, ⟨.count 11, 1707145440⟩, ⟨.path 12, 223107885⟩, ⟨.hall 10 9, 1939140⟩, ⟨.hall 11 9, 3986466⟩]
  caps := #[0, 644050178200, 216170524570, 0, 0, 2082526160, 2403575460, 647116470, 797266470, 0, 154708840, 0, 966707885, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_27_13_checked :
    (Witness.linear .positive case_46_27_13).check 46 27 13 = true := by
  change case_46_27_13.check 46 27 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_27_14 : Certificate := {
  objectiveScale := 2539765800000
  eta := 2066440863459772800
  rows := #[⟨.count 2, 459209080768838400⟩, ⟨.count 3, 102260845717430400⟩, ⟨.count 4, 24439698976492800⟩, ⟨.count 5, 5788349757590400⟩, ⟨.count 6, 1538966006978400⟩, ⟨.count 7, 420521136235200⟩, ⟨.count 8, 123682687128000⟩, ⟨.count 9, 33731641944000⟩, ⟨.count 10, 13492656777600⟩, ⟨.count 11, 8245512475200⟩, ⟨.path 11, 1209396988800⟩, ⟨.privateRow 2 25, 1822258257019200⟩, ⟨.privateRow 4 20, 331624204861950⟩, ⟨.privateRow 4 21, 3202350907555800⟩, ⟨.privateRow 5 18, 435198148441056⟩, ⟨.privateRow 5 19, 1197866824834680⟩, ⟨.privateRow 5 20, 2490419617926240⟩, ⟨.privateRow 6 16, 255856288888200⟩, ⟨.privateRow 6 17, 498441229125840⟩, ⟨.privateRow 6 18, 948454796589300⟩, ⟨.privateRow 6 19, 1281195581265600⟩, ⟨.privateRow 7 13, 17227231421400⟩, ⟨.privateRow 7 14, 103742008999200⟩, ⟨.privateRow 7 15, 219095045769600⟩, ⟨.privateRow 7 16, 386596742051520⟩, ⟨.privateRow 7 17, 507982464990000⟩, ⟨.privateRow 7 18, 520056251114400⟩, ⟨.privateRow 8 11, 14200604818400⟩, ⟨.privateRow 8 12, 45736827010875⟩, ⟨.privateRow 8 13, 91584084992400⟩, ⟨.privateRow 8 14, 170750820840600⟩, ⟨.privateRow 8 15, 219742907464080⟩, ⟨.privateRow 8 16, 200726694318150⟩, ⟨.privateRow 9 9, 8320471679520⟩, ⟨.privateRow 9 10, 22404473291200⟩, ⟨.privateRow 9 11, 41040164365200⟩, ⟨.privateRow 9 12, 78064657070400⟩, ⟨.privateRow 9 13, 97197101601600⟩, ⟨.privateRow 10 7, 4354448323680⟩, ⟨.privateRow 10 8, 11806074680400⟩, ⟨.privateRow 10 9, 21438332435520⟩, ⟨.privateRow 10 10, 38116755396720⟩, ⟨.privateRow 11 5, 2248776129600⟩, ⟨.privateRow 11 6, 6610038926400⟩, ⟨.privateRow 11 7, 12068431895520⟩, ⟨.privateRow 12 3, 1189256607000⟩, ⟨.privateRow 12 4, 3779193217800⟩, ⟨.privateRow 13 1, 757240941600⟩, ⟨.privateRow 13 2, 271830081600⟩, ⟨.privateRow 14 0, 273448117800⟩, ⟨.hall 6 20, 549083820542400⟩, ⟨.hall 5 21, 2825962002864000⟩, ⟨.hall 4 22, 7501086098906400⟩, ⟨.hall 3 23, 15033630620408400⟩, ⟨.hall 2 24, 19243047194122752⟩, ⟨.assumptionRow 14, 3353393883840⟩]
  caps := #[0, 12327770345404800, 796280919033600, 0, 49161414111810, 0, 3387856174560, 3052209766320, 4688593427375, 3056487994560, 4199565158880, 0, 10983824174400, 3529205122080, 0, 2539765800000, 0, 0, 0, 0] }

theorem case_46_27_14_checked :
    (Witness.linear .conditional case_46_27_14).check 46 27 14 = true := by
  change case_46_27_14.check 46 27 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_27_15 : Certificate := {
  objectiveScale := 223133994745200000
  eta := 171448711564395127262400
  rows := #[⟨.count 2, 35614949745260823537600⟩, ⟨.count 3, 8282546452386238032000⟩, ⟨.count 4, 1900113597900372254400⟩, ⟨.count 5, 430367609780853544800⟩, ⟨.count 6, 107881907573098058400⟩, ⟨.count 7, 28108189318052844000⟩, ⟨.count 8, 7495517151480758400⟩, ⟨.count 9, 2044231950403843200⟩, ⟨.count 10, 511057987600960800⟩, ⟨.count 11, 624626429290063200⟩, ⟨.path 9, 151479359110759680⟩, ⟨.path 10, 56468649823185600⟩, ⟨.privateRow 2 25, 1794551731350351573600⟩, ⟨.privateRow 4 20, 81455190294607304175⟩, ⟨.privateRow 4 21, 354241263711127092300⟩, ⟨.privateRow 5 18, 51644113173702425376⟩, ⟨.privateRow 5 19, 131546326008487309920⟩, ⟨.privateRow 5 20, 282039653705439870240⟩, ⟨.privateRow 6 16, 23490415358658448200⟩, ⟨.privateRow 6 17, 51794915840202454920⟩, ⟨.privateRow 6 18, 106431881933674697400⟩, ⟨.privateRow 6 19, 157279447689453889800⟩, ⟨.privateRow 7 13, 719435798021590650⟩, ⟨.privateRow 7 14, 8681032619317000800⟩, ⟨.privateRow 7 15, 20969601554737836000⟩, ⟨.privateRow 7 16, 42403211314091147520⟩, ⟨.privateRow 7 17, 63009191054635125300⟩, ⟨.privateRow 7 18, 74642858300162552400⟩, ⟨.privateRow 8 11, 477145189041020500⟩, ⟨.privateRow 8 12, 3357367057434089700⟩, ⟨.privateRow 8 13, 8320916361614056200⟩, ⟨.privateRow 8 14, 17931983740868897700⟩, ⟨.privateRow 8 15, 27155634013385497620⟩, ⟨.privateRow 8 16, 32949044145050833800⟩, ⟨.privateRow 8 17, 26052127321639719300⟩, ⟨.privateRow 9 9, 198744772955929200⟩, ⟨.privateRow 9 10, 1369130658140845600⟩, ⟨.privateRow 9 11, 3478033526728761000⟩, ⟨.privateRow 9 12, 7811886381900400800⟩, ⟨.privateRow 9 13, 12776449690024020000⟩, ⟨.privateRow 9 14, 16058577654839079360⟩, ⟨.privateRow 10 7, 51105798760096080⟩, ⟨.privateRow 10 8, 567274366237066488⟩, ⟨.privateRow 10 9, 1567244495309613120⟩, ⟨.privateRow 10 10, 3666841061036893740⟩, ⟨.privateRow 10 11, 6424728986983507200⟩, ⟨.privateRow 10 12, 2470113606737977200⟩, ⟨.privateRow 11 6, 221974681483245600⟩, ⟨.privateRow 11 7, 687089072219069520⟩, ⟨.privateRow 11 8, 2012685161045759200⟩, ⟨.privateRow 11 9, 1888075343081327400⟩, ⟨.privateRow 12 4, 58558727745943425⟩, ⟨.privateRow 12 5, 354901380278445000⟩, ⟨.privateRow 12 6, 991594456497975330⟩, ⟨.privateRow 13 2, 10296040043242800⟩, ⟨.privateRow 13 3, 145002563942336100⟩, ⟨.privateRow 13 4, 206856804505150800⟩, ⟨.privateRow 14 1, 66924260281078200⟩, ⟨.privateRow 14 2, 24167093990389350⟩, ⟨.hall 6 20, 122630739791232816000⟩, ⟨.hall 5 21, 410251799546671282200⟩, ⟨.hall 4 22, 959589141414569265600⟩, ⟨.hall 3 23, 1857482844101325441000⟩, ⟨.hall 2 24, 2771892212731927661376⟩, ⟨.assumptionRow 15, 210288990343617900⟩]
  caps := #[0, 0, 16756935416579385720, 0, 6125185343517585345, 2259021143933769072, 377092487015552880, 494239052971083420, 0, 142350281348234960, 340093024470851652, 0, 210957538498791975, 2088362493552881700, 210288990343617900, 2244184951853582100, 223133994745200000, 0, 0, 0] }

theorem case_46_27_15_checked :
    (Witness.linear .conditional case_46_27_15).check 46 27 15 = true := by
  change case_46_27_15.check 46 27 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_27_16 : Certificate := {
  objectiveScale := 6231388693250952000000
  eta := 5745589221946009504817548800
  rows := #[⟨.count 2, 1133389178242167736457568000⟩, ⟨.count 3, 244093659755876220792902400⟩, ⟨.count 4, 51227013878532551353694400⟩, ⟨.count 5, 10476706689633483278179200⟩, ⟨.count 6, 2245008576350032131038400⟩, ⟨.count 7, 470980820213293454064000⟩, ⟨.count 8, 94196164042658690812800⟩, ⟨.count 9, 34253150560966796659200⟩, ⟨.count 10, 8563287640241699164800⟩, ⟨.count 11, 10466240449184298979200⟩, ⟨.path 8, 8216903893089936844800⟩, ⟨.path 9, 4766597414885697431040⟩, ⟨.privateRow 2 25, 55512939342473521785676800⟩, ⟨.privateRow 4 20, 2359810151277022410466500⟩, ⟨.privateRow 4 21, 10561744893283105707385200⟩, ⟨.privateRow 5 18, 1393265928595413880111104⟩, ⟨.privateRow 5 19, 3765491657605281165241680⟩, ⟨.privateRow 5 20, 8689770570276083965797120⟩, ⟨.privateRow 6 16, 579879560125044374395200⟩, ⟨.privateRow 6 17, 1410176382806881654604640⟩, ⟨.privateRow 6 18, 3184073310938005527841800⟩, ⟨.privateRow 6 19, 5207577613972116378996000⟩, ⟨.privateRow 7 13, 11213829052697463192000⟩, ⟨.privateRow 7 14, 195120625516935859540800⟩, ⟨.privateRow 7 15, 534152057210155830045600⟩, ⟨.privateRow 7 16, 1221858813581915589400320⟩, ⟨.privateRow 7 17, 2052691408096270637295600⟩, ⟨.privateRow 7 18, 2780282016465457707403200⟩, ⟨.privateRow 8 11, 4651662421859688435200⟩, ⟨.privateRow 8 12, 65904607828457382634650⟩, ⟨.privateRow 8 13, 195681316969570732700400⟩, ⟨.privateRow 8 14, 489514787675390650173000⟩, ⟨.privateRow 8 15, 859539996889260553666800⟩, ⟨.privateRow 8 16, 1212775612049230644214800⟩, ⟨.privateRow 8 17, 1319182389949271017170000⟩, ⟨.privateRow 9 9, 95147640447129990720⟩, ⟨.privateRow 9 10, 21566798501349464563200⟩, ⟨.privateRow 9 11, 73263683144290092854400⟩, ⟨.privateRow 9 12, 199266344136417951993600⟩, ⟨.privateRow 9 13, 384713626207895595811200⟩, ⟨.privateRow 9 14, 574882043581559403930240⟩, ⟨.privateRow 9 15, 640105751108067012568800⟩, ⟨.privateRow 10 8, 4624175325730517548992⟩, ⟨.privateRow 10 9, 27592815729667697308800⟩, ⟨.privateRow 10 10, 84776547638392821731520⟩, ⟨.privateRow 10 11, 180807701889674733793920⟩, ⟨.privateRow 10 12, 298145131341081825921120⟩, ⟨.privateRow 10 13, 140951714558378368252608⟩, ⟨.privateRow 11 6, 432489274759681776000⟩, ⟨.privateRow 11 7, 8372992359347439183360⟩, ⟨.privateRow 11 8, 37213299374877507481600⟩, ⟨.privateRow 11 9, 90628127525891316160800⟩, ⟨.privateRow 11 10, 134430023431730801174400⟩, ⟨.privateRow 12 0, 81767503509252335775⟩, ⟨.privateRow 12 5, 1308280056148037372400⟩, ⟨.privateRow 12 6, 14391080617628411096400⟩, ⟨.privateRow 12 7, 47970268725428036988000⟩, ⟨.privateRow 12 8, 31071651333515887594500⟩, ⟨.privateRow 13 4, 3873868218204578193600⟩, ⟨.privateRow 13 5, 23324764429610723439360⟩, ⟨.privateRow 13 6, 2741158212881602113600⟩, ⟨.privateRow 14 2, 404943826902963948600⟩, ⟨.privateRow 14 3, 7951624237367292081600⟩, ⟨.privateRow 15 1, 2267685430656598112160⟩, ⟨.hall 7 19, 1084825822557952589194080⟩, ⟨.hall 6 20, 5970028990912268499360000⟩, ⟨.hall 5 21, 15708875437821161467872000⟩, ⟨.hall 4 22, 33009612268862132519616000⟩, ⟨.hall 3 23, 60241063465392528849530400⟩, ⟨.hall 2 24, 87340357898825007609464832⟩, ⟨.assumptionRow 16, 3583671637488622495200⟩]
  caps := #[0, 0, 0, 830292303906093166959744, 0, 0, 19023632210596111698600, 5218787225434385082480, 4106781748350640509920, 16021204027774787761920, 4051729266916739829120, 475268273129650656600, 13651797750502962475425, 3583671637488622495200, 15306006960085845003000, 3583671637488622495200, 58730215295020897504800, 6231388693250952000000, 0, 0] }

theorem case_46_27_16_checked :
    (Witness.linear .conditional case_46_27_16).check 46 27 16 = true := by
  change case_46_27_16.check 46 27 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_27_17 : Certificate := {
  objectiveScale := 276276000000
  eta := 227081413567008000
  rows := #[⟨.count 2, 50742883772380800⟩, ⟨.count 3, 12269322563097600⟩, ⟨.count 4, 2956016222359200⟩, ⟨.count 5, 709114072867200⟩, ⟨.count 6, 166088179857600⟩, ⟨.count 7, 38056211424000⟩, ⟨.count 8, 8245512475200⟩, ⟨.count 9, 1556845012800⟩, ⟨.path 10, 238306068000⟩, ⟨.path 11, 1816214400⟩, ⟨.privateRow 4 20, 79620729838650⟩, ⟨.privateRow 5 18, 50627446597728⟩, ⟨.privateRow 5 19, 197067748157280⟩, ⟨.privateRow 5 20, 330095349423840⟩, ⟨.privateRow 6 16, 22331596287000⟩, ⟨.privateRow 6 18, 325182398240700⟩, ⟨.privateRow 6 19, 187879891399200⟩, ⟨.privateRow 7 14, 8446148964000⟩, ⟨.privateRow 7 16, 93264900996960⟩, ⟨.privateRow 7 17, 142337026477800⟩, ⟨.privateRow 7 18, 156347601933600⟩, ⟨.privateRow 8 12, 2903768215425⟩, ⟨.privateRow 8 13, 9604662883200⟩, ⟨.privateRow 8 14, 12896827204800⟩, ⟨.privateRow 8 16, 211093047742500⟩, ⟨.privateRow 8 17, 34277018206200⟩, ⟨.privateRow 9 10, 916168052800⟩, ⟨.privateRow 9 11, 3445240352400⟩, ⟨.privateRow 9 12, 10230695798400⟩, ⟨.privateRow 9 15, 154776341689200⟩, ⟨.privateRow 9 16, 11378422809600⟩, ⟨.privateRow 10 7, 4717712160⟩, ⟨.privateRow 10 8, 259474168800⟩, ⟨.privateRow 10 9, 1193581176480⟩, ⟨.privateRow 10 10, 4080231304380⟩, ⟨.privateRow 10 11, 9645025531680⟩, ⟨.privateRow 10 12, 4670535038400⟩, ⟨.privateRow 10 13, 3643017329952⟩, ⟨.privateRow 10 14, 48807091151280⟩, ⟨.privateRow 11 6, 52419024000⟩, ⟨.privateRow 11 9, 2551495993200⟩, ⟨.privateRow 11 12, 30387308212800⟩, ⟨.privateRow 12 4, 6606981150⟩, ⟨.privateRow 12 5, 93699005400⟩, ⟨.privateRow 12 6, 134782415460⟩, ⟨.privateRow 12 10, 12579692109600⟩, ⟨.privateRow 13 3, 11326253400⟩, ⟨.privateRow 13 5, 448519634640⟩, ⟨.privateRow 13 11, 7475327244000⟩, ⟨.privateRow 14 9, 765654729840⟩, ⟨.privateRow 14 11, 294482588400⟩, ⟨.privateRow 15 5, 103068905940⟩, ⟨.hall 13 3, 21843488700⟩, ⟨.hall 14 4, 5766092640⟩, ⟨.hall 6 17, 486080783760⟩, ⟨.hall 7 17, 1005930266880⟩, ⟨.hall 5 18, 966015610560⟩, ⟨.hall 4 19, 1671566977080⟩, ⟨.hall 3 21, 19652347915200⟩, ⟨.hall 2 24, 5113537016620032⟩]
  caps := #[0, 96948287436000, 0, 13318465864704, 4313558839590, 0, 928567951740, 351245664000, 495795550635, 285993796200, 456641371788, 4234692000, 492684425310, 0, 3615298006320, 0, 12156144000000, 2486484000000, 276276000000, 0] }

theorem case_46_27_17_checked :
    (Witness.linear .negative case_46_27_17).check 46 27 17 = true := by
  change case_46_27_17.check 46 27 17 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_28_1_checked :
    (Witness.rising).check 46 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_28_2_checked :
    (Witness.rising).check 46 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_28_3_checked :
    (Witness.rising).check 46 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_28_4_checked :
    (Witness.rising).check 46 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_28_5_checked :
    (Witness.rising).check 46 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_28_6_checked :
    (Witness.rising).check 46 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_28_7_checked :
    (Witness.rising).check 46 28 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_28_8_checked :
    (Witness.rising).check 46 28 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_28_9_checked :
    (Witness.rising).check 46 28 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_28_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_28_10_checked :
    (Witness.linear .positive case_46_28_10).check 46 28 10 = true := by
  change case_46_28_10.check 46 28 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_28_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_28_11_checked :
    (Witness.linear .positive case_46_28_11).check 46 28 11 = true := by
  change case_46_28_11.check 46 28 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_28_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_28_12_checked :
    (Witness.linear .positive case_46_28_12).check 46 28 12 = true := by
  change case_46_28_12.check 46 28 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_28_13 : Certificate := {
  objectiveScale := 743600000
  eta := 1119387215026080
  rows := #[⟨.count 2, 246030386521920⟩, ⟨.count 3, 51298866899280⟩, ⟨.count 4, 11535864596256⟩, ⟨.count 5, 2497492809240⟩, ⟨.count 6, 580551388560⟩, ⟨.count 7, 132517164780⟩, ⟨.count 8, 32125373280⟩, ⟨.count 9, 9637611984⟩, ⟨.count 10, 3569485920⟩, ⟨.path 10, 817253580⟩, ⟨.hall 10 9, 1275603⟩]
  caps := #[0, 0, 2762102200, 18109783120, 20247662864, 8922828200, 3784921140, 2329675920, 1168126960, 0, 399510540, 743600000, 743600000, 0, 0, 0, 0, 0, 0] }

theorem case_46_28_13_checked :
    (Witness.linear .positive case_46_28_13).check 46 28 13 = true := by
  change case_46_28_13.check 46 28 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_28_14 : Certificate := {
  objectiveScale := 99459360000
  eta := 153069693589612800
  rows := #[⟨.count 2, 30442432058438400⟩, ⟨.count 3, 6270712237389600⟩, ⟨.count 4, 1393491608308800⟩, ⟨.count 5, 302433618286800⟩, ⟨.count 6, 74209612276800⟩, ⟨.count 7, 18552403069200⟩, ⟨.count 8, 4497552259200⟩, ⟨.count 9, 1349265677760⟩, ⟨.count 10, 749592043200⟩, ⟨.path 10, 104168544480⟩, ⟨.privateRow 2 26, 1179108283953600⟩, ⟨.privateRow 3 23, 133989577722000⟩, ⟨.privateRow 3 24, 716844240812700⟩, ⟨.privateRow 4 21, 154088014380300⟩, ⟨.privateRow 4 22, 281378113216200⟩, ⟨.privateRow 4 23, 471643313581440⟩, ⟨.privateRow 5 18, 17099622299760⟩, ⟨.privateRow 5 19, 67224485279952⟩, ⟨.privateRow 5 20, 113699727381240⟩, ⟨.privateRow 5 21, 187074972324240⟩, ⟨.privateRow 5 22, 198304575028560⟩, ⟨.privateRow 6 16, 13630336948800⟩, ⟨.privateRow 6 17, 27534122015400⟩, ⟨.privateRow 6 18, 45350318613600⟩, ⟨.privateRow 6 19, 73031681923200⟩, ⟨.privateRow 6 20, 80982711810000⟩, ⟨.privateRow 6 21, 59779965445200⟩, ⟨.privateRow 7 13, 1079769490800⟩, ⟨.privateRow 7 14, 6349780812375⟩, ⟨.privateRow 7 15, 12473441065800⟩, ⟨.privateRow 7 16, 18650563932000⟩, ⟨.privateRow 7 17, 14930267231880⟩, ⟨.privateRow 7 18, 63056084241150⟩, ⟨.privateRow 7 19, 981608628000⟩, ⟨.privateRow 8 11, 965099755620⟩, ⟨.privateRow 8 12, 2946313169800⟩, ⟨.privateRow 8 13, 5739064080750⟩, ⟨.privateRow 8 14, 3774731360400⟩, ⟨.privateRow 8 15, 22753241811300⟩, ⟨.privateRow 8 16, 3560562205200⟩, ⟨.privateRow 9 8, 6246600360⟩, ⟨.privateRow 9 9, 606488107680⟩, ⟨.privateRow 9 10, 1521671847696⟩, ⟨.privateRow 9 11, 2815134562240⟩, ⟨.privateRow 9 12, 4319524148940⟩, ⟨.privateRow 9 13, 3341038821120⟩, ⟨.privateRow 10 6, 17298277920⟩, ⟨.privateRow 10 7, 337316419440⟩, ⟨.privateRow 10 8, 879067032480⟩, ⟨.privateRow 10 9, 1589135131584⟩, ⟨.privateRow 10 10, 841208848480⟩, ⟨.privateRow 11 4, 13385572200⟩, ⟨.privateRow 11 5, 194605626600⟩, ⟨.privateRow 11 6, 554385781950⟩, ⟨.privateRow 11 7, 195916102200⟩, ⟨.privateRow 12 3, 126206823600⟩, ⟨.privateRow 12 4, 90610027200⟩, ⟨.privateRow 13 1, 39264345120⟩, ⟨.hall 5 22, 32623549358400⟩, ⟨.hall 4 23, 167933604078240⟩, ⟨.hall 3 24, 442165606482600⟩, ⟨.hall 2 25, 882269834846400⟩, ⟨.assumptionRow 14, 133244010900⟩]
  caps := #[0, 0, 0, 0, 5181554998620, 1805817653640, 1701048492000, 0, 160812091440, 78395128448, 0, 133244010900, 485607078000, 15450975540, 1159727669100, 99459360000, 0, 0, 0] }

theorem case_46_28_14_checked :
    (Witness.linear .conditional case_46_28_14).check 46 28 14 = true := by
  change case_46_28_14.check 46 28 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_28_15 : Certificate := {
  objectiveScale := 80864987152950000
  eta := 108613203271300785657600
  rows := #[⟨.count 2, 22513661182286437363200⟩, ⟨.count 3, 4563579969382385952000⟩, ⟨.count 4, 1019199526495399529280⟩, ⟨.count 5, 222746165172235504800⟩, ⟨.count 6, 48895499671954135200⟩, ⟨.count 7, 11701487100980476800⟩, ⟨.count 8, 2659428886586472000⟩, ⟨.count 9, 957394399171129920⟩, ⟨.path 9, 130457125218420000⟩, ⟨.privateRow 2 26, 2053610986222073678400⟩, ⟨.privateRow 3 23, 228178998469119297600⟩, ⟨.privateRow 3 24, 727320557620317761100⟩, ⟨.privateRow 4 21, 154971569793610189620⟩, ⟨.privateRow 4 22, 283322256432489794520⟩, ⟨.privateRow 4 23, 495338575843379808540⟩, ⟨.privateRow 5 18, 12042780474759074040⟩, ⟨.privateRow 5 19, 59869822931659396656⟩, ⟨.privateRow 5 20, 111101440921273562760⟩, ⟨.privateRow 5 21, 198117320893028977440⟩, ⟨.privateRow 5 22, 231167056782405383640⟩, ⟨.privateRow 6 16, 8597010931332595200⟩, ⟨.privateRow 6 17, 23124367366223323200⟩, ⟨.privateRow 6 18, 43002965096103252240⟩, ⟨.privateRow 6 19, 77417874480594047400⟩, ⟨.privateRow 6 20, 97860651052842678000⟩, ⟨.privateRow 6 21, 87238765440345519000⟩, ⟨.privateRow 7 13, 81260327090142200⟩, ⟨.privateRow 7 14, 4179102536064456000⟩, ⟨.privateRow 7 15, 9731338762550090400⟩, ⟨.privateRow 7 16, 17291036742966686700⟩, ⟨.privateRow 7 17, 31468642096565353680⟩, ⟨.privateRow 7 18, 41007443635132474500⟩, ⟨.privateRow 7 19, 40572120454292427000⟩, ⟨.privateRow 7 20, 14522381312823984600⟩, ⟨.privateRow 8 11, 126322872112857420⟩, ⟨.privateRow 8 12, 1743403381206687200⟩, ⟨.privateRow 8 13, 4346504086514765175⟩, ⟨.privateRow 8 14, 7598368247389920000⟩, ⟨.privateRow 8 15, 10028263093169821500⟩, ⟨.privateRow 8 16, 25995917366382763800⟩, ⟨.privateRow 8 17, 7828693784888926950⟩, ⟨.privateRow 9 9, 67694553476746560⟩, ⟨.privateRow 9 10, 739321230471039216⟩, ⟨.privateRow 9 11, 1985706901984565760⟩, ⟨.privateRow 9 12, 3503797558077676860⟩, ⟨.privateRow 9 13, 7043687365330455840⟩, ⟨.privateRow 9 14, 7038621786498862560⟩, ⟨.privateRow 10 7, 22161907388220600⟩, ⟨.privateRow 10 8, 328802116887054720⟩, ⟨.privateRow 10 9, 968032114717475808⟩, ⟨.privateRow 10 10, 1926608482282644160⟩, ⟨.privateRow 10 11, 3556986135809406300⟩, ⟨.privateRow 11 6, 144052398023433900⟩, ⟨.privateRow 11 7, 507709151075599200⟩, ⟨.privateRow 11 8, 1110311560149852060⟩, ⟨.privateRow 11 9, 361977820674269800⟩, ⟨.privateRow 12 4, 56257149523944600⟩, ⟨.privateRow 12 5, 287313299354431350⟩, ⟨.privateRow 12 6, 256444928349409800⟩, ⟨.privateRow 13 2, 14925366200230200⟩, ⟨.privateRow 13 3, 128587770340444800⟩, ⟨.privateRow 14 1, 38805952120598520⟩, ⟨.hall 5 22, 63304318415863324800⟩, ⟨.hall 4 23, 216770048545663332720⟩, ⟨.hall 3 24, 506557376601444840672⟩, ⟨.hall 2 25, 977074172931869812800⟩, ⟨.assumptionRow 15, 81695397057386112⟩]
  caps := #[0, 0, 112093636905977126400, 5419298962788590880, 1545278582325133656, 743205352758561264, 453925768723290864, 603788028511942560, 252709646004191376, 226242615852183840, 264447915587063208, 874382932987291000, 81695397057386112, 940984219320678720, 42889444936787592, 888684448778013888, 80864987152950000, 0, 0] }

theorem case_46_28_15_checked :
    (Witness.linear .conditional case_46_28_15).check 46 28 15 = true := by
  change case_46_28_15.check 46 28 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_28_16 : Certificate := {
  objectiveScale := 7958007981000000
  eta := 12737413924288048195200
  rows := #[⟨.count 2, 2471583756126175891200⟩, ⟨.count 3, 459772962507723664800⟩, ⟨.count 4, 92441124737002641600⟩, ⟨.count 5, 17723674291680957600⟩, ⟨.count 6, 3288102470402349600⟩, ⟨.count 7, 654947240039492400⟩, ⟨.count 8, 170116166244024000⟩, ⟨.count 9, 61241819847848640⟩, ⟨.count 10, 34023233248804800⟩, ⟨.path 8, 32673217979001600⟩, ⟨.privateRow 2 26, 223804828310637974400⟩, ⟨.privateRow 3 23, 23515724713798917600⟩, ⟨.privateRow 3 24, 78453322967587768200⟩, ⟨.privateRow 4 21, 15295357152208002870⟩, ⟨.privateRow 4 22, 29840643774751729920⟩, ⟨.privateRow 4 23, 55464674842201584960⟩, ⟨.privateRow 5 18, 1019400874292760960⟩, ⟨.privateRow 5 19, 5636823470805198672⟩, ⟨.privateRow 5 20, 11337938701295906700⟩, ⟨.privateRow 5 21, 21998207503204012080⟩, ⟨.privateRow 5 22, 28097236597694223960⟩, ⟨.privateRow 6 16, 654947240039492400⟩, ⟨.privateRow 6 17, 2056177899851875800⟩, ⟨.privateRow 6 18, 4234434400908391680⟩, ⟨.privateRow 6 19, 8440799634386519400⟩, ⟨.privateRow 6 20, 12020732337595581600⟩, ⟨.privateRow 6 21, 12350433669316142400⟩, ⟨.privateRow 7 14, 283197849966056025⟩, ⟨.privateRow 7 15, 802930945879319400⟩, ⟨.privateRow 7 16, 1630684964996287200⟩, ⟨.privateRow 7 17, 3354933821426787600⟩, ⟨.privateRow 7 18, 5003997407954795250⟩, ⟨.privateRow 7 19, 5863337196544027200⟩, ⟨.privateRow 7 20, 4163593168822487400⟩, ⟨.privateRow 8 12, 101597154840181000⟩, ⟨.privateRow 8 13, 325878780961208475⟩, ⟨.privateRow 8 14, 674996645346823800⟩, ⟨.privateRow 8 15, 1411255362466049100⟩, ⟨.privateRow 8 16, 2228521777796714400⟩, ⟨.privateRow 8 17, 2778209639972716950⟩, ⟨.privateRow 8 18, 1173801547083765600⟩, ⟨.privateRow 9 10, 31301374588900416⟩, ⟨.privateRow 9 11, 132312573745352000⟩, ⟨.privateRow 9 12, 300680323836312420⟩, ⟨.privateRow 9 13, 649357708862903040⟩, ⟨.privateRow 9 14, 1078536493987112160⟩, ⟨.privateRow 9 15, 1158831324454291488⟩, ⟨.privateRow 10 8, 7732553011092000⟩, ⟨.privateRow 10 9, 51715314538183296⟩, ⟨.privateRow 10 10, 139873292245086400⟩, ⟨.privateRow 10 11, 186277202037206280⟩, ⟨.privateRow 10 12, 870994771169402880⟩, ⟨.privateRow 11 6, 708817359350100⟩, ⟨.privateRow 11 7, 18944754877175400⟩, ⟨.privateRow 11 8, 65920014419559300⟩, ⟨.privateRow 11 9, 180984699087392200⟩, ⟨.privateRow 11 10, 183938104751350950⟩, ⟨.privateRow 12 5, 4455423401629200⟩, ⟨.privateRow 12 6, 29770329092704200⟩, ⟨.privateRow 12 7, 103588594087878900⟩, ⟨.privateRow 12 8, 10395987937134800⟩, ⟨.privateRow 13 4, 10024702653665700⟩, ⟨.privateRow 13 5, 35238348721976400⟩, ⟨.privateRow 14 3, 11584100844235920⟩, ⟨.hall 6 21, 1403458371513198000⟩, ⟨.hall 5 22, 10501239243579084000⟩, ⟨.hall 4 23, 28685129715539196900⟩, ⟨.hall 3 24, 60865182655784370864⟩, ⟨.hall 2 25, 110779647458108428800⟩, ⟨.assumptionRow 16, 5411166896800665⟩]
  caps := #[0, 0, 0, 511255845149360850, 0, 1668927866025420, 64344021873241110, 11856224557794045, 0, 0, 37680847102043964, 12647862788233785, 12094934218767400, 5411166896800665, 5411166896800665, 452336516003392020, 82126920894199335, 7958007981000000, 0] }

theorem case_46_28_16_checked :
    (Witness.linear .conditional case_46_28_16).check 46 28 16 = true := by
  change case_46_28_16.check 46 28 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_28_17 : Certificate := {
  objectiveScale := 4176718474500000
  eta := 10504230963536247537600
  rows := #[⟨.count 2, 1965590231249950905600⟩, ⟨.count 3, 355776697178595693000⟩, ⟨.count 4, 67627980728649300960⟩, ⟨.count 5, 11728902104788869000⟩, ⟨.count 6, 2004940530733140000⟩, ⟨.count 7, 280691674302639600⟩, ⟨.count 8, 34023233248804800⟩, ⟨.path 8, 27792624185726400⟩, ⟨.privateRow 2 26, 153257654169241221600⟩, ⟨.privateRow 3 23, 15406854122833773600⟩, ⟨.privateRow 3 24, 57471620313465458100⟩, ⟨.privateRow 4 21, 10825342238938467240⟩, ⟨.privateRow 4 22, 21549323595489870180⟩, ⟨.privateRow 4 23, 41081565631477160790⟩, ⟨.privateRow 5 18, 831159235573927260⟩, ⟨.privateRow 5 19, 3947861567715601536⟩, ⟨.privateRow 5 20, 8049502074138434910⟩, ⟨.privateRow 5 21, 16090316072643692880⟩, ⟨.privateRow 5 22, 21372666057615272400⟩, ⟨.privateRow 6 16, 532741341023377200⟩, ⟨.privateRow 6 17, 1417938497568492900⟩, ⟨.privateRow 6 18, 2936569564013805720⟩, ⟨.privateRow 6 19, 6063274321692137550⟩, ⟨.privateRow 6 20, 9069014334016236600⟩, ⟨.privateRow 6 21, 9914430924475377300⟩, ⟨.privateRow 7 13, 22277117008146000⟩, ⟨.privateRow 7 14, 208847971951368750⟩, ⟨.privateRow 7 15, 550403912365550100⟩, ⟨.privateRow 7 16, 1100489580202412400⟩, ⟨.privateRow 7 17, 2349121988508995700⟩, ⟨.privateRow 7 18, 3710810765631919950⟩, ⟨.privateRow 7 19, 4690446986065140300⟩, ⟨.privateRow 7 20, 3794349954412467450⟩, ⟨.privateRow 8 11, 14672519338547070⟩, ⟨.privateRow 8 12, 77497364622277600⟩, ⟨.privateRow 8 13, 215303272902592875⟩, ⟨.privateRow 8 14, 445643599785684300⟩, ⟨.privateRow 8 15, 958321069841335200⟩, ⟨.privateRow 8 16, 1610574803915297220⟩, ⟨.privateRow 8 17, 2179081766982044925⟩, ⟨.privateRow 8 18, 1845760403747660400⟩, ⟨.privateRow 9 9, 6186042408873600⟩, ⟨.privateRow 9 10, 29940445258948224⟩, ⟨.privateRow 9 11, 86570226821958880⟩, ⟨.privateRow 9 12, 190742751401111910⟩, ⟨.privateRow 9 13, 428449715840306160⟩, ⟨.privateRow 9 14, 471505307439686520⟩, ⟨.privateRow 9 15, 1669520055518851536⟩, ⟨.privateRow 9 16, 85908663953232120⟩, ⟨.privateRow 10 7, 2126452078050300⟩, ⟨.privateRow 10 8, 12062782697303520⟩, ⟨.privateRow 10 9, 37085324241197232⟩, ⟨.privateRow 10 10, 86948262746945600⟩, ⟨.privateRow 10 11, 208604948856734430⟩, ⟨.privateRow 10 12, 394426482591501360⟩, ⟨.privateRow 10 13, 431528008372340880⟩, ⟨.privateRow 11 5, 817866183865500⟩, ⟨.privateRow 11 6, 4784517175613175⟩, ⟨.privateRow 11 7, 17011616624402400⟩, ⟨.privateRow 11 8, 43379622392226120⟩, ⟨.privateRow 11 9, 74662095184877200⟩, ⟨.privateRow 11 10, 304082647161192900⟩, ⟨.privateRow 12 3, 238683396515850⟩, ⟨.privateRow 12 4, 2056349262290400⟩, ⟨.privateRow 12 5, 8353918878054750⟩, ⟨.privateRow 12 6, 17315395492695300⟩, ⟨.privateRow 12 7, 80197621229325600⟩, ⟨.privateRow 12 8, 53465080819550400⟩, ⟨.privateRow 13 2, 1432100379095100⟩, ⟨.privateRow 13 3, 4112698524580800⟩, ⟨.privateRow 13 4, 14480126055294900⟩, ⟨.privateRow 13 5, 33415675512219000⟩, ⟨.privateRow 14 1, 3723460985647260⟩, ⟨.privateRow 14 2, 9356389143421320⟩, ⟨.privateRow 14 3, 2896025211058980⟩, ⟨.privateRow 15 0, 4344037816588470⟩, ⟨.hall 6 21, 1850013307903761000⟩, ⟨.hall 5 22, 8975159871490612800⟩, ⟨.hall 4 23, 22664293301747577480⟩, ⟨.hall 3 24, 46378685345025141108⟩, ⟨.hall 2 25, 82336224462107616000⟩, ⟨.assumptionRow 17, 561835363458600⟩]
  caps := #[0, 3920538900877770600, 44639942472496800, 29334996036327300, 113630302215711336, 5094581846948880, 32925036958992750, 23571850877104530, 0, 755233301452028, 913299721794360, 6670862250452950, 1889557323588000, 21021379596399600, 38947698435462960, 0, 219362608624955400, 41205349381541400, 4176718474500000] }

theorem case_46_28_17_checked :
    (Witness.linear .conditional case_46_28_17).check 46 28 17 = true := by
  change case_46_28_17.check 46 28 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_28_18 : Certificate := {
  objectiveScale := 671404063791499038000000
  eta := 2298246640443889934118255936000
  rows := #[⟨.count 2, 297420153469209285591774297600⟩, ⟨.count 3, 42400807002841819640149641600⟩, ⟨.count 4, 7804206506320161006230441280⟩, ⟨.count 5, 1514314535815779272862487200⟩, ⟨.count 6, 273488243926595587741051200⟩, ⟨.count 7, 41360876396306122837381200⟩, ⟨.count 8, 4297233911304532242844800⟩, ⟨.path 3, 4527408382605065534889312000⟩, ⟨.path 8, 1789748834724291734092800⟩, ⟨.path 9, 448098311906488582859520⟩, ⟨.privateRow 6 16, 29181726203807818445032800⟩, ⟨.privateRow 7 14, 14666229130322834373459150⟩, ⟨.privateRow 9 10, 558640408469589191569824⟩, ⟨.privateRow 9 12, 11871108679978770320858760⟩, ⟨.privateRow 10 8, 195328814150206011038400⟩, ⟨.privateRow 10 9, 859446782260906448568960⟩, ⟨.privateRow 10 16, 29364431727247636992772800⟩, ⟨.privateRow 11 7, 244161017687757513798000⟩, ⟨.privateRow 11 9, 1790514129710221767852000⟩, ⟨.hall 13 5, 32156172125408064402240⟩, ⟨.hall 11 6, 18688046865869222948700⟩, ⟨.hall 12 6, 28038270712495230980100⟩, ⟨.hall 14 6, 15347263968944758010160⟩, ⟨.hall 10 7, 25031414539595200619575⟩, ⟨.hall 11 7, 14149344043766943188100⟩, ⟨.hall 10 8, 4750644235553652983400⟩, ⟨.hall 9 9, 6228751658659820166240⟩, ⟨.hall 8 11, 2766008173704923045360⟩, ⟨.hall 9 11, 24216074643068229148920⟩, ⟨.hall 7 14, 109534035358680856113190⟩, ⟨.hall 8 14, 172214568512892331025600⟩, ⟨.hall 6 16, 344278296552356535283200⟩, ⟨.hall 5 18, 1255264710853887075719520⟩]
  caps := #[0, 1592873858240758602420912000, 411272762307244630257104640, 91138391372864978313050880, 5100545202842036761894080, 8065951231373742313807200, 959990466141061831218600, 4143768814610125985384100, 2219526002582745749692800, 1492429978653525300340224, 1063574651850765414272640, 0, 0, 2665776265080957355427100, 0, 12082484239058925687996000, 103396225823890851852000000, 29541778806825957672000000, 6042636574123491342000000] }

theorem case_46_28_18_checked :
    (Witness.linear .negative case_46_28_18).check 46 28 18 = true := by
  change case_46_28_18.check 46 28 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_29_1_checked :
    (Witness.rising).check 46 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_29_2_checked :
    (Witness.rising).check 46 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_29_3_checked :
    (Witness.rising).check 46 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_29_4_checked :
    (Witness.rising).check 46 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_29_5_checked :
    (Witness.rising).check 46 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_29_6_checked :
    (Witness.rising).check 46 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_29_7_checked :
    (Witness.rising).check 46 29 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_29_8_checked :
    (Witness.rising).check 46 29 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_29_9_checked :
    (Witness.rising).check 46 29 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_29_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_29_10_checked :
    (Witness.linear .positive case_46_29_10).check 46 29 10 = true := by
  change case_46_29_10.check 46 29 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_29_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_29_11_checked :
    (Witness.linear .positive case_46_29_11).check 46 29 11 = true := by
  change case_46_29_11.check 46 29 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_29_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_46_29_12_checked :
    (Witness.linear .positive case_46_29_12).check 46 29 12 = true := by
  change case_46_29_12.check 46 29 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_29_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_46_29_13_checked :
    (Witness.linear .positive case_46_29_13).check 46 29 13 = true := by
  change case_46_29_13.check 46 29 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_29_14 : Certificate := {
  objectiveScale := 26561333700000
  eta := 154856834209000123200
  rows := #[⟨.count 2, 27099945986575021560⟩, ⟨.count 3, 4645705026270003696⟩, ⟨.count 4, 774284171045000616⟩, ⟨.count 5, 136745634603708900⟩, ⟨.count 6, 23550637070638755⟩, ⟨.count 7, 4350997464663465⟩, ⟨.count 8, 1160265990576924⟩, ⟨.count 9, 386755330192308⟩, ⟨.path 7, 657704213364870⟩, ⟨.path 8, 34991693355080⟩]
  caps := #[0, 0, 39779711501360600, 2700658801266174, 0, 0, 236278169081705, 232703117362365, 0, 0, 132806668500000, 53122667400000, 26561333700000, 26561333700000, 0, 0, 0, 0] }

theorem case_46_29_14_checked :
    (Witness.linear .positive case_46_29_14).check 46 29 14 = true := by
  change case_46_29_14.check 46 29 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_29_15 : Certificate := {
  objectiveScale := 400621221000000
  eta := 1306077450952940265600
  rows := #[⟨.count 2, 234760271749752949200⟩, ⟨.count 3, 43377024830918819040⟩, ⟨.count 4, 7967208642413660640⟩, ⟨.count 5, 1519060161932913600⟩, ⟨.count 6, 275002270694751600⟩, ⟨.count 7, 58333814995856400⟩, ⟨.count 8, 13333443427624320⟩, ⟨.count 9, 6666721713812160⟩, ⟨.path 8, 2673211802060800⟩, ⟨.privateRow 2 27, 22046015367362586600⟩, ⟨.privateRow 3 24, 3919291620864459840⟩, ⟨.privateRow 3 25, 7269226688697933960⟩, ⟨.privateRow 4 21, 537956822863828368⟩, ⟨.privateRow 4 22, 1821562659697140360⟩, ⟨.privateRow 4 23, 2860023615225416640⟩, ⟨.privateRow 4 24, 4485810848880340980⟩, ⟨.privateRow 5 18, 40408496918412480⟩, ⟨.privateRow 5 19, 361431555770244960⟩, ⟨.privateRow 5 20, 698767674489140256⟩, ⟨.privateRow 5 21, 1105247221268430240⟩, ⟨.privateRow 5 22, 1780967086404105600⟩, ⟨.privateRow 5 23, 1799300571117089040⟩, ⟨.privateRow 6 16, 46924990634421900⟩, ⟨.privateRow 6 17, 158703124471234200⟩, ⟨.privateRow 6 18, 288097616918311200⟩, ⟨.privateRow 6 19, 433892471540608080⟩, ⟨.privateRow 6 20, 701146662386420250⟩, ⟨.privateRow 6 21, 765350234843594400⟩, ⟨.privateRow 6 22, 524905127794347300⟩, ⟨.privateRow 7 13, 952388816258880⟩, ⟨.privateRow 7 14, 28174835814325200⟩, ⟨.privateRow 7 15, 69494621436390150⟩, ⟨.privateRow 7 16, 124830962702503200⟩, ⟨.privateRow 7 17, 185715819170481600⟩, ⟨.privateRow 7 18, 242621050941949680⟩, ⟨.privateRow 7 19, 439586963004489300⟩, ⟨.privateRow 8 11, 1060614818106480⟩, ⟨.privateRow 8 12, 13916781577582884⟩, ⟨.privateRow 8 13, 33241015211924520⟩, ⟨.privateRow 8 14, 58646317576191345⟩, ⟨.privateRow 8 15, 31905025344672480⟩, ⟨.privateRow 8 16, 251946524767817880⟩, ⟨.privateRow 9 9, 617289047575200⟩, ⟨.privateRow 9 10, 6868743583927680⟩, ⟨.privateRow 9 11, 17481625827329664⟩, ⟨.privateRow 9 12, 31275978410476800⟩, ⟨.privateRow 9 13, 47315205496639080⟩, ⟨.privateRow 9 14, 29206590365272320⟩, ⟨.privateRow 10 7, 256412373608160⟩, ⟨.privateRow 10 8, 3611140928314920⟩, ⟨.privateRow 10 9, 10151598973304880⟩, ⟨.privateRow 10 10, 19250158948632612⟩, ⟨.privateRow 10 11, 9074148999355440⟩, ⟨.privateRow 11 5, 85034715737400⟩, ⟨.privateRow 11 6, 2014668649778400⟩, ⟨.privateRow 11 7, 6547673111779800⟩, ⟨.privateRow 11 8, 3896136066513600⟩, ⟨.privateRow 12 4, 1247175830815200⟩, ⟨.privateRow 12 5, 2182557703926600⟩, ⟨.privateRow 13 2, 698418465256512⟩, ⟨.hall 5 23, 89484865860990600⟩, ⟨.hall 4 24, 1157628606162668640⟩, ⟨.hall 3 25, 3492528837823345320⟩, ⟨.hall 2 26, 7944510042292824000⟩, ⟨.assumptionRow 15, 427663153417500⟩]
  caps := #[0, 0, 0, 0, 109767649184797604, 0, 6265069811800800, 0, 7147022452518403, 0, 1504969980766560, 10464687187023600, 427663153417500, 3985790142638304, 30068625742155000, 4780412719582500, 400621221000000, 0] }

theorem case_46_29_15_checked :
    (Witness.linear .conditional case_46_29_15).check 46 29 15 = true := by
  change case_46_29_15.check 46 29 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_29_16 : Certificate := {
  objectiveScale := 4671010890000000
  eta := 24719694317266908960000
  rows := #[⟨.count 2, 3179670357745219338000⟩, ⟨.count 3, 454523411640068971200⟩, ⟨.count 4, 70058119839258751200⟩, ⟨.count 5, 11391564201505488000⟩, ⟨.count 6, 1752548338693152000⟩, ⟨.count 7, 348518135535570000⟩, ⟨.count 8, 111525803371382400⟩, ⟨.count 9, 55762901685691200⟩, ⟨.path 3, 29260521478173585600⟩, ⟨.path 7, 85306129943580000⟩, ⟨.privateRow 2 27, 299028560289519060000⟩, ⟨.privateRow 3 24, 54711151401119413200⟩, ⟨.privateRow 3 25, 95356885336768855800⟩, ⟨.privateRow 4 21, 7091248715437166280⟩, ⟨.privateRow 4 22, 22249148831065406250⟩, ⟨.privateRow 4 23, 37117513356572048400⟩, ⟨.privateRow 4 24, 61372052135610816600⟩, ⟨.privateRow 5 18, 481950793140616800⟩, ⟨.privateRow 5 19, 3928629192570482400⟩, ⟨.privateRow 5 20, 8166875258310088320⟩, ⟨.privateRow 5 21, 13932759292610558400⟩, ⟨.privateRow 5 22, 24564885880682347200⟩, ⟨.privateRow 5 23, 27602636334417144000⟩, ⟨.privateRow 6 16, 403907624933187375⟩, ⟨.privateRow 6 17, 1598678767290033000⟩, ⟨.privateRow 6 18, 3219090524891241000⟩, ⟨.privateRow 6 19, 5374481571992332800⟩, ⟨.privateRow 6 20, 9634451934846989250⟩, ⟨.privateRow 6 21, 12079196014951065000⟩, ⟨.privateRow 6 22, 10296221489822268000⟩, ⟨.privateRow 7 14, 202472440644474000⟩, ⟨.privateRow 7 15, 649737381248455500⟩, ⟨.privateRow 7 16, 1335749099052654000⟩, ⟨.privateRow 7 17, 2242133338612167000⟩, ⟨.privateRow 7 18, 4018911985775887200⟩, ⟨.privateRow 7 19, 5309922736409791500⟩, ⟨.privateRow 7 20, 4839423253436772000⟩, ⟨.privateRow 8 12, 83644352528536800⟩, ⟨.privateRow 8 13, 282686932156629000⟩, ⟨.privateRow 8 14, 594223421088146850⟩, ⟨.privateRow 8 15, 1021656020169985200⟩, ⟨.privateRow 8 16, 1855278208167684300⟩, ⟨.privateRow 8 17, 2566487550083937480⟩, ⟨.privateRow 8 18, 822502799863945200⟩, ⟨.privateRow 9 10, 30979389825384000⟩, ⟨.privateRow 9 11, 130113437266612800⟩, ⟨.privateRow 9 12, 291206264358609600⟩, ⟨.privateRow 9 13, 516581325338278200⟩, ⟨.privateRow 9 14, 964786711704816000⟩, ⟨.privateRow 9 15, 780680623599676800⟩, ⟨.privateRow 10 8, 11036407625293050⟩, ⟨.privateRow 10 9, 62099595059065200⟩, ⟨.privateRow 10 10, 158227233533148780⟩, ⟨.privateRow 10 11, 298176627069321000⟩, ⟨.privateRow 10 12, 440004146113657125⟩, ⟨.privateRow 11 6, 3063895697016000⟩, ⟨.privateRow 11 7, 30702788130514500⟩, ⟨.privateRow 11 8, 94145158690128000⟩, ⟨.privateRow 11 9, 197161688102979600⟩, ⟨.privateRow 11 10, 1106406779478000⟩, ⟨.privateRow 12 4, 1303979418670500⟩, ⟨.privateRow 12 5, 15447140805789000⟩, ⟨.privateRow 12 6, 60852372871290000⟩, ⟨.privateRow 12 7, 28213372876689000⟩, ⟨.privateRow 13 3, 6259101209618400⟩, ⟨.privateRow 13 4, 23591996867023200⟩, ⟨.hall 5 23, 4198813728119010000⟩, ⟨.hall 4 24, 20071936123052669856⟩, ⟨.hall 3 25, 51831617116849970400⟩, ⟨.hall 2 26, 110382147563661974000⟩, ⟨.assumptionRow 16, 3568083675156000⟩]
  caps := #[0, 44792107796498025600, 8787024941874379200, 1401035732903968980, 520575756670905390, 44653266158155200, 37955302418124000, 164324190273703200, 0, 0, 13169407485780000, 178294776393363000, 0, 0, 1313726280735960000, 313282750752972000, 52484047004844000, 4671010890000000] }

theorem case_46_29_16_checked :
    (Witness.linear .conditional case_46_29_16).check 46 29 16 = true := by
  change case_46_29_16.check 46 29 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_29_17 : Certificate := {
  objectiveScale := 75764865688031520000
  eta := 511412040286636466865888000
  rows := #[⟨.count 2, 64320505066867028671692000⟩, ⟨.count 3, 8865000698343082052760000⟩, ⟨.count 4, 1305828674295615896025600⟩, ⟨.count 5, 188340674177252292696000⟩, ⟨.count 6, 24895606356763234092000⟩, ⟨.count 7, 2066433729217501644000⟩, ⟨.path 3, 632782948700637931996800⟩, ⟨.path 7, 1718141796130683268800⟩, ⟨.path 8, 23874783092095936000⟩, ⟨.privateRow 2 27, 6254750492719841226114000⟩, ⟨.privateRow 3 24, 1090066752537001200561600⟩, ⟨.privateRow 3 25, 1953583487227456970886000⟩, ⟨.privateRow 4 21, 138181439456712802790640⟩, ⟨.privateRow 4 22, 434807177109208310206800⟩, ⟨.privateRow 4 23, 750007201939184560971600⟩, ⟨.privateRow 4 24, 1288942958679724311163200⟩, ⟨.privateRow 5 18, 11195291305774274212800⟩, ⟨.privateRow 5 19, 73099273157684510536800⟩, ⟨.privateRow 5 20, 156041330973521209856640⟩, ⟨.privateRow 5 21, 276557714093608970022000⟩, ⟨.privateRow 5 22, 512633007415785550694400⟩, ⟨.privateRow 5 23, 613297850510523845066400⟩, ⟨.privateRow 6 16, 8839744286097090366000⟩, ⟨.privateRow 6 17, 28812927439815005916000⟩, ⟨.privateRow 6 18, 59593106037566098998000⟩, ⟨.privateRow 6 19, 104128579631331439984800⟩, ⟨.privateRow 6 20, 198037332450266958148500⟩, ⟨.privateRow 6 21, 268740253160325828882000⟩, ⟨.privateRow 6 22, 255540771046051602111000⟩, ⟨.privateRow 7 13, 275524497229000219200⟩, ⟨.privateRow 7 14, 4067266387666193712000⟩, ⟨.privateRow 7 15, 11476087317618625201500⟩, ⟨.privateRow 7 16, 23841303433693080192000⟩, ⟨.privateRow 7 17, 42083086898191343004000⟩, ⟨.privateRow 7 18, 80807398973019635716800⟩, ⟨.privateRow 7 19, 116482901283867503385000⟩, ⟨.privateRow 7 20, 129201308879170459932000⟩, ⟨.privateRow 7 21, 44379124375099678164000⟩, ⟨.privateRow 8 11, 169071850572341043600⟩, ⟨.privateRow 8 12, 1701363770389076353560⟩, ⟨.privateRow 8 13, 4859945992789309422000⟩, ⟨.privateRow 8 14, 10246067240703445651500⟩, ⟨.privateRow 8 15, 18440460993112371813600⟩, ⟨.privateRow 8 16, 36082228949614487039400⟩, ⟨.privateRow 8 17, 54788046273986693587920⟩, ⟨.privateRow 8 18, 54347207078420293237200⟩, ⟨.privateRow 9 9, 66329971555129682400⟩, ⟨.privateRow 9 10, 718033538233152086400⟩, ⟨.privateRow 9 11, 2216441511042179541120⟩, ⟨.privateRow 9 12, 4864197914042843376000⟩, ⟨.privateRow 9 13, 8962199618198868241200⟩, ⟨.privateRow 9 14, 9673971236040452140800⟩, ⟨.privateRow 9 15, 45410518987742628720000⟩, ⟨.privateRow 10 7, 26492740118173098000⟩, ⟨.privateRow 10 8, 315705153074896084500⟩, ⟨.privateRow 10 9, 1108359909307569063600⟩, ⟨.privateRow 10 10, 2596818386383327065960⟩, ⟨.privateRow 10 11, 3199145551158946989600⟩, ⟨.privateRow 10 12, 13767614720911604703150⟩, ⟨.privateRow 10 13, 6710989539649219624800⟩, ⟨.privateRow 11 5, 14057372307602052000⟩, ⟨.privateRow 11 6, 151387086389560560000⟩, ⟨.privateRow 11 7, 606809904611488578000⟩, ⟨.privateRow 11 8, 1583371299010812948000⟩, ⟨.privateRow 11 9, 3217732521210109702800⟩, ⟨.privateRow 11 10, 4570207930227067128000⟩, ⟨.privateRow 12 3, 12026862974281755600⟩, ⟨.privateRow 12 4, 77315547691811286000⟩, ⟨.privateRow 12 5, 374683038814162386000⟩, ⟨.privateRow 12 6, 1112484825121062393000⟩, ⟨.privateRow 12 7, 1918831319987680098000⟩, ⟨.privateRow 13 2, 57728942276552426880⟩, ⟨.privateRow 13 3, 278335971690520629600⟩, ⟨.privateRow 13 4, 766018657131176433600⟩, ⟨.privateRow 14 0, 87946435499435337825⟩, ⟨.privateRow 14 1, 281428593598193081040⟩, ⟨.hall 5 23, 130070523066857186814000⟩, ⟨.hall 4 24, 477077751867656910979008⟩, ⟨.hall 3 25, 1141842397641284158419600⟩, ⟨.hall 2 26, 2331166850305032687948000⟩, ⟨.assumptionRow 17, 24833504132859240000⟩]
  caps := #[0, 0, 28921522474539306939600, 4832341434989990681760, 8045429133183166590320, 0, 0, 626942006307640511800, 146777950466938336000, 466985894339345996160, 62020877101213389660, 15931688615282325600, 0, 6126509259964815816960, 0, 18771628514602443480000, 4626714220127737920000, 808580018435487480000] }

theorem case_46_29_17_checked :
    (Witness.linear .conditional case_46_29_17).check 46 29 17 = true := by
  change case_46_29_17.check 46 29 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_29_18 : Certificate := {
  objectiveScale := 111802996305000000
  eta := 1205944846379881511904000
  rows := #[⟨.count 2, 123261059433683737566000⟩, ⟨.count 3, 14312432066692637077200⟩, ⟨.count 4, 2052407422926048988800⟩, ⟨.count 5, 370772902743050808000⟩, ⟨.count 6, 59802081087588840000⟩, ⟨.count 7, 7611173956602216000⟩, ⟨.path 3, 2724285986502813532800⟩, ⟨.path 8, 754573498767088000⟩, ⟨.privateRow 7 14, 1812184275381480000⟩, ⟨.privateRow 7 19, 219568777265908570500⟩, ⟨.privateRow 8 11, 34596245257282800⟩, ⟨.privateRow 8 12, 1008480549249793620⟩, ⟨.privateRow 8 14, 8633925457020638775⟩, ⟨.privateRow 8 15, 7448077371817882800⟩, ⟨.privateRow 8 16, 18013111697291911200⟩, ⟨.privateRow 8 17, 28503846467475298920⟩, ⟨.privateRow 8 18, 124823252888276342400⟩, ⟨.privateRow 8 19, 79853900094684916200⟩, ⟨.privateRow 8 20, 19218214240420595400⟩, ⟨.privateRow 9 9, 28189533172600800⟩, ⟨.privateRow 9 10, 415154943087393600⟩, ⟨.privateRow 9 12, 3232399803791558400⟩, ⟨.privateRow 10 7, 14636872993465800⟩, ⟨.privateRow 10 8, 174422736505467450⟩, ⟨.privateRow 10 10, 114167609349033240⟩, ⟨.privateRow 10 16, 98184144040168586400⟩, ⟨.privateRow 11 6, 41819637124188000⟩, ⟨.privateRow 11 15, 22697608049153037000⟩, ⟨.privateRow 14 10, 647855878448879100⟩, ⟨.privateRow 14 12, 971783817673318650⟩, ⟨.hall 11 5, 12737954946877875⟩, ⟨.hall 10 6, 6572273798376000⟩, ⟨.hall 11 6, 1181180226897000⟩, ⟨.hall 14 6, 3624368550762960⟩, ⟨.hall 12 7, 3382470649750500⟩, ⟨.hall 9 8, 687283510013100⟩, ⟨.hall 13 8, 1208122850254320⟩, ⟨.hall 9 9, 186926009591475⟩, ⟨.hall 8 10, 3435338612059200⟩, ⟨.hall 7 12, 1679317964169300⟩, ⟨.hall 6 15, 9178009605765000⟩, ⟨.hall 5 17, 37504532908557000⟩, ⟨.hall 4 20, 606372616666776960⟩, ⟨.hall 3 22, 3877644940433722458⟩]
  caps := #[0, 1162576466997894748800, 151981620149828669200, 0, 7985974041467021600, 2594938192318472000, 304538682247800000, 815572710395443000, 840066752491942885, 2063507785134868800, 0, 1289040073370280000, 0, 0, 40928942628061037550, 129021470848670400, 23255023231440000000, 6037361800470000000] }

theorem case_46_29_18_checked :
    (Witness.linear .negative case_46_29_18).check 46 29 18 = true := by
  change case_46_29_18.check 46 29 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_30_1_checked :
    (Witness.rising).check 46 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_30_2_checked :
    (Witness.rising).check 46 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_30_3_checked :
    (Witness.rising).check 46 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_30_4_checked :
    (Witness.rising).check 46 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_30_5_checked :
    (Witness.rising).check 46 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_30_6_checked :
    (Witness.rising).check 46 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_30_7_checked :
    (Witness.rising).check 46 30 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_30_8_checked :
    (Witness.rising).check 46 30 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_30_9_checked :
    (Witness.rising).check 46 30 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_30_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_30_10_checked :
    (Witness.linear .positive case_46_30_10).check 46 30 10 = true := by
  change case_46_30_10.check 46 30 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_46_30_11_checked :
    (Witness.linear .positive case_46_30_11).check 46 30 11 = true := by
  change case_46_30_11.check 46 30 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_30_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_46_30_12_checked :
    (Witness.linear .positive case_46_30_12).check 46 30 12 = true := by
  change case_46_30_12.check 46 30 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_30_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_46_30_13_checked :
    (Witness.linear .positive case_46_30_13).check 46 30 13 = true := by
  change case_46_30_13.check 46 30 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_30_14 : Certificate := {
  objectiveScale := 143
  eta := 38749664
  rows := #[⟨.assumptionRow 14, 411⟩]
  caps := #[0, 0, 11228126, 3300414, 986986, 301444, 94523, 30657, 10398, 3752, 1483, 87723, 39324, 10441, 1734, 143, 0] }

theorem case_46_30_14_checked :
    (Witness.linear .conditional case_46_30_14).check 46 30 14 = true := by
  change case_46_30_14.check 46 30 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_30_15 : Certificate := {
  objectiveScale := 4667288705556750000
  eta := 36346176844415561592869400
  rows := #[⟨.count 2, 5701361073633813583195200⟩, ⟨.count 3, 907563599476402978549440⟩, ⟨.count 4, 143652818260318222936080⟩, ⟨.count 5, 23494619808930550480200⟩, ⟨.count 6, 3661499191002163711200⟩, ⟨.count 7, 640762358425378649460⟩, ⟨.count 8, 189855513607519599840⟩, ⟨.path 7, 123880455126304236360⟩, ⟨.path 8, 13693949226512755200⟩, ⟨.privateRow 2 28, 468326088191348972905320⟩, ⟨.privateRow 3 24, 11635430762517986904480⟩, ⟨.privateRow 3 25, 103264448017347133777260⟩, ⟨.privateRow 3 26, 155623886448678074847420⟩, ⟨.privateRow 4 21, 2125703696998478376780⟩, ⟨.privateRow 4 22, 22152070105563090452760⟩, ⟨.privateRow 4 23, 43381137290061052136655⟩, ⟨.privateRow 4 24, 61197890645166719584140⟩, ⟨.privateRow 4 25, 87769186857647699293890⟩, ⟨.privateRow 5 19, 4187476455741363418920⟩, ⟨.privateRow 5 20, 10665811532308154662440⟩, ⟨.privateRow 5 21, 16893750434040538678620⟩, ⟨.privateRow 5 22, 23522589594417372564105⟩, ⟨.privateRow 5 23, 34570654861712095706580⟩, ⟨.privateRow 5 24, 29312335190189543932440⟩, ⟨.privateRow 6 16, 440736013731741928200⟩, ⟨.privateRow 6 17, 2402858844095169935475⟩, ⟨.privateRow 6 18, 4613198385488837215500⟩, ⟨.privateRow 6 19, 7077203297423163654750⟩, ⟨.privateRow 6 20, 9489385403347274284860⟩, ⟨.privateRow 6 21, 13857757354834577934750⟩, ⟨.privateRow 6 22, 11679504363891161097300⟩, ⟨.privateRow 7 13, 11095452093945950640⟩, ⟨.privateRow 7 14, 375303667077721780398⟩, ⟨.privateRow 7 15, 1189987237075703206140⟩, ⟨.privateRow 7 16, 2151130774713771180330⟩, ⟨.privateRow 7 17, 3225606430168572793200⟩, ⟨.privateRow 7 18, 4281919887255308117820⟩, ⟨.privateRow 7 19, 6145216142231964761964⟩, ⟨.privateRow 7 20, 305124932583513642600⟩, ⟨.privateRow 8 11, 13843631200548304155⟩, ⟨.privateRow 8 12, 237319392009399499800⟩, ⟨.privateRow 8 13, 626523194904814679472⟩, ⟨.privateRow 8 14, 1125948670977928737940⟩, ⟨.privateRow 8 15, 1524777093660391786215⟩, ⟨.privateRow 8 16, 2525756386385751819300⟩, ⟨.privateRow 9 9, 9127668923438442300⟩, ⟨.privateRow 9 10, 146346958405796358210⟩, ⟨.privateRow 9 11, 375396129178504663320⟩, ⟨.privateRow 9 12, 681106655066976564426⟩, ⟨.privateRow 9 13, 769969582963829488240⟩, ⟨.privateRow 10 7, 4358927608335909180⟩, ⟨.privateRow 10 8, 96231709507108148820⟩, ⟨.privateRow 10 9, 264441608239045156920⟩, ⟨.privateRow 10 10, 246873809090297401740⟩, ⟨.privateRow 11 5, 3390277028705707140⟩, ⟨.privateRow 11 6, 72648793472265153000⟩, ⟨.privateRow 11 7, 101708310861171214200⟩, ⟨.privateRow 12 4, 44751656778915334248⟩, ⟨.hall 4 25, 9810940139992977123600⟩, ⟨.hall 3 26, 49773787150771388424720⟩, ⟨.hall 2 27, 139625169150215842853760⟩, ⟨.assumptionRow 15, 5256777640821246540⟩]
  caps := #[0, 1930803452682942310200, 4200690631002719227920, 2203808793953851031220, 183253885753316054040, 230790313001427910020, 37611847584900240795, 204938590098484636992, 0, 45591154738156951560, 349015494633112228680, 5256777640821246540, 5256777640821246540, 1913448516565143661740, 406546360765583301900, 60085264236973253460, 4667288705556750000] }

theorem case_46_30_15_checked :
    (Witness.linear .conditional case_46_30_15).check 46 30 15 = true := by
  change case_46_30_15.check 46 30 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_30_16 : Certificate := {
  objectiveScale := 6609784681500000
  eta := 55739722550823520209000
  rows := #[⟨.count 2, 8375704340970306740400⟩, ⟨.count 3, 1248772015424345532120⟩, ⟨.count 4, 188229727644155477280⟩, ⟨.count 5, 27223307717129924400⟩, ⟨.count 6, 3889043959589989200⟩, ⟨.count 7, 742453846830816120⟩, ⟨.count 8, 219986324986908480⟩, ⟨.path 6, 289462054533724800⟩, ⟨.path 7, 156155988909080160⟩, ⟨.privateRow 2 28, 754993067355069903360⟩, ⟨.privateRow 3 24, 8847575008067225430⟩, ⟨.privateRow 3 25, 153357966806498574120⟩, ⟨.privateRow 3 26, 248574726417126809700⟩, ⟨.privateRow 4 22, 28312240025815121376⟩, ⟨.privateRow 4 23, 63780320937275822880⟩, ⟨.privateRow 4 24, 97874272983014728200⟩, ⟨.privateRow 4 25, 151867166621989078260⟩, ⟨.privateRow 5 19, 3351985508027562120⟩, ⟨.privateRow 5 20, 13698077057666961960⟩, ⟨.privateRow 5 21, 24475049985686332032⟩, ⟨.privateRow 5 22, 37788543807349395060⟩, ⟨.privateRow 5 23, 61490106161072829240⟩, ⟨.privateRow 5 24, 60733903168930331340⟩, ⟨.privateRow 6 16, 183321937489090400⟩, ⟨.privateRow 6 17, 2231780908628346075⟩, ⟨.privateRow 6 18, 5698880434290958200⟩, ⟨.privateRow 6 19, 10095800986006335600⟩, ⟨.privateRow 6 20, 15214411369183866840⟩, ⟨.privateRow 6 21, 22435658903240733150⟩, ⟨.privateRow 6 22, 32683682569483545600⟩, ⟨.privateRow 6 23, 11696594333009285700⟩, ⟨.privateRow 7 14, 159097252892317740⟩, ⟨.privateRow 7 15, 1111716606630269640⟩, ⟨.privateRow 7 16, 2532297941869390695⟩, ⟨.privateRow 7 17, 4464824493866948640⟩, ⟨.privateRow 7 18, 6764579493347435760⟩, ⟨.privateRow 7 19, 11080239790322751048⟩, ⟨.privateRow 7 20, 11985326384554603080⟩, ⟨.privateRow 8 12, 87494561074338600⟩, ⟨.privateRow 8 13, 541716325280262132⟩, ⟨.privateRow 8 14, 1246589174925814720⟩, ⟨.privateRow 8 15, 2203300536197005245⟩, ⟨.privateRow 8 16, 3370504764977990640⟩, ⟨.privateRow 8 17, 5595902141854484460⟩, ⟨.privateRow 8 18, 1352915898669487152⟩, ⟨.privateRow 9 10, 43538960153658970⟩, ⟨.privateRow 9 11, 279982595437883520⟩, ⟨.privateRow 9 12, 692956923708761712⟩, ⟨.privateRow 9 13, 1255755271800269240⟩, ⟨.privateRow 9 14, 1952378634258812760⟩, ⟨.privateRow 9 15, 986010135209179080⟩, ⟨.privateRow 10 8, 21756889284419520⟩, ⟨.privateRow 10 9, 159097252892317740⟩, ⟨.privateRow 10 10, 437115684714246720⟩, ⟨.privateRow 10 11, 844983187583643108⟩, ⟨.privateRow 10 12, 326051160248453640⟩, ⟨.privateRow 11 6, 12626766102564900⟩, ⟨.privateRow 11 7, 104251761154510200⟩, ⟨.privateRow 11 8, 319176587592612750⟩, ⟨.privateRow 11 9, 149990676127437600⟩, ⟨.privateRow 12 4, 8642319910199976⟩, ⟨.privateRow 12 5, 74077027801714080⟩, ⟨.privateRow 12 6, 89747168298230520⟩, ⟨.privateRow 13 3, 51853919461199856⟩, ⟨.hall 4 25, 27582296390322846480⟩, ⟨.hall 3 26, 96433886331314732200⟩, ⟨.hall 2 27, 237620585930948340120⟩, ⟨.assumptionRow 16, 5603775452975700⟩]
  caps := #[0, 122411225888136221400, 28582534260654585120, 8568895668424558740, 530161504431463268, 0, 369247150057494865, 2081382977560458, 135484719683363323, 99878884395171336, 201560093446150152, 8509852271143080, 839072243960188656, 0, 2325512612750527200, 516427764993340200, 80323425406524300] }

theorem case_46_30_16_checked :
    (Witness.linear .conditional case_46_30_16).check 46 30 16 = true := by
  change case_46_30_16.check 46 30 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_30_17 : Certificate := {
  objectiveScale := 71385674560200000
  eta := 788849787719273819338800
  rows := #[⟨.count 2, 110700858500937124580160⟩, ⟨.count 3, 15045933270861750216960⟩, ⟨.count 4, 1913409628118274686400⟩, ⟨.count 5, 217786461737039395200⟩, ⟨.count 6, 19091670347078128800⟩, ⟨.count 7, 1484907693661632240⟩, ⟨.path 6, 10176876443606745600⟩, ⟨.path 7, 494039362290954480⟩, ⟨.privateRow 2 28, 10192406409293443695360⟩, ⟨.privateRow 3 24, 176951500161344508600⟩, ⟨.privateRow 3 25, 1944781249392300599280⟩, ⟨.privateRow 3 26, 3255907602968738958240⟩, ⟨.privateRow 4 21, 25278785737334929800⟩, ⟨.privateRow 4 22, 344413733061289443552⟩, ⟨.privateRow 4 23, 788114758410911311380⟩, ⟨.privateRow 4 24, 1263939286866746490000⟩, ⟨.privateRow 4 25, 2055748637039268291120⟩, ⟨.privateRow 5 19, 49557531599346719520⟩, ⟨.privateRow 5 20, 157635915162047562240⟩, ⟨.privateRow 5 21, 294478408620153982224⟩, ⟨.privateRow 5 22, 479324668019466168900⟩, ⟨.privateRow 5 23, 831996137754951689520⟩, ⟨.privateRow 5 24, 896813537081451509520⟩, ⟨.privateRow 6 16, 3535494508718172000⟩, ⟨.privateRow 6 17, 26383627771309358550⟩, ⟨.privateRow 6 18, 63840929414568134400⟩, ⟨.privateRow 6 19, 117673042231836491400⟩, ⟨.privateRow 6 20, 189290375996770928880⟩, ⟨.privateRow 6 21, 335606816240072477100⟩, ⟨.privateRow 6 22, 410117363011307952000⟩, ⟨.privateRow 6 23, 320492577215302291800⟩, ⟨.privateRow 7 14, 2481917145120156744⟩, ⟨.privateRow 7 15, 11973541402858875840⟩, ⟨.privateRow 7 16, 27444276123924810150⟩, ⟨.privateRow 7 17, 50517165823141651920⟩, ⟨.privateRow 7 18, 81775987986651318360⟩, ⟨.privateRow 7 19, 146030065188095376288⟩, ⟨.privateRow 7 20, 191871286988135194440⟩, ⟨.privateRow 7 21, 89235881400046661280⟩, ⟨.privateRow 8 12, 1274920747083219600⟩, ⟨.privateRow 8 13, 5593152312792148104⟩, ⟨.privateRow 8 14, 12997525367976509360⟩, ⟨.privateRow 8 15, 24109126304034001230⟩, ⟨.privateRow 8 16, 39408978790511890560⟩, ⟨.privateRow 8 17, 71303067586381711080⟩, ⟨.privateRow 8 18, 82989841101311224080⟩, ⟨.privateRow 9 10, 632460684337361880⟩, ⟨.privateRow 9 11, 2864821914034058160⟩, ⟨.privateRow 9 12, 6946068211461635256⟩, ⟨.privateRow 9 13, 13217511692963417840⟩, ⟨.privateRow 9 14, 21902388481509075540⟩, ⟨.privateRow 9 15, 40139647655646979440⟩, ⟨.privateRow 9 16, 6132118809010073880⟩, ⟨.privateRow 10 8, 326353339266292800⟩, ⟨.privateRow 10 9, 1644004946553949980⟩, ⟨.privateRow 10 10, 4319731472470202880⟩, ⟨.privateRow 10 11, 8548825722080539896⟩, ⟨.privateRow 10 12, 14566237375918868640⟩, ⟨.privateRow 10 13, 4772917586769532200⟩, ⟨.privateRow 11 6, 202028257641038400⟩, ⟨.privateRow 11 7, 1115040575826500400⟩, ⟨.privateRow 11 8, 3181945057846354800⟩, ⟨.privateRow 11 9, 6717439566564526800⟩, ⟨.privateRow 11 10, 883873627179543000⟩, ⟨.privateRow 12 4, 155561758383599568⟩, ⟨.privateRow 12 5, 888924333620568960⟩, ⟨.privateRow 12 6, 2871909385543376640⟩, ⟨.privateRow 12 7, 129634798652999640⟩, ⟨.privateRow 13 2, 145839148484624595⟩, ⟨.privateRow 13 3, 933370550301597408⟩, ⟨.privateRow 13 4, 166673312553856680⟩, ⟨.hall 5 24, 20223028589867943840⟩, ⟨.hall 4 25, 462377411072483639040⟩, ⟨.hall 3 26, 1390894966347584137440⟩, ⟨.hall 2 27, 3235684574378871014400⟩, ⟨.assumptionRow 17, 34296850755367200⟩]
  caps := #[0, 0, 25380422550353510640, 11707619112721864332, 3978711994164499956, 1770710614406697600, 1775016711431108730, 457922869059025188, 702949674706483568, 168692280727370400, 3765310251345835164, 3992612109211440, 0, 0, 74855335613490432000, 21898269528086952000, 5050837881315626400] }

theorem case_46_30_17_checked :
    (Witness.linear .conditional case_46_30_17).check 46 30 17 = true := by
  change case_46_30_17.check 46 30 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_30_18 : Certificate := {
  objectiveScale := 120806526178800000
  eta := 1929656109259461866283000
  rows := #[⟨.count 2, 274982631250729366364400⟩, ⟨.count 3, 37690669534366380331800⟩, ⟨.count 4, 4900195389083386392000⟩, ⟨.count 5, 563911374140548434000⟩, ⟨.count 6, 47729175867695322000⟩, ⟨.count 7, 3712269234154080600⟩, ⟨.path 6, 21056732162509680000⟩, ⟨.path 7, 2309097019403374200⟩, ⟨.privateRow 3 24, 126393928686674649000⟩, ⟨.privateRow 4 22, 756030145744293900480⟩, ⟨.privateRow 4 23, 1190047451634536695200⟩, ⟨.privateRow 5 19, 89725799924826179400⟩, ⟨.privateRow 5 20, 353254826329424019000⟩, ⟨.privateRow 5 21, 627302790681865257960⟩, ⟨.privateRow 6 17, 69384079733594125500⟩, ⟨.privateRow 6 18, 131570902788726258000⟩, ⟨.privateRow 6 19, 266340586323435624000⟩, ⟨.privateRow 6 22, 2488104260510413545000⟩, ⟨.privateRow 7 15, 34883545819352630400⟩, ⟨.privateRow 7 17, 215690418564013621800⟩, ⟨.privateRow 7 18, 44812392898002830100⟩, ⟨.privateRow 7 19, 247767455170969493760⟩, ⟨.privateRow 8 12, 862446387732766200⟩, ⟨.privateRow 8 13, 13570406422629916860⟩, ⟨.privateRow 8 14, 17415584061463588000⟩, ⟨.privateRow 8 17, 484038660697757064900⟩, ⟨.privateRow 8 20, 227410863455216641200⟩, ⟨.privateRow 9 10, 549965812467271200⟩, ⟨.privateRow 9 11, 5924631707033785200⟩, ⟨.privateRow 9 12, 12786705139864055400⟩, ⟨.privateRow 9 13, 15032398874105412800⟩, ⟨.privateRow 9 14, 8661961546359521400⟩, ⟨.privateRow 9 18, 486410388264022171950⟩, ⟨.privateRow 10 8, 40794167408286600⟩, ⟨.privateRow 10 9, 3358719783282263400⟩, ⟨.hall 10 6, 1664674272035775⟩, ⟨.hall 11 6, 430013706279300⟩, ⟨.hall 12 6, 5656334136443100⟩, ⟨.hall 10 7, 7183183502620125⟩, ⟨.hall 9 8, 6689970812236140⟩, ⟨.hall 11 8, 3653278837962600⟩, ⟨.hall 13 8, 1039851326093580⟩, ⟨.hall 6 14, 2609903525966100⟩, ⟨.hall 5 19, 42949304409738870⟩, ⟨.hall 4 20, 178126085018791800⟩, ⟨.hall 3 23, 6051784517117533194⟩, ⟨.hall 2 25, 70290868602959804800⟩]
  caps := #[0, 864982186025364225000, 63278005686279930000, 38651829975746341200, 11862365431822563840, 9998056983964024440, 1896139232912622600, 3097007224203423960, 0, 3102886825346471800, 9988045632214650, 4311766129110640200, 7795886747370321600, 0, 120454616768041155600, 109933938822708000000, 32980181646812400000] }

theorem case_46_30_18_checked :
    (Witness.linear .negative case_46_30_18).check 46 30 18 = true := by
  change case_46_30_18.check 46 30 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_30_19 : Certificate := {
  objectiveScale := 442897792837500
  eta := 7962075084409303057200
  rows := #[⟨.count 2, 1000289577391493669280⟩, ⟨.count 3, 115386441398608259880⟩, ⟨.count 4, 11623928397122321280⟩, ⟨.count 5, 894958255213222200⟩, ⟨.count 6, 28715238135183600⟩, ⟨.path 5, 346472115129940800⟩, ⟨.path 6, 36885470963577600⟩, ⟨.privateRow 9 11, 406074074638960⟩, ⟨.hall 9 7, 24694907237⟩, ⟨.hall 12 7, 13895634341435⟩, ⟨.hall 9 9, 14126572429992⟩, ⟨.hall 11 9, 16298638776420⟩, ⟨.hall 10 10, 14713329346800⟩, ⟨.hall 13 10, 42228291375270⟩, ⟨.hall 8 13, 15849640463020⟩, ⟨.hall 12 13, 70045340455805⟩, ⟨.hall 7 14, 14498741189660⟩, ⟨.hall 6 19, 234024056324760⟩]
  caps := #[0, 3899870362245475800, 0, 69579939915906420, 0, 0, 8170232828394000, 0, 0, 21521925955864880, 3032043778249200, 16022270553689400, 0, 0, 20921074460706420, 725466584667825000, 282125894037487500] }

theorem case_46_30_19_checked :
    (Witness.linear .negative case_46_30_19).check 46 30 19 = true := by
  change case_46_30_19.check 46 30 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_31_1_checked :
    (Witness.rising).check 46 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_31_2_checked :
    (Witness.rising).check 46 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_31_3_checked :
    (Witness.rising).check 46 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_31_4_checked :
    (Witness.rising).check 46 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_31_5_checked :
    (Witness.rising).check 46 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_31_6_checked :
    (Witness.rising).check 46 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_31_7_checked :
    (Witness.rising).check 46 31 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_31_8_checked :
    (Witness.rising).check 46 31 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_31_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_31_9_checked :
    (Witness.linear .positive case_46_31_9).check 46 31 9 = true := by
  change case_46_31_9.check 46 31 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_31_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_46_31_10_checked :
    (Witness.linear .positive case_46_31_10).check 46 31 10 = true := by
  change case_46_31_10.check 46 31 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_46_31_11_checked :
    (Witness.linear .positive case_46_31_11).check 46 31 11 = true := by
  change case_46_31_11.check 46 31 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_46_31_12_checked :
    (Witness.linear .positive case_46_31_12).check 46 31 12 = true := by
  change case_46_31_12.check 46 31 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_31_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_46_31_13_checked :
    (Witness.linear .positive case_46_31_13).check 46 31 13 = true := by
  change case_46_31_13.check 46 31 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_31_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_46_31_14_checked :
    (Witness.linear .positive case_46_31_14).check 46 31 14 = true := by
  change case_46_31_14.check 46 31 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_31_15 : Certificate := {
  objectiveScale := 297435600000
  eta := 51886887817660295400
  rows := #[⟨.count 2, 5023763116098526800⟩, ⟨.count 3, 441265814933743800⟩, ⟨.count 4, 38865517534443600⟩, ⟨.count 5, 6247782752211000⟩, ⟨.count 6, 1852790747207400⟩, ⟨.count 7, 569721185833800⟩, ⟨.count 8, 167565054657000⟩, ⟨.count 9, 43088156911800⟩, ⟨.path 4, 17485639892721000⟩, ⟨.privateRow 2 28, 300891781074584700⟩, ⟨.privateRow 3 25, 64657370125898550⟩, ⟨.privateRow 4 25, 16009644079228800⟩, ⟨.privateRow 4 26, 530549862074607375⟩, ⟨.privateRow 5 23, 75777705288885600⟩, ⟨.privateRow 5 25, 118815592684288500⟩, ⟨.privateRow 6 20, 10472815916062500⟩, ⟨.privateRow 6 21, 2183133283531200⟩, ⟨.privateRow 6 22, 38897833652127450⟩, ⟨.privateRow 6 23, 7497339302653200⟩, ⟨.privateRow 8 18, 3521658898707950⟩, ⟨.privateRow 8 19, 255536708351925⟩, ⟨.privateRow 9 17, 5979678664759800⟩, ⟨.hall 9 10, 84957457500⟩, ⟨.hall 7 14, 52783364725⟩, ⟨.hall 6 16, 98538972168⟩, ⟨.hall 5 18, 254164804110⟩, ⟨.hall 4 20, 625152268620⟩, ⟨.hall 3 23, 5613560857740⟩, ⟨.hall 2 27, 25815006284967900⟩, ⟨.hall 1 29, 457670433784664100⟩, ⟨.assumptionRow 15, 1719965779200⟩]
  caps := #[0, 4304272299019200, 963944477773200, 143046156569400, 17173060639200, 12977685312900, 11294245848600, 6389042460768, 10945656153900, 14873497014600, 19915422508800, 7410086496000, 3142495958400, 1719965779200, 7875383932800, 2741568220800] }

theorem case_46_31_15_checked :
    (Witness.linear .conditional case_46_31_15).check 46 31 15 = true := by
  change case_46_31_15.check 46 31 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_31_16 : Certificate := {
  objectiveScale := 1908819145773540000
  eta := 49435750013625514285306560
  rows := #[⟨.count 2, 5721179557472740550629440⟩, ⟨.count 3, 618955589757120687751680⟩, ⟨.count 4, 61562787153262003889280⟩, ⟨.count 5, 5294097175341941366400⟩, ⟨.count 6, 680669636829678175680⟩, ⟨.count 7, 176469905844731378880⟩, ⟨.path 5, 2382074263489451731200⟩, ⟨.path 6, 95736658181040676800⟩, ⟨.privateRow 2 29, 421788284955457242863040⟩, ⟨.privateRow 3 25, 37228847636601009108720⟩, ⟨.privateRow 3 26, 92898800433976447310400⟩, ⟨.privateRow 3 27, 134772588092276278784640⟩, ⟨.privateRow 4 22, 8977906459850708900520⟩, ⟨.privateRow 4 23, 23709992349567123119520⟩, ⟨.privateRow 4 24, 37592816817405767577660⟩, ⟨.privateRow 4 25, 51926269794812208235440⟩, ⟨.privateRow 4 26, 73937739300623791833240⟩, ⟨.privateRow 5 18, 33613315398996453120⟩, ⟨.privateRow 5 19, 1295163058967582084280⟩, ⟨.privateRow 5 20, 5358922855040005954560⟩, ⟨.privateRow 5 21, 9882314727304957217280⟩, ⟨.privateRow 5 22, 14883976058675629441536⟩, ⟨.privateRow 5 23, 20268829185594861231360⟩, ⟨.privateRow 5 24, 29873834060858097710400⟩, ⟨.privateRow 5 25, 23974697208334220187840⟩, ⟨.privateRow 6 16, 102100445524451726352⟩, ⟨.privateRow 6 17, 924366173472402460800⟩, ⟨.privateRow 6 18, 2533603648199357653920⟩, ⟨.privateRow 6 19, 4289299140021940249920⟩, ⟨.privateRow 6 20, 6390731590234200649440⟩, ⟨.privateRow 6 21, 5717624949369296675712⟩, ⟨.privateRow 6 22, 18368626449445342990920⟩, ⟨.privateRow 6 23, 3857127942034842995520⟩, ⟨.privateRow 7 14, 75629959647742019520⟩, ⟨.privateRow 7 15, 539493712153893072576⟩, ⟨.privateRow 7 16, 1252095998612617878720⟩, ⟨.privateRow 7 17, 2095580131906185124200⟩, ⟨.privateRow 7 18, 3079219785658067937600⟩, ⟨.privateRow 7 19, 4121832800801940063840⟩, ⟨.privateRow 7 20, 4492419603075875959488⟩, ⟨.privateRow 8 12, 47793932832948081780⟩, ⟨.privateRow 8 13, 320854374263147961600⟩, ⟨.privateRow 8 14, 705879623378925515520⟩, ⟨.privateRow 8 15, 1188720893537426649400⟩, ⟨.privateRow 8 16, 1745397662495546294235⟩, ⟨.privateRow 8 17, 1607136642514517914800⟩, ⟨.privateRow 9 10, 32966905487477290560⟩, ⟨.privateRow 9 11, 212184053456165110320⟩, ⟨.privateRow 9 12, 476697927476676971520⟩, ⟨.privateRow 9 13, 811761566885764342848⟩, ⟨.privateRow 9 14, 420166442487455664000⟩, ⟨.privateRow 10 8, 24309629886774220560⟩, ⟨.privateRow 10 9, 162895297702828965120⟩, ⟨.privateRow 10 10, 390754791513333767520⟩, ⟨.privateRow 10 11, 72192234209208291360⟩, ⟨.privateRow 11 6, 25209986549247339840⟩, ⟨.privateRow 11 7, 151259919295484039040⟩, ⟨.privateRow 11 8, 29088446018362315200⟩, ⟨.privateRow 12 4, 25997798628911319210⟩, ⟨.privateRow 12 5, 27730985204172073824⟩, ⟨.hall 4 26, 2773098520417207382400⟩, ⟨.hall 3 27, 31821305521787454713040⟩, ⟨.hall 2 28, 103675635028839180827520⟩, ⟨.assumptionRow 16, 1743192376817189760⟩]
  caps := #[0, 7599242524363524951840, 4626986659761299359680, 0, 1675721611530770583780, 119648361831716134560, 0, 22675136253361480944, 138041265096335785345, 21502113515929015200, 66560967288036343440, 1743192376817189760, 337567727290882194414, 3127653617286026949120, 830957722459560178560, 172369305508190313600] }

theorem case_46_31_16_checked :
    (Witness.linear .conditional case_46_31_16).check 46 31 16 = true := by
  change case_46_31_16.check 46 31 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_31_17 : Certificate := {
  objectiveScale := 31677373728000
  eta := 881804083776033337920
  rows := #[⟨.count 2, 99610994325546063360⟩, ⟨.count 3, 10276913915603375040⟩, ⟨.count 4, 923282778311974080⟩, ⟨.count 5, 62754989180083200⟩, ⟨.count 7, 1830353851085760⟩, ⟨.path 5, 50452072655212800⟩, ⟨.privateRow 2 28, 476741808427444560⟩, ⟨.privateRow 2 29, 8300916193795505280⟩, ⟨.privateRow 3 25, 655789636931869440⟩, ⟨.privateRow 3 26, 1751648635489072320⟩, ⟨.privateRow 3 27, 2623158547727477760⟩, ⟨.privateRow 4 22, 142375381702313760⟩, ⟨.privateRow 4 23, 406848439228126896⟩, ⟨.privateRow 4 24, 690844181669181540⟩, ⟨.privateRow 4 25, 1017480631862494800⟩, ⟨.privateRow 4 26, 1537006961559069000⟩, ⟨.privateRow 5 18, 1481715022307520⟩, ⟨.privateRow 5 19, 17747895377492280⟩, ⟨.privateRow 5 20, 82590048260216640⟩, ⟨.privateRow 5 21, 166169981766428640⟩, ⟨.privateRow 5 22, 269062016109606720⟩, ⟨.privateRow 5 23, 395552541175711920⟩, ⟨.privateRow 5 24, 633563911597256640⟩, ⟨.privateRow 5 25, 584013618057149280⟩, ⟨.privateRow 6 14, 261479121583680⟩, ⟨.privateRow 6 16, 1568874729502080⟩, ⟨.privateRow 6 17, 12158779153641120⟩, ⟨.privateRow 6 18, 38045212190425440⟩, ⟨.privateRow 6 19, 70151112904878720⟩, ⟨.privateRow 6 20, 113351199206525280⟩, ⟨.privateRow 6 21, 165516283962469440⟩, ⟨.privateRow 6 22, 268865906768418960⟩, ⟨.privateRow 6 23, 282789669992749920⟩, ⟨.privateRow 7 14, 1164770632509120⟩, ⟨.privateRow 7 15, 6824605073334048⟩, ⟨.privateRow 7 16, 18071112625005440⟩, ⟨.privateRow 7 17, 33109793770533480⟩, ⟨.privateRow 7 18, 53080261681487040⟩, ⟨.privateRow 7 19, 42926155793320800⟩, ⟨.privateRow 7 20, 196632299430927360⟩, ⟨.privateRow 7 21, 31377494590041600⟩, ⟨.privateRow 8 12, 686382694157160⟩, ⟨.privateRow 8 13, 3951900360298800⟩, ⟨.privateRow 8 14, 9746634257031672⟩, ⟨.privateRow 8 15, 18023901116941720⟩, ⟨.privateRow 8 16, 28856672433523935⟩, ⟨.privateRow 8 17, 42196193245566360⟩, ⟨.privateRow 8 18, 43623433450877280⟩, ⟨.privateRow 9 10, 442503128833920⟩, ⟨.privateRow 9 11, 2549421435440880⟩, ⟨.privateRow 9 12, 6251728088773440⟩, ⟨.privateRow 9 13, 11714264646948864⟩, ⟨.privateRow 9 14, 18942709696951040⟩, ⟨.privateRow 9 15, 14610145918488120⟩, ⟨.privateRow 10 8, 336187442036160⟩, ⟨.privateRow 10 9, 1930922744002560⟩, ⟨.privateRow 10 10, 4347090396328680⟩, ⟨.privateRow 10 11, 10696873155696000⟩, ⟨.privateRow 10 12, 2235646489540464⟩, ⟨.privateRow 11 6, 313774945900416⟩, ⟨.privateRow 11 7, 1849030931198880⟩, ⟨.privateRow 11 8, 4585941517006080⟩, ⟨.privateRow 12 4, 404475516199755⟩, ⟨.privateRow 12 5, 1869575719323312⟩, ⟨.privateRow 13 2, 507577118368320⟩, ⟨.hall 4 26, 133267192300482240⟩, ⟨.hall 3 27, 736838826082753680⟩, ⟨.hall 2 28, 2123580144638272320⟩, ⟨.assumptionRow 17, 18832198681296⟩]
  caps := #[0, 40913472286486800, 103813577446859280, 5241995369953056, 0, 1336007693619456, 214148325631968, 53607813321608, 884662774264633, 100148017041072, 1700353934466840, 3088576892231424, 0, 26135902914016896, 43606819254974976, 11979495777465216] }

theorem case_46_31_17_checked :
    (Witness.linear .conditional case_46_31_17).check 46 31 17 = true := by
  change case_46_31_17.check 46 31 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_31_18 : Certificate := {
  objectiveScale := 84928283440000
  eta := 1754826919394815506240
  rows := #[⟨.count 2, 235630469742060032640⟩, ⟨.count 3, 30458883740514989760⟩, ⟨.count 4, 3656883133648704960⟩, ⟨.count 5, 371676433685356800⟩, ⟨.count 6, 24778428912357120⟩, ⟨.path 6, 25082848949558400⟩, ⟨.privateRow 2 28, 17568938533399212960⟩, ⟨.privateRow 2 29, 36761896595095832160⟩, ⟨.privateRow 3 25, 3571707284262477360⟩, ⟨.privateRow 3 26, 8540298498459087360⟩, ⟨.privateRow 3 27, 11265925678818370560⟩, ⟨.privateRow 4 22, 573517385867265840⟩, ⟨.privateRow 4 23, 1806863684979841488⟩, ⟨.privateRow 4 24, 2976895936048654620⟩, ⟨.privateRow 4 25, 4423465778124753360⟩, ⟨.privateRow 4 26, 6501756503148706800⟩, ⟨.privateRow 5 19, 77948807620123440⟩, ⟨.privateRow 5 20, 332148939944215680⟩, ⟨.privateRow 5 21, 700334761620093600⟩, ⟨.privateRow 5 22, 1130722306033896576⟩, ⟨.privateRow 5 23, 1691127773268373440⟩, ⟨.privateRow 5 24, 2810286812476503360⟩, ⟨.privateRow 5 25, 2761762389189804000⟩, ⟨.privateRow 6 15, 187715370548160⟩, ⟨.privateRow 6 16, 8259476304119040⟩, ⟨.privateRow 6 17, 52539446490090560⟩, ⟨.privateRow 6 18, 152155040039942940⟩, ⟨.privateRow 6 19, 285836876381833920⟩, ⟨.privateRow 6 20, 467176628451733200⟩, ⟨.privateRow 6 22, 2567406587408502840⟩, ⟨.privateRow 6 23, 646304020797314880⟩, ⟨.privateRow 6 24, 431041419621212400⟩, ⟨.privateRow 7 12, 105890721847680⟩, ⟨.privateRow 7 13, 573574743341600⟩, ⟨.privateRow 7 14, 6570037969185600⟩, ⟨.privateRow 7 15, 29321140879622592⟩, ⟨.privateRow 7 16, 72040987763704960⟩, ⟨.privateRow 7 17, 131721439808398440⟩, ⟨.privateRow 7 18, 213959767116226560⟩, ⟨.privateRow 7 19, 320169421733281120⟩, ⟨.privateRow 7 20, 158444287100683584⟩, ⟨.privateRow 7 21, 1062719284463316480⟩, ⟨.privateRow 8 10, 86036211501240⟩, ⟨.privateRow 8 11, 509599098891960⟩, ⟨.privateRow 8 12, 4466713313772710⟩, ⟨.privateRow 8 16, 418114478843151090⟩, ⟨.privateRow 8 18, 270411812748397320⟩, ⟨.privateRow 8 20, 17314787564624550⟩, ⟨.privateRow 9 8, 91771958934656⟩, ⟨.privateRow 9 9, 442471944863520⟩, ⟨.privateRow 9 10, 3388503099125760⟩, ⟨.privateRow 9 11, 1720724230024800⟩, ⟨.privateRow 9 12, 1439151174202560⟩, ⟨.privateRow 9 13, 3647935367652576⟩, ⟨.privateRow 9 15, 25810863450372000⟩, ⟨.privateRow 9 18, 511812214978576512⟩, ⟨.privateRow 10 12, 7640015581310112⟩, ⟨.privateRow 11 17, 62978506818907680⟩, ⟨.privateRow 11 18, 75023576429081280⟩, ⟨.privateRow 13 13, 3785593306054560⟩, ⟨.hall 9 6, 18970792644960⟩, ⟨.hall 10 6, 3386653172760⟩, ⟨.hall 11 7, 3882284156751⟩, ⟨.hall 7 9, 319665496605⟩, ⟨.hall 12 9, 1229381445600⟩, ⟨.hall 3 26, 139706419628204000⟩, ⟨.hall 4 26, 817688154107784960⟩, ⟨.hall 2 28, 9448840891912181760⟩]
  caps := #[0, 1073435380503245760, 241305795640990080, 73251130348075680, 0, 0, 304420037201280, 4167819847806256, 86289110706106, 388808089581952, 0, 7849067543665920, 36489827650099824, 7694502479664000, 323406903339520000, 107009637134400000] }

theorem case_46_31_18_checked :
    (Witness.linear .negative case_46_31_18).check 46 31 18 = true := by
  change case_46_31_18.check 46 31 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_31_19 : Certificate := {
  objectiveScale := 148079909734803200000
  eta := 2822739470158935078937785600
  rows := #[⟨.count 2, 346358666462892448927161600⟩, ⟨.count 3, 39385266420529576132185600⟩, ⟨.count 4, 3861300629463683934528000⟩, ⟨.count 5, 292522774959369995040000⟩, ⟨.count 6, 17551366497562199702400⟩, ⟨.path 3, 220891640764267208736000⟩, ⟨.path 5, 122716629345866686416000⟩, ⟨.path 6, 11634404414956491168000⟩, ⟨.hall 12 7, 3831567664388032800⟩, ⟨.hall 9 8, 1838730267593375520⟩, ⟨.hall 10 8, 3680074224266485760⟩, ⟨.hall 11 8, 5491913652289513680⟩, ⟨.hall 10 10, 1924077268697020800⟩, ⟨.hall 8 11, 4210181069959972800⟩, ⟨.hall 9 11, 3425189275740817200⟩, ⟨.hall 12 12, 5108756885850710400⟩, ⟨.hall 7 13, 4353896408491655025⟩, ⟨.hall 6 14, 1116960028224632592⟩, ⟨.hall 6 15, 4459010389355252640⟩, ⟨.hall 5 16, 5382092818406646720⟩]
  caps := #[0, 0, 0, 0, 29485594096085048064000, 2636801874556814096000, 183512882358930678400, 0, 0, 348377262515408190400, 19758455331028153376000, 0, 101102654162768922343680, 0, 916318481438962201600000, 377307610004278553600000] }

theorem case_46_31_19_checked :
    (Witness.linear .negative case_46_31_19).check 46 31 19 = true := by
  change case_46_31_19.check 46 31 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_31_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16796, 16796, 11934, 7072, 3640] }

theorem case_46_31_20_checked :
    (Witness.linear .negative case_46_31_20).check 46 31 20 = true := by
  change case_46_31_20.check 46 31 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_32_1_checked :
    (Witness.rising).check 46 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_32_2_checked :
    (Witness.rising).check 46 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_32_3_checked :
    (Witness.rising).check 46 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_32_4_checked :
    (Witness.rising).check 46 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_32_5_checked :
    (Witness.rising).check 46 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_32_6_checked :
    (Witness.rising).check 46 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_32_7_checked :
    (Witness.rising).check 46 32 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_32_8_checked :
    (Witness.rising).check 46 32 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_32_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_46_32_9_checked :
    (Witness.linear .positive case_46_32_9).check 46 32 9 = true := by
  change case_46_32_9.check 46 32 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_32_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_46_32_10_checked :
    (Witness.linear .positive case_46_32_10).check 46 32 10 = true := by
  change case_46_32_10.check 46 32 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_46_32_11_checked :
    (Witness.linear .positive case_46_32_11).check 46 32 11 = true := by
  change case_46_32_11.check 46 32 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_46_32_12_checked :
    (Witness.linear .positive case_46_32_12).check 46 32 12 = true := by
  change case_46_32_12.check 46 32 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_32_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_46_32_13_checked :
    (Witness.linear .positive case_46_32_13).check 46 32 13 = true := by
  change case_46_32_13.check 46 32 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_32_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_46_32_14_checked :
    (Witness.linear .positive case_46_32_14).check 46 32 14 = true := by
  change case_46_32_14.check 46 32 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_32_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_46_32_15_checked :
    (Witness.linear .positive case_46_32_15).check 46 32 15 = true := by
  change case_46_32_15.check 46 32 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_32_16 : Certificate := {
  objectiveScale := 25711963200000
  eta := 1262363971401468936000
  rows := #[⟨.count 2, 134717713014217132800⟩, ⟨.count 3, 13889691214057058400⟩, ⟨.count 4, 1251524872063065600⟩, ⟨.count 5, 89394633718790400⟩, ⟨.count 6, 7449552809899200⟩, ⟨.path 5, 63671847333494400⟩, ⟨.privateRow 2 29, 921882160225026000⟩, ⟨.privateRow 2 30, 9833409709066944000⟩, ⟨.privateRow 3 26, 1428917348348790300⟩, ⟨.privateRow 3 27, 2403722373327475200⟩, ⟨.privateRow 3 28, 3103669939424254200⟩, ⟨.privateRow 4 22, 87000134601322800⟩, ⟨.privateRow 4 23, 266321512953896400⟩, ⟨.privateRow 4 24, 730801130651111520⟩, ⟨.privateRow 4 25, 952611565565860200⟩, ⟨.privateRow 4 26, 1201240390596246000⟩, ⟨.privateRow 4 27, 1544851013952846600⟩, ⟨.privateRow 5 19, 24831842699664000⟩, ⟨.privateRow 5 20, 60620735990554740⟩, ⟨.privateRow 5 21, 165380072379762240⟩, ⟨.privateRow 5 22, 294629813631513360⟩, ⟨.privateRow 5 23, 393783361531271712⟩, ⟨.privateRow 5 24, 330201428298782040⟩, ⟨.privateRow 5 25, 934173922361359680⟩, ⟨.privateRow 6 16, 3499032380407200⟩, ⟨.privateRow 6 17, 14029991125310160⟩, ⟨.privateRow 6 18, 40834585772780800⟩, ⟨.privateRow 6 19, 82721075993255700⟩, ⟨.privateRow 6 20, 130899285088228800⟩, ⟨.privateRow 6 21, 178789267437580800⟩, ⟨.privateRow 6 22, 216781986768066720⟩, ⟨.privateRow 6 23, 156130210974137400⟩, ⟨.privateRow 7 11, 124159213498320⟩, ⟨.privateRow 7 13, 143260630959600⟩, ⟨.privateRow 7 14, 2017587219347700⟩, ⟨.privateRow 7 15, 10666405159628400⟩, ⟨.privateRow 7 16, 24956001913162320⟩, ⟨.privateRow 7 17, 45214646915638200⟩, ⟨.privateRow 7 18, 68675564966258250⟩, ⟨.privateRow 7 19, 93385465581236400⟩, ⟨.privateRow 7 20, 49198088348709300⟩, ⟨.privateRow 8 12, 1862388202474800⟩, ⟨.privateRow 8 13, 8225547894263700⟩, ⟨.privateRow 8 14, 17354071886697000⟩, ⟨.privateRow 8 15, 29611972419349320⟩, ⟨.privateRow 8 16, 44179986803152200⟩, ⟨.privateRow 8 17, 232798525309350⟩, ⟨.privateRow 9 10, 1862388202474800⟩, ⟨.privateRow 9 11, 7354045722592800⟩, ⟨.privateRow 9 12, 14899105619798400⟩, ⟨.privateRow 9 13, 10384225128950400⟩, ⟨.privateRow 10 8, 2085874786771776⟩, ⟨.privateRow 10 9, 8141296999389840⟩, ⟨.privateRow 10 10, 687651028606080⟩, ⟨.privateRow 11 6, 3142780091676225⟩, ⟨.privateRow 12 4, 1205074719248400⟩, ⟨.hall 3 28, 368752864090010400⟩, ⟨.hall 2 29, 1901125877086275840⟩, ⟨.assumptionRow 16, 25220864702880⟩]
  caps := #[0, 1122956051574218400, 0, 21500992005280920, 49710102562755360, 567078899587200, 2993088756687680, 1841395248544140, 11021771113647630, 324433551657600, 6250114299909744, 49506046799246730, 0, 54618426989501760, 13642214866711200] }

theorem case_46_32_16_checked :
    (Witness.linear .conditional case_46_32_16).check 46 32 16 = true := by
  change case_46_32_16.check 46 32 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_32_17 : Certificate := {
  objectiveScale := 559235199600000
  eta := 15778750677979500010800
  rows := #[⟨.count 2, 1803693175885604203200⟩, ⟨.count 3, 188924384035448661600⟩, ⟨.count 4, 17174944003222605600⟩, ⟨.count 5, 1134194415307153200⟩, ⟨.path 5, 882775019726800200⟩, ⟨.privateRow 2 29, 169319023427996442000⟩, ⟨.privateRow 2 30, 260216604426184005600⟩, ⟨.privateRow 3 25, 9386809018113486960⟩, ⟨.privateRow 3 26, 32749863741994048650⟩, ⟨.privateRow 3 27, 70698118554145882800⟩, ⟨.privateRow 3 28, 79906697021282531400⟩, ⟨.privateRow 4 22, 2870206275471163200⟩, ⟨.privateRow 4 23, 6292078542061111800⟩, ⟨.privateRow 4 24, 16462021799315252160⟩, ⟨.privateRow 4 25, 24243405627190399650⟩, ⟨.privateRow 4 26, 32459563980933289200⟩, ⟨.privateRow 4 27, 43423443328902436800⟩, ⟨.privateRow 5 19, 525690109951886880⟩, ⟨.privateRow 5 20, 1332678437985905010⟩, ⟨.privateRow 5 21, 3587757844338954000⟩, ⟨.privateRow 5 22, 6578327608781488560⟩, ⟨.privateRow 5 23, 9630930863693883744⟩, ⟨.privateRow 5 24, 12889309391097719580⟩, ⟨.privateRow 5 25, 18784419887801327760⟩, ⟨.privateRow 5 26, 10434588620825809440⟩, ⟨.privateRow 6 16, 60555834583498800⟩, ⟨.privateRow 6 17, 253843511997315240⟩, ⟨.privateRow 6 18, 824141268265515200⟩, ⟨.privateRow 6 19, 1728296251896614400⟩, ⟨.privateRow 6 20, 2903640577963210800⟩, ⟨.privateRow 6 21, 4296736515131860800⟩, ⟨.privateRow 6 22, 5735783185981889040⟩, ⟨.privateRow 6 23, 8483954257357078500⟩, ⟨.privateRow 6 24, 582099779284623600⟩, ⟨.privateRow 7 13, 1038639574457100⟩, ⟨.privateRow 7 14, 32630593297527225⟩, ⟨.privateRow 7 15, 180440020617047100⟩, ⟨.privateRow 7 16, 483382857952334340⟩, ⟨.privateRow 7 17, 922658155309390500⟩, ⟨.privateRow 7 18, 1498756905941595300⟩, ⟨.privateRow 7 19, 2200877258274594900⟩, ⟨.privateRow 7 20, 2959257254224020750⟩, ⟨.privateRow 7 21, 1328627743645522320⟩, ⟨.privateRow 8 12, 25965989361427500⟩, ⟨.privateRow 8 13, 133897951807094475⟩, ⟨.privateRow 8 14, 324055547230615200⟩, ⟨.privateRow 8 15, 588700910802284280⟩, ⟨.privateRow 8 16, 937660726940437500⟩, ⟨.privateRow 8 17, 1363733761262172300⟩, ⟨.privateRow 8 18, 152383263281063100⟩, ⟨.privateRow 9 10, 24432759513419400⟩, ⟨.privateRow 9 11, 117712485105138000⟩, ⟨.privateRow 9 12, 267045775032636600⟩, ⟨.privateRow 9 13, 476263455778328400⟩, ⟨.privateRow 9 14, 392467273868189520⟩, ⟨.privateRow 10 8, 28084814093319984⟩, ⟨.privateRow 10 9, 124992853931808720⟩, ⟨.privateRow 10 10, 291649992507553680⟩, ⟨.privateRow 11 6, 40506943403826900⟩, ⟨.privateRow 11 7, 108018515743538400⟩, ⟨.privateRow 12 4, 52420750287305400⟩, ⟨.hall 3 28, 12568326784401187800⟩, ⟨.hall 2 29, 51924500517918908880⟩, ⟨.assumptionRow 17, 386617934656800⟩]
  caps := #[0, 11491931740347412200, 736792194809008800, 834003982820172780, 0, 60019603399497600, 159968979153384700, 22069984137547500, 78723109523990085, 2147090342997600, 386617934656800, 775818603877086000, 0, 3211292931251882400, 998596097224941600] }

theorem case_46_32_17_checked :
    (Witness.linear .conditional case_46_32_17).check 46 32 17 = true := by
  change case_46_32_17.check 46 32 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_32_18 : Certificate := {
  objectiveScale := 1838405368800000
  eta := 73773189660332933971200
  rows := #[⟨.count 2, 8326931341637888179200⟩, ⟨.count 3, 848377422649750593600⟩, ⟨.count 4, 73236553674119035200⟩, ⟨.count 5, 4212722113997997600⟩, ⟨.path 5, 4181565882916422000⟩, ⟨.privateRow 2 29, 791343646337162318400⟩, ⟨.privateRow 2 30, 1240484634798794985600⟩, ⟨.privateRow 3 25, 44438817376891697760⟩, ⟨.privateRow 3 26, 149119560983954761200⟩, ⟨.privateRow 3 27, 328538315633972043600⟩, ⟨.privateRow 3 28, 379334022662370976200⟩, ⟨.privateRow 4 22, 14281590902949255600⟩, ⟨.privateRow 4 23, 28030804835448214800⟩, ⟨.privateRow 4 24, 73949475878026388640⟩, ⟨.privateRow 4 25, 111475108247331628800⟩, ⟨.privateRow 4 26, 153656338645183374000⟩, ⟨.privateRow 4 27, 213147536190937147800⟩, ⟨.privateRow 5 18, 200914439282981424⟩, ⟨.privateRow 5 19, 2743670299885875360⟩, ⟨.privateRow 5 20, 6148954008700923420⟩, ⟨.privateRow 5 21, 15675029756040900960⟩, ⟨.privateRow 5 22, 29110989992883598800⟩, ⟨.privateRow 5 23, 43669725544797704352⟩, ⟨.privateRow 5 24, 60533576222678919360⟩, ⟨.privateRow 5 25, 92485453179617578080⟩, ⟨.privateRow 5 26, 65329598321692024320⟩, ⟨.privateRow 6 14, 2769705531885600⟩, ⟨.privateRow 6 15, 72012343829025600⟩, ⟨.privateRow 6 16, 464806946532801600⟩, ⟨.privateRow 6 17, 1278219102965204400⟩, ⟨.privateRow 6 18, 3688632278353422400⟩, ⟨.privateRow 6 19, 7412770642900322700⟩, ⟨.privateRow 6 20, 12627878864304132000⟩, ⟨.privateRow 6 21, 19167285515825647200⟩, ⟨.privateRow 6 22, 26565353638527543840⟩, ⟨.privateRow 6 23, 41470108502540117400⟩, ⟨.privateRow 6 24, 15122592204095376000⟩, ⟨.privateRow 7 11, 1800308595725640⟩, ⟨.privateRow 7 12, 19289020668489000⟩, ⟨.privateRow 7 13, 91400282552224800⟩, ⟨.privateRow 7 14, 258794360635560750⟩, ⟨.privateRow 7 15, 896062687417989000⟩, ⟨.privateRow 7 16, 2122563834360529560⟩, ⟨.privateRow 7 17, 3909670167050848200⟩, ⟨.privateRow 7 18, 6396721479187664625⟩, ⟨.privateRow 7 19, 9636794725977104400⟩, ⟨.privateRow 7 20, 13443804438581216700⟩, ⟨.privateRow 7 21, 13594130206324307640⟩, ⟨.privateRow 8 9, 6751157233971150⟩, ⟨.privateRow 8 10, 23404011744433320⟩, ⟨.privateRow 8 11, 65582670272862600⟩, ⟨.privateRow 8 12, 228500706380562000⟩, ⟨.privateRow 8 13, 663863794673829750⟩, ⟨.privateRow 8 14, 1421425468534289400⟩, ⟨.privateRow 8 15, 2487126324994971660⟩, ⟨.privateRow 8 16, 3300565758830340000⟩, ⟨.privateRow 8 17, 7149475510775447850⟩, ⟨.privateRow 8 18, 3803794875826030800⟩, ⟨.privateRow 9 6, 2000342884139600⟩, ⟨.privateRow 9 7, 8472040450473600⟩, ⟨.privateRow 9 8, 24754243191227550⟩, ⟨.privateRow 9 9, 76813166750960640⟩, ⟨.privateRow 9 10, 228896378599402800⟩, ⟨.privateRow 9 11, 598256394887289600⟩, ⟨.privateRow 9 12, 1191204187505131800⟩, ⟨.privateRow 9 13, 2019618915568581600⟩, ⟨.privateRow 9 14, 2905698073501182960⟩, ⟨.privateRow 10 4, 3411111023480160⟩, ⟨.privateRow 10 5, 10801851574353840⟩, ⟨.privateRow 10 6, 38124182027131200⟩, ⟨.privateRow 10 7, 105318052849949940⟩, ⟨.privateRow 10 8, 289489622192682912⟩, ⟨.privateRow 10 9, 587929349975544720⟩, ⟨.privateRow 10 10, 1520568337005194400⟩, ⟨.privateRow 11 1, 7715608267395600⟩, ⟨.privateRow 11 2, 8101388680765380⟩, ⟨.privateRow 11 3, 25583332676101200⟩, ⟨.privateRow 11 4, 72012343829025600⟩, ⟨.privateRow 11 5, 95310455067828000⟩, ⟨.privateRow 11 6, 688618037865057300⟩, ⟨.privateRow 12 0, 56581127294234400⟩, ⟨.privateRow 12 1, 59410183658946120⟩, ⟨.privateRow 12 2, 156342588576174000⟩, ⟨.privateRow 13 0, 178230550976838360⟩, ⟨.hall 3 28, 66805727210973550800⟩, ⟨.hall 2 29, 253087382387110471200⟩, ⟨.assumptionRow 18, 391912027879680⟩]
  caps := #[0, 21894793152204495600, 5111963966609549280, 129160593340899120, 92958411991579200, 1280710743359796, 505882039961766500, 0, 57523303676885550, 0, 756261736150687668, 0, 8104182556552786440, 0, 9246486180788398080] }

theorem case_46_32_18_checked :
    (Witness.linear .conditional case_46_32_18).check 46 32 18 = true := by
  change case_46_32_18.check 46 32 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_32_19 : Certificate := {
  objectiveScale := 923181916800000
  eta := 56812770429376995633600
  rows := #[⟨.count 2, 6252327728267489668800⟩, ⟨.count 3, 638065372497081328800⟩, ⟨.count 4, 53793220840282123200⟩, ⟨.count 5, 2916499925075536800⟩, ⟨.path 5, 2958570269848393200⟩, ⟨.privateRow 4 22, 2129507881801185600⟩, ⟨.privateRow 5 19, 633708625695425280⟩, ⟨.privateRow 6 14, 2769705531885600⟩, ⟨.privateRow 6 15, 6001028652418800⟩, ⟨.privateRow 6 16, 104745227387673600⟩, ⟨.privateRow 6 17, 327656164422066480⟩, ⟨.privateRow 7 13, 2077279148914200⟩, ⟨.privateRow 7 14, 6751157233971150⟩, ⟨.privateRow 7 15, 31914561469681800⟩, ⟨.hall 8 8, 11700631415200⟩, ⟨.hall 9 8, 21017075592240⟩, ⟨.hall 11 8, 35034753742560⟩, ⟨.hall 9 9, 27044614252656⟩, ⟨.hall 10 9, 32247898331220⟩, ⟨.hall 7 10, 37564718049495⟩, ⟨.hall 8 10, 29373970080000⟩, ⟨.hall 6 12, 13525103302326⟩, ⟨.hall 6 13, 10009311438555⟩, ⟨.hall 5 15, 25252576124160⟩, ⟨.hall 4 21, 1011231844673760⟩, ⟨.hall 3 23, 4917080060947890⟩]
  caps := #[0, 7982576829887259600, 0, 794060076710300400, 102041383524537600, 107910201987965520, 0, 1796088056551008, 16393795239890640, 154769350210800, 194120231191286400, 615366351162162600, 0, 21469518657100800000, 9228126440332800000] }

theorem case_46_32_19_checked :
    (Witness.linear .negative case_46_32_19).check 46 32 19 = true := by
  change case_46_32_19.check 46 32 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_32_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58786, 58786, 41990, 25194, 13260] }

theorem case_46_32_20_checked :
    (Witness.linear .negative case_46_32_20).check 46 32 20 = true := by
  change case_46_32_20.check 46 32 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_33_1_checked :
    (Witness.rising).check 46 33 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_33_2_checked :
    (Witness.rising).check 46 33 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_33_3_checked :
    (Witness.rising).check 46 33 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_33_4_checked :
    (Witness.rising).check 46 33 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_33_5_checked :
    (Witness.rising).check 46 33 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_33_6_checked :
    (Witness.rising).check 46 33 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_33_7_checked :
    (Witness.rising).check 46 33 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_33_8_checked :
    (Witness.rising).check 46 33 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_33_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_46_33_9_checked :
    (Witness.linear .positive case_46_33_9).check 46 33 9 = true := by
  change case_46_33_9.check 46 33 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_33_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_46_33_10_checked :
    (Witness.linear .positive case_46_33_10).check 46 33 10 = true := by
  change case_46_33_10.check 46 33 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_33_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_46_33_11_checked :
    (Witness.linear .positive case_46_33_11).check 46 33 11 = true := by
  change case_46_33_11.check 46 33 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_33_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_46_33_12_checked :
    (Witness.linear .positive case_46_33_12).check 46 33 12 = true := by
  change case_46_33_12.check 46 33 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_33_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_46_33_13_checked :
    (Witness.linear .positive case_46_33_13).check 46 33 13 = true := by
  change case_46_33_13.check 46 33 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_33_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_46_33_14_checked :
    (Witness.linear .positive case_46_33_14).check 46 33 14 = true := by
  change case_46_33_14.check 46 33 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_33_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_46_33_15_checked :
    (Witness.linear .positive case_46_33_15).check 46 33 15 = true := by
  change case_46_33_15.check 46 33 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_33_16 : Certificate := {
  objectiveScale := 909
  eta := 1036754095
  rows := #[⟨.assumptionRow 16, 1673⟩]
  caps := #[0, 0, 300607056, 88171248, 26208220, 7912242, 2432976, 764764, 246906, 82395, 18497336, 12066824, 5269061, 1778495] }

theorem case_46_33_16_checked :
    (Witness.linear .conditional case_46_33_16).check 46 33 16 = true := by
  change case_46_33_16.check 46 33 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_33_17 : Certificate := {
  objectiveScale := 33346074361600000
  eta := 2565604429013866006166400
  rows := #[⟨.count 2, 225967869764093889432000⟩, ⟨.count 3, 17382143828007222264000⟩, ⟨.count 4, 969186201319190574720⟩, ⟨.count 5, 23410294717854844800⟩, ⟨.path 4, 734872677844355930880⟩, ⟨.path 5, 6779050829989838400⟩, ⟨.privateRow 2 30, 18927223279385642020800⟩, ⟨.privateRow 2 31, 26266350673433135865600⟩, ⟨.privateRow 3 26, 2170134320345144112960⟩, ⟨.privateRow 3 27, 3915371791561222792800⟩, ⟨.privateRow 3 28, 7924384761993864964800⟩, ⟨.privateRow 3 29, 8322359772197397326400⟩, ⟨.privateRow 3 30, 10464401738881115625600⟩, ⟨.privateRow 4 22, 118514617009140151800⟩, ⟨.privateRow 4 23, 561345424055990814240⟩, ⟨.privateRow 4 24, 909489949788660720480⟩, ⟨.privateRow 4 25, 2014221757524230846592⟩, ⟨.privateRow 4 26, 2712667900431430141200⟩, ⟨.privateRow 4 27, 3311386187840567796960⟩, ⟨.privateRow 4 28, 3961021866261039740160⟩, ⟨.privateRow 5 19, 39329295125996139264⟩, ⟨.privateRow 5 20, 120693074989829422080⟩, ⟨.privateRow 5 21, 232347175074709334640⟩, ⟨.privateRow 5 22, 521046273863112117120⟩, ⟨.privateRow 5 23, 834186835112894303040⟩, ⟨.privateRow 5 24, 1123694146457032550400⟩, ⟨.privateRow 5 25, 1369502240994508420800⟩, ⟨.privateRow 5 26, 1440513468305334783360⟩, ⟨.privateRow 6 16, 8535003282551245500⟩, ⟨.privateRow 6 17, 28996842320979296400⟩, ⟨.privateRow 6 18, 59110994162583483120⟩, ⟨.privateRow 6 19, 150216057772901920800⟩, ⟨.privateRow 6 20, 265560530705665895700⟩, ⟨.privateRow 6 21, 397975010203532361600⟩, ⟨.privateRow 6 22, 498444191700992737200⟩, ⟨.privateRow 6 23, 740350570452159466800⟩, ⟨.privateRow 7 13, 1791604187590932000⟩, ⟨.privateRow 7 14, 7717679577314784000⟩, ⟨.privateRow 7 15, 17557721038391133600⟩, ⟨.privateRow 7 16, 46288537283031170400⟩, ⟨.privateRow 7 17, 96818290297413965280⟩, ⟨.privateRow 7 18, 158298183330256569600⟩, ⟨.privateRow 7 19, 230758619361712041600⟩, ⟨.privateRow 7 20, 235775111086966651200⟩, ⟨.privateRow 8 10, 548678782449722925⟩, ⟨.privateRow 8 11, 2341029471785484480⟩, ⟨.privateRow 8 12, 6270614656568262000⟩, ⟨.privateRow 8 13, 17782820026062814800⟩, ⟨.privateRow 8 14, 39992586809668693200⟩, ⟨.privateRow 8 15, 76083457833028245600⟩, ⟨.privateRow 8 16, 119392503061059708480⟩, ⟨.privateRow 8 17, 22434865771277559600⟩, ⟨.privateRow 9 7, 260114385753942720⟩, ⟨.privateRow 9 8, 1101660927899051520⟩, ⟨.privateRow 9 9, 2926286839731855600⟩, ⟨.privateRow 9 10, 8739843361332475392⟩, ⟨.privateRow 9 11, 5016491725254609600⟩, ⟨.privateRow 9 12, 76713734998508952960⟩, ⟨.privateRow 9 13, 5072230522201883040⟩, ⟨.privateRow 10 5, 554454348580772640⟩, ⟨.privateRow 10 6, 1755772103839113360⟩, ⟨.privateRow 10 7, 1239368543886432960⟩, ⟨.privateRow 10 8, 24361337940767697870⟩, ⟨.privateRow 10 9, 5618470732285162752⟩, ⟨.privateRow 11 4, 7392724647743635200⟩, ⟨.privateRow 11 5, 1950857893154570400⟩, ⟨.hall 3 29, 280923536614258137600⟩, ⟨.assumptionRow 17, 25870807919480832⟩]
  caps := #[0, 0, 0, 0, 14135111574789997176, 24043214204458665216, 3213633213748013056, 8070871381347645760, 41152873833621591195, 0, 0, 111992035223991871872, 759323827018241329152, 259584463278617917440] }

theorem case_46_33_17_checked :
    (Witness.linear .conditional case_46_33_17).check 46 33 17 = true := by
  change case_46_33_17.check 46 33 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_33_18 : Certificate := {
  objectiveScale := 32825041949700000
  eta := 3190202797233592192852800
  rows := #[⟨.count 2, 277341761522426346345600⟩, ⟨.count 3, 20489860451802452911200⟩, ⟨.count 4, 1011324731811329295360⟩, ⟨.path 4, 945801590098389504480⟩, ⟨.path 5, 4003569874233129200⟩, ⟨.privateRow 2 30, 24093582694932233082600⟩, ⟨.privateRow 2 31, 34474585258880990823600⟩, ⟨.privateRow 3 26, 2577473448435818412480⟩, ⟨.privateRow 3 27, 4793257843480779472800⟩, ⟨.privateRow 3 28, 10078131876036510686400⟩, ⟨.privateRow 3 29, 11035027672628827467600⟩, ⟨.privateRow 3 30, 14450004414595902952800⟩, ⟨.privateRow 4 22, 156702660267640867380⟩, ⟨.privateRow 4 23, 647127432557844638400⟩, ⟨.privateRow 4 24, 1061364236770744026120⟩, ⟨.privateRow 4 25, 2445088231806349265136⟩, ⟨.privateRow 4 26, 3446141696810219747340⟩, ⟨.privateRow 4 27, 4406987980636174533600⟩, ⟨.privateRow 4 28, 5607058213610208515160⟩, ⟨.privateRow 5 16, 180079190137344960⟩, ⟨.privateRow 5 17, 195085789315457040⟩, ⟨.privateRow 5 18, 4894879804642376640⟩, ⟨.privateRow 5 19, 52204957220816303904⟩, ⟨.privateRow 5 20, 137860624449589641600⟩, ⟨.privateRow 5 21, 260146900052161962840⟩, ⟨.privateRow 5 22, 598969111995400386240⟩, ⟨.privateRow 5 23, 1003131128660080099680⟩, ⟨.privateRow 5 24, 1413045389169718432128⟩, ⟨.privateRow 5 25, 1808445266954286760800⟩, ⟨.privateRow 5 26, 2568889673705938302720⟩, ⟨.privateRow 6 15, 1913341395209290200⟩, ⟨.privateRow 6 16, 14753362816981438650⟩, ⟨.privateRow 6 17, 34849416000443007600⟩, ⟨.privateRow 6 18, 65695139551980158220⟩, ⟨.privateRow 6 19, 165172634953753627200⟩, ⟨.privateRow 6 20, 300858865709931403875⟩, ⟨.privateRow 6 21, 470714140219724200800⟩, ⟨.privateRow 6 22, 668656542878729004600⟩, ⟨.privateRow 6 23, 866180904560629257600⟩, ⟨.privateRow 6 24, 566602289343080540550⟩, ⟨.privateRow 7 12, 836081954209101600⟩, ⟨.privateRow 7 13, 4747751097115969800⟩, ⟨.privateRow 7 14, 11480048371255741200⟩, ⟨.privateRow 7 15, 21006559099503677700⟩, ⟨.privateRow 7 16, 50848984305989906400⟩, ⟨.privateRow 7 17, 105095501644084071120⟩, ⟨.privateRow 7 18, 176691986322856804800⟩, ⟨.privateRow 7 19, 267441715102636374300⟩, ⟨.privateRow 7 20, 376057718975336626800⟩, ⟨.privateRow 7 21, 185401173345868279800⟩, ⟨.privateRow 8 9, 430336299960567000⟩, ⟨.privateRow 8 10, 2011822202315650725⟩, ⟨.privateRow 8 11, 5072230522201883040⟩, ⟨.privateRow 8 12, 9614942473404668400⟩, ⟨.privateRow 8 13, 21271854334973873400⟩, ⟨.privateRow 8 14, 43528516741011352050⟩, ⟨.privateRow 8 15, 81803018474322327000⟩, ⟨.privateRow 8 16, 131243964761973723660⟩, ⟨.privateRow 8 17, 149078057335228421400⟩, ⟨.privateRow 9 6, 246424154924787840⟩, ⟨.privateRow 9 7, 1170514735892742240⟩, ⟨.privateRow 9 8, 3029567551722391680⟩, ⟨.privateRow 9 9, 5998888021450303980⟩, ⟨.privateRow 9 10, 13421902304903444352⟩, ⟨.privateRow 9 11, 25584107798798508960⟩, ⟨.privateRow 9 12, 48081143766671104320⟩, ⟨.privateRow 9 13, 63012709948892623920⟩, ⟨.privateRow 10 3, 250824586262730480⟩, ⟨.privateRow 10 5, 4158407614355794800⟩, ⟨.privateRow 10 6, 4389430259597783400⟩, ⟨.privateRow 10 7, 12083843302892721360⟩, ⟨.privateRow 10 8, 23373716132358196605⟩, ⟨.privateRow 10 9, 11939250306105970848⟩, ⟨.privateRow 11 1, 798078229017778800⟩, ⟨.privateRow 11 2, 836081954209101600⟩, ⟨.privateRow 11 3, 10534632623034680160⟩, ⟨.privateRow 11 4, 6468634066775680800⟩, ⟨.privateRow 12 0, 4389430259597783400⟩, ⟨.hall 3 29, 626810641070563469520⟩, ⟨.assumptionRow 18, 12948280674609280⟩]
  caps := #[0, 0, 43084165394098829000, 61132380269192632400, 13720318218589030048, 4016518154907738480, 9871000692335306475, 4247088746080979710, 67948279713429115, 264025880276558400, 0, 0, 486011006794982268600, 625363451871562884480] }

theorem case_46_33_18_checked :
    (Witness.linear .conditional case_46_33_18).check 46 33 18 = true := by
  change case_46_33_18.check 46 33 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_33_19 : Certificate := {
  objectiveScale := 1814451607719150400000
  eta := 290931585090997806237522240000
  rows := #[⟨.count 2, 22929643120728289540903308000⟩, ⟨.count 3, 1476077344331727025884996000⟩, ⟨.count 4, 61464419385422071740321600⟩, ⟨.path 3, 252563413075562660393322000⟩, ⟨.path 4, 57569959063106566487611200⟩, ⟨.path 5, 188903286542232600338000⟩, ⟨.privateRow 2 30, 2125644503745846647686122000⟩, ⟨.privateRow 3 28, 2245934718452165096167812000⟩, ⟨.privateRow 3 29, 112529555693007580837710000⟩, ⟨.privateRow 4 26, 653292275740508838270236400⟩, ⟨.privateRow 4 27, 888595457024094345235710000⟩, ⟨.privateRow 5 19, 41390181404324627434560⟩, ⟨.privateRow 5 20, 6553445389018066010472000⟩, ⟨.privateRow 5 22, 27376648557431860717430400⟩, ⟨.privateRow 5 23, 25765387924192080578013600⟩, ⟨.privateRow 5 24, 123673862036121986774465280⟩, ⟨.privateRow 5 25, 209072153818594774328821200⟩, ⟨.privateRow 6 15, 9949562837578035441000⟩, ⟨.privateRow 6 16, 75450851518300102094250⟩, ⟨.privateRow 6 17, 1046513109370707909567000⟩, ⟨.privateRow 6 18, 556180562620612181151900⟩, ⟨.privateRow 6 25, 155946131395252268157087000⟩, ⟨.privateRow 7 13, 15838079619001770702000⟩, ⟨.privateRow 7 14, 153507540922632546804000⟩, ⟨.privateRow 7 15, 535855027109559908751000⟩, ⟨.privateRow 7 16, 161260447029836210784000⟩, ⟨.privateRow 7 17, 199559803199422310845200⟩, ⟨.privateRow 7 23, 17627782615948970791326000⟩, ⟨.privateRow 8 11, 17245908918468594764400⟩, ⟨.privateRow 8 12, 83149917999759296185500⟩, ⟨.privateRow 8 13, 447730327691011594845000⟩, ⟨.hall 10 7, 69642922002161508000⟩, ⟨.hall 11 7, 100111700378107167750⟩, ⟨.hall 8 8, 214111887716705998656⟩, ⟨.hall 9 8, 151948193459261472000⟩, ⟨.hall 10 8, 28490286273611526000⟩, ⟨.hall 7 9, 150019620234586230240⟩, ⟨.hall 10 9, 24691581437129989200⟩, ⟨.hall 6 11, 69081696989689876800⟩, ⟨.hall 5 14, 39532030864282511555⟩, ⟨.hall 4 18, 60810049595844669120⟩, ⟨.hall 3 23, 841383392668750123500⟩, ⟨.hall 2 27, 215690332341978508014000⟩, ⟨.hall 1 31, 1482188863304709334154630250⟩]
  caps := #[0, 41272734761115697688098250, 3718474306342807515504000, 2807106463688120097504000, 0, 683274681509486032126160, 197219664754348796979510, 17346743560482085437600, 1070559438583529993280, 284593178345597610705216, 1738466910516891679124000, 0, 18546462469591488792360000, 70328144315194269504000000] }

theorem case_46_33_19_checked :
    (Witness.linear .negative case_46_33_19).check 46 33 19 = true := by
  change case_46_33_19.check 46 33 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_33_20 : Certificate := {
  objectiveScale := 985
  eta := 3871406
  rows := #[⟨.assumptionRow 20, 383⟩]
  caps := #[0, 0, 1595902, 916237, 432972, 206397, 115260, 49180, 28714, 29716, 79698312, 78947660, 55681970, 32878170] }

theorem case_46_33_20_checked :
    (Witness.linear .conditional case_46_33_20).check 46 33 20 = true := by
  change case_46_33_20.check 46 33 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_33_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58786, 58786, 41990] }

theorem case_46_33_21_checked :
    (Witness.linear .negative case_46_33_21).check 46 33 21 = true := by
  change case_46_33_21.check 46 33 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_34_1_checked :
    (Witness.rising).check 46 34 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_34_2_checked :
    (Witness.rising).check 46 34 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_34_3_checked :
    (Witness.rising).check 46 34 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_34_4_checked :
    (Witness.rising).check 46 34 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_34_5_checked :
    (Witness.rising).check 46 34 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_34_6_checked :
    (Witness.rising).check 46 34 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_34_7_checked :
    (Witness.rising).check 46 34 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_34_8_checked :
    (Witness.rising).check 46 34 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_34_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_46_34_9_checked :
    (Witness.linear .positive case_46_34_9).check 46 34 9 = true := by
  change case_46_34_9.check 46 34 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_34_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_46_34_10_checked :
    (Witness.linear .positive case_46_34_10).check 46 34 10 = true := by
  change case_46_34_10.check 46 34 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_34_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_46_34_11_checked :
    (Witness.linear .positive case_46_34_11).check 46 34 11 = true := by
  change case_46_34_11.check 46 34 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_34_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_46_34_12_checked :
    (Witness.linear .positive case_46_34_12).check 46 34 12 = true := by
  change case_46_34_12.check 46 34 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_34_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_46_34_13_checked :
    (Witness.linear .positive case_46_34_13).check 46 34 13 = true := by
  change case_46_34_13.check 46 34 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_34_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_46_34_14_checked :
    (Witness.linear .positive case_46_34_14).check 46 34 14 = true := by
  change case_46_34_14.check 46 34 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_34_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_46_34_15_checked :
    (Witness.linear .positive case_46_34_15).check 46 34 15 = true := by
  change case_46_34_15.check 46 34 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_34_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_46_34_16_checked :
    (Witness.linear .positive case_46_34_16).check 46 34 16 = true := by
  change case_46_34_16.check 46 34 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_34_17 : Certificate := {
  objectiveScale := 5
  eta := 7413705
  rows := #[⟨.assumptionRow 17, 7⟩]
  caps := #[0, 0, 2191555, 653752, 197030, 60078, 18564, 5824, 2002, 600875, 466279, 249964, 108262] }

theorem case_46_34_17_checked :
    (Witness.linear .conditional case_46_34_17).check 46 34 17 = true := by
  change case_46_34_17.check 46 34 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_34_18 : Certificate := {
  objectiveScale := 550
  eta := 838089525
  rows := #[⟨.assumptionRow 18, 607⟩]
  caps := #[0, 0, 262604225, 82209314, 25759250, 8091150, 2551020, 889304, 314314, 90611950, 78272381, 47300880, 23456697] }

theorem case_46_34_18_checked :
    (Witness.linear .conditional case_46_34_18).check 46 34 18 = true := by
  change case_46_34_18.check 46 34 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_34_19 : Certificate := {
  objectiveScale := 999
  eta := 531535290
  rows := #[⟨.assumptionRow 19, 799⟩]
  caps := #[0, 0, 186848090, 68076734, 23396505, 7736496, 3093048, 1140020, 482885, 208049145, 196043881, 130668681, 72427905] }

theorem case_46_34_19_checked :
    (Witness.linear .conditional case_46_34_19).check 46 34 19 = true := by
  change case_46_34_19.check 46 34 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_34_20 : Certificate := {
  objectiveScale := 13
  eta := 46046
  rows := #[⟨.assumptionRow 20, 5⟩]
  caps := #[0, 0, 20020, 11305, 5130, 2601, 1428, 580, 364, 3714500, 3684784, 2615008, 1563320] }

theorem case_46_34_20_checked :
    (Witness.linear .conditional case_46_34_20).check 46 34 20 = true := by
  change case_46_34_20.check 46 34 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_34_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208012, 208012, 149226] }

theorem case_46_34_21_checked :
    (Witness.linear .negative case_46_34_21).check 46 34 21 = true := by
  change case_46_34_21.check 46 34 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_34_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58786] }

theorem case_46_34_22_checked :
    (Witness.linear .negative case_46_34_22).check 46 34 22 = true := by
  change case_46_34_22.check 46 34 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_35_1_checked :
    (Witness.rising).check 46 35 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_35_2_checked :
    (Witness.rising).check 46 35 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_35_3_checked :
    (Witness.rising).check 46 35 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_35_4_checked :
    (Witness.rising).check 46 35 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_35_5_checked :
    (Witness.rising).check 46 35 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_35_6_checked :
    (Witness.rising).check 46 35 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_35_7_checked :
    (Witness.rising).check 46 35 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_35_8_checked :
    (Witness.rising).check 46 35 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_35_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_46_35_9_checked :
    (Witness.linear .positive case_46_35_9).check 46 35 9 = true := by
  change case_46_35_9.check 46 35 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_35_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_46_35_10_checked :
    (Witness.linear .positive case_46_35_10).check 46 35 10 = true := by
  change case_46_35_10.check 46 35 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_35_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_46_35_11_checked :
    (Witness.linear .positive case_46_35_11).check 46 35 11 = true := by
  change case_46_35_11.check 46 35 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_35_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_46_35_12_checked :
    (Witness.linear .positive case_46_35_12).check 46 35 12 = true := by
  change case_46_35_12.check 46 35 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_35_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_46_35_13_checked :
    (Witness.linear .positive case_46_35_13).check 46 35 13 = true := by
  change case_46_35_13.check 46 35 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_35_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_46_35_14_checked :
    (Witness.linear .positive case_46_35_14).check 46 35 14 = true := by
  change case_46_35_14.check 46 35 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_35_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_46_35_15_checked :
    (Witness.linear .positive case_46_35_15).check 46 35 15 = true := by
  change case_46_35_15.check 46 35 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_35_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_46_35_16_checked :
    (Witness.linear .positive case_46_35_16).check 46 35 16 = true := by
  change case_46_35_16.check 46 35 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_35_17 : Certificate := {
  objectiveScale := 8
  eta := 75847905
  rows := #[⟨.assumptionRow 17, 21⟩]
  caps := #[0, 0, 21395520, 6091780, 1753244, 510986, 151164, 45526, 14014, 4433, 1452, 498] }

theorem case_46_35_17_checked :
    (Witness.linear .conditional case_46_35_17).check 46 35 17 = true := by
  change case_46_35_17.check 46 35 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_35_18 : Certificate := {
  objectiveScale := 207
  eta := 544012560
  rows := #[⟨.assumptionRow 18, 254⟩]
  caps := #[0, 0, 160516655, 48177065, 15363172, 4919290, 1585284, 515372, 170430, 55929445, 46387550, 26875937] }

theorem case_46_35_18_checked :
    (Witness.linear .conditional case_46_35_18).check 46 35 18 = true := by
  change case_46_35_18.check 46 35 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_35_19 : Certificate := {
  objectiveScale := 25
  eta := 19967220
  rows := #[⟨.assumptionRow 19, 21⟩]
  caps := #[0, 0, 6874010, 2278518, 735471, 281010, 100776, 34748, 12015315, 14429740, 10455225, 6124118] }

theorem case_46_35_19_checked :
    (Witness.linear .conditional case_46_35_19).check 46 35 19 = true := by
  change case_46_35_19.check 46 35 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_35_20 : Certificate := {
  objectiveScale := 153
  eta := 4409790
  rows := #[⟨.assumptionRow 20, 77⟩]
  caps := #[0, 0, 2196040, 807576, 413763, 159885, 80784, 33116, 74550015, 109614895, 87476475, 55977515] }

theorem case_46_35_20_checked :
    (Witness.linear .conditional case_46_35_20).check 46 35 20 = true := by
  change case_46_35_20.check 46 35 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_35_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900, 534888] }

theorem case_46_35_21_checked :
    (Witness.linear .negative case_46_35_21).check 46 35 21 = true := by
  change case_46_35_21.check 46 35 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_35_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208012] }

theorem case_46_35_22_checked :
    (Witness.linear .negative case_46_35_22).check 46 35 22 = true := by
  change case_46_35_22.check 46 35 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_36_1_checked :
    (Witness.rising).check 46 36 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_36_2_checked :
    (Witness.rising).check 46 36 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_36_3_checked :
    (Witness.rising).check 46 36 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_36_4_checked :
    (Witness.rising).check 46 36 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_36_5_checked :
    (Witness.rising).check 46 36 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_36_6_checked :
    (Witness.rising).check 46 36 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_36_7_checked :
    (Witness.rising).check 46 36 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_36_8_checked :
    (Witness.rising).check 46 36 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_36_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_46_36_9_checked :
    (Witness.linear .positive case_46_36_9).check 46 36 9 = true := by
  change case_46_36_9.check 46 36 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_36_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_46_36_10_checked :
    (Witness.linear .positive case_46_36_10).check 46 36 10 = true := by
  change case_46_36_10.check 46 36 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_36_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_46_36_11_checked :
    (Witness.linear .positive case_46_36_11).check 46 36 11 = true := by
  change case_46_36_11.check 46 36 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_36_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_46_36_12_checked :
    (Witness.linear .positive case_46_36_12).check 46 36 12 = true := by
  change case_46_36_12.check 46 36 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_36_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_46_36_13_checked :
    (Witness.linear .positive case_46_36_13).check 46 36 13 = true := by
  change case_46_36_13.check 46 36 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_36_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_46_36_14_checked :
    (Witness.linear .positive case_46_36_14).check 46 36 14 = true := by
  change case_46_36_14.check 46 36 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_36_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_46_36_15_checked :
    (Witness.linear .positive case_46_36_15).check 46 36 15 = true := by
  change case_46_36_15.check 46 36 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_36_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_46_36_16_checked :
    (Witness.linear .positive case_46_36_16).check 46 36 16 = true := by
  change case_46_36_16.check 46 36 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_36_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_46_36_17_checked :
    (Witness.linear .positive case_46_36_17).check 46 36 17 = true := by
  change case_46_36_17.check 46 36 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_36_18 : Certificate := {
  objectiveScale := 772
  eta := 3204241320
  rows := #[⟨.assumptionRow 18, 1037⟩]
  caps := #[0, 0, 954322785, 286313660, 86622140, 26460160, 8172546, 2556528, 816270, 336563370, 268135725] }

theorem case_46_36_18_checked :
    (Witness.linear .conditional case_46_36_18).check 46 36 18 = true := by
  change case_46_36_18.check 46 36 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_36_19 : Certificate := {
  objectiveScale := 597
  eta := 890362200
  rows := #[⟨.assumptionRow 19, 551⟩]
  caps := #[0, 0, 297059490, 101451735, 33749947, 11029158, 3558168, 1338648, 740262705, 681208710, 444935920] }

theorem case_46_36_19_checked :
    (Witness.linear .conditional case_46_36_19).check 46 36 19 = true := by
  change case_46_36_19.check 46 36 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_36_20 : Certificate := {
  objectiveScale := 957
  eta := 158414685
  rows := #[⟨.assumptionRow 20, 581⟩]
  caps := #[0, 0, 58563175, 23809071, 9532908, 3574641, 1589160, 585548, 1519986510, 1485553095, 1039850240] }

theorem case_46_36_20_checked :
    (Witness.linear .conditional case_46_36_20).check 46 36 20 = true := by
  change case_46_36_20.check 46 36 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_36_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 2674440, 2674440, 1931540] }

theorem case_46_36_21_checked :
    (Witness.linear .negative case_46_36_21).check 46 36 21 = true := by
  change case_46_36_21.check 46 36 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_36_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 742900] }

theorem case_46_36_22_checked :
    (Witness.linear .negative case_46_36_22).check 46 36 22 = true := by
  change case_46_36_22.check 46 36 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_36_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_36_23_checked :
    (Witness.linear .negative case_46_36_23).check 46 36 23 = true := by
  change case_46_36_23.check 46 36 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_37_1_checked :
    (Witness.rising).check 46 37 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_37_2_checked :
    (Witness.rising).check 46 37 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_37_3_checked :
    (Witness.rising).check 46 37 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_37_4_checked :
    (Witness.rising).check 46 37 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_37_5_checked :
    (Witness.rising).check 46 37 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_37_6_checked :
    (Witness.rising).check 46 37 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_37_7_checked :
    (Witness.rising).check 46 37 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_37_8_checked :
    (Witness.rising).check 46 37 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_37_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_46_37_9_checked :
    (Witness.linear .positive case_46_37_9).check 46 37 9 = true := by
  change case_46_37_9.check 46 37 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_37_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_46_37_10_checked :
    (Witness.linear .positive case_46_37_10).check 46 37 10 = true := by
  change case_46_37_10.check 46 37 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_37_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_46_37_11_checked :
    (Witness.linear .positive case_46_37_11).check 46 37 11 = true := by
  change case_46_37_11.check 46 37 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_37_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_46_37_12_checked :
    (Witness.linear .positive case_46_37_12).check 46 37 12 = true := by
  change case_46_37_12.check 46 37 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_37_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_46_37_13_checked :
    (Witness.linear .positive case_46_37_13).check 46 37 13 = true := by
  change case_46_37_13.check 46 37 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_37_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_46_37_14_checked :
    (Witness.linear .positive case_46_37_14).check 46 37 14 = true := by
  change case_46_37_14.check 46 37 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_37_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_46_37_15_checked :
    (Witness.linear .positive case_46_37_15).check 46 37 15 = true := by
  change case_46_37_15.check 46 37 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_37_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_46_37_16_checked :
    (Witness.linear .positive case_46_37_16).check 46 37 16 = true := by
  change case_46_37_16.check 46 37 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_37_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_46_37_17_checked :
    (Witness.linear .positive case_46_37_17).check 46 37 17 = true := by
  change case_46_37_17.check 46 37 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_37_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_46_37_18_checked :
    (Witness.linear .positive case_46_37_18).check 46 37 18 = true := by
  change case_46_37_18.check 46 37 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_37_19 : Certificate := {
  objectiveScale := 365
  eta := 1273726545
  rows := #[⟨.assumptionRow 19, 381⟩]
  caps := #[0, 0, 384660510, 121573400, 40287467, 13217160, 4312050, 1403520, 763871745, 679764540] }

theorem case_46_37_19_checked :
    (Witness.linear .conditional case_46_37_19).check 46 37 19 = true := by
  change case_46_37_19.check 46 37 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_37_20 : Certificate := {
  objectiveScale := 5
  eta := 740025
  rows := #[⟨.assumptionRow 20, 3⟩]
  caps := #[0, 0, 284625, 110561, 46398, 16473, 7752, 28514250, 27943965, 19684665] }

theorem case_46_37_20_checked :
    (Witness.linear .conditional case_46_37_20).check 46 37 20 = true := by
  change case_46_37_20.check 46 37 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_37_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 9694845, 9694845, 7020405] }

theorem case_46_37_21_checked :
    (Witness.linear .negative case_46_37_21).check 46 37 21 = true := by
  change case_46_37_21.check 46 37 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_37_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440] }

theorem case_46_37_22_checked :
    (Witness.linear .negative case_46_37_22).check 46 37 22 = true := by
  change case_46_37_22.check 46 37 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_37_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_37_23_checked :
    (Witness.linear .negative case_46_37_23).check 46 37 23 = true := by
  change case_46_37_23.check 46 37 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_37_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_37_24_checked :
    (Witness.linear .negative case_46_37_24).check 46 37 24 = true := by
  change case_46_37_24.check 46 37 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_38_1_checked :
    (Witness.rising).check 46 38 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_38_2_checked :
    (Witness.rising).check 46 38 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_38_3_checked :
    (Witness.rising).check 46 38 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_38_4_checked :
    (Witness.rising).check 46 38 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_38_5_checked :
    (Witness.rising).check 46 38 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_38_6_checked :
    (Witness.rising).check 46 38 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_38_7_checked :
    (Witness.rising).check 46 38 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_38_8_checked :
    (Witness.rising).check 46 38 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_38_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1] }

theorem case_46_38_9_checked :
    (Witness.linear .positive case_46_38_9).check 46 38 9 = true := by
  change case_46_38_9.check 46 38 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_38_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_46_38_10_checked :
    (Witness.linear .positive case_46_38_10).check 46 38 10 = true := by
  change case_46_38_10.check 46 38 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_38_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_46_38_11_checked :
    (Witness.linear .positive case_46_38_11).check 46 38 11 = true := by
  change case_46_38_11.check 46 38 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_38_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_46_38_12_checked :
    (Witness.linear .positive case_46_38_12).check 46 38 12 = true := by
  change case_46_38_12.check 46 38 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_38_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_46_38_13_checked :
    (Witness.linear .positive case_46_38_13).check 46 38 13 = true := by
  change case_46_38_13.check 46 38 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_38_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_46_38_14_checked :
    (Witness.linear .positive case_46_38_14).check 46 38 14 = true := by
  change case_46_38_14.check 46 38 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_38_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_46_38_15_checked :
    (Witness.linear .positive case_46_38_15).check 46 38 15 = true := by
  change case_46_38_15.check 46 38 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_38_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_46_38_16_checked :
    (Witness.linear .positive case_46_38_16).check 46 38 16 = true := by
  change case_46_38_16.check 46 38 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_38_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_46_38_17_checked :
    (Witness.linear .positive case_46_38_17).check 46 38 17 = true := by
  change case_46_38_17.check 46 38 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_38_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_46_38_18_checked :
    (Witness.linear .positive case_46_38_18).check 46 38 18 = true := by
  change case_46_38_18.check 46 38 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_38_19 : Certificate := {
  objectiveScale := 3
  eta := 99249600
  rows := #[⟨.assumptionRow 19, 5⟩]
  caps := #[0, 0, 28514250, 8259300, 2414425, 713184, 213180, 64600, 19890] }

theorem case_46_38_19_checked :
    (Witness.linear .conditional case_46_38_19).check 46 38 19 = true := by
  change case_46_38_19.check 46 38 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_38_20 : Certificate := {
  objectiveScale := 779
  eta := 822140865
  rows := #[⟨.assumptionRow 20, 592⟩]
  caps := #[0, 0, 298082070, 101067175, 35326643, 13611543, 4962480, 7347571950, 7050073275] }

theorem case_46_38_20_checked :
    (Witness.linear .conditional case_46_38_20).check 46 38 20 = true := by
  change case_46_38_20.check 46 38 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_38_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 35357670, 35357670, 25662825] }

theorem case_46_38_21_checked :
    (Witness.linear .negative case_46_38_21).check 46 38 21 = true := by
  change case_46_38_21.check 46 38 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_38_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 9694845] }

theorem case_46_38_22_checked :
    (Witness.linear .negative case_46_38_22).check 46 38 22 = true := by
  change case_46_38_22.check 46 38 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_38_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_38_23_checked :
    (Witness.linear .negative case_46_38_23).check 46 38 23 = true := by
  change case_46_38_23.check 46 38 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_38_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_38_24_checked :
    (Witness.linear .negative case_46_38_24).check 46 38 24 = true := by
  change case_46_38_24.check 46 38 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_39_1_checked :
    (Witness.rising).check 46 39 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_39_2_checked :
    (Witness.rising).check 46 39 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_39_3_checked :
    (Witness.rising).check 46 39 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_39_4_checked :
    (Witness.rising).check 46 39 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_39_5_checked :
    (Witness.rising).check 46 39 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_39_6_checked :
    (Witness.rising).check 46 39 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_39_7_checked :
    (Witness.rising).check 46 39 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_39_8_checked :
    (Witness.rising).check 46 39 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_39_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_46_39_9_checked :
    (Witness.linear .positive case_46_39_9).check 46 39 9 = true := by
  change case_46_39_9.check 46 39 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_39_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_46_39_10_checked :
    (Witness.linear .positive case_46_39_10).check 46 39 10 = true := by
  change case_46_39_10.check 46 39 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_39_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_46_39_11_checked :
    (Witness.linear .positive case_46_39_11).check 46 39 11 = true := by
  change case_46_39_11.check 46 39 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_39_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_46_39_12_checked :
    (Witness.linear .positive case_46_39_12).check 46 39 12 = true := by
  change case_46_39_12.check 46 39 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_39_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42] }

theorem case_46_39_13_checked :
    (Witness.linear .positive case_46_39_13).check 46 39 13 = true := by
  change case_46_39_13.check 46 39 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_39_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_46_39_14_checked :
    (Witness.linear .positive case_46_39_14).check 46 39 14 = true := by
  change case_46_39_14.check 46 39 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_39_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_46_39_15_checked :
    (Witness.linear .positive case_46_39_15).check 46 39 15 = true := by
  change case_46_39_15.check 46 39 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_39_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_46_39_16_checked :
    (Witness.linear .positive case_46_39_16).check 46 39 16 = true := by
  change case_46_39_16.check 46 39 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_39_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_46_39_17_checked :
    (Witness.linear .positive case_46_39_17).check 46 39 17 = true := by
  change case_46_39_17.check 46 39 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_39_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_46_39_18_checked :
    (Witness.linear .positive case_46_39_18).check 46 39 18 = true := by
  change case_46_39_18.check 46 39 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_39_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_46_39_19_checked :
    (Witness.linear .positive case_46_39_19).check 46 39 19 = true := by
  change case_46_39_19.check 46 39 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_39_20 : Certificate := {
  objectiveScale := 998
  eta := 3731955045
  rows := #[⟨.assumptionRow 20, 887⟩]
  caps := #[0, 0, 1203621510, 380882645, 127794095, 45272326, 27293640, 15971741880] }

theorem case_46_39_20_checked :
    (Witness.linear .conditional case_46_39_20).check 46 39 20 = true := by
  change case_46_39_20.check 46 39 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_39_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 129644790, 129644790, 94287120] }

theorem case_46_39_21_checked :
    (Witness.linear .negative case_46_39_21).check 46 39 21 = true := by
  change case_46_39_21.check 46 39 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_39_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 35357670] }

theorem case_46_39_22_checked :
    (Witness.linear .negative case_46_39_22).check 46 39 22 = true := by
  change case_46_39_22.check 46 39 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_39_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_39_23_checked :
    (Witness.linear .negative case_46_39_23).check 46 39 23 = true := by
  change case_46_39_23.check 46 39 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_39_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_39_24_checked :
    (Witness.linear .negative case_46_39_24).check 46 39 24 = true := by
  change case_46_39_24.check 46 39 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_39_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_46_39_25_checked :
    (Witness.linear .negative case_46_39_25).check 46 39 25 = true := by
  change case_46_39_25.check 46 39 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_40_1_checked :
    (Witness.rising).check 46 40 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_40_2_checked :
    (Witness.rising).check 46 40 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_40_3_checked :
    (Witness.rising).check 46 40 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_40_4_checked :
    (Witness.rising).check 46 40 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_40_5_checked :
    (Witness.rising).check 46 40 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_40_6_checked :
    (Witness.rising).check 46 40 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_40_7_checked :
    (Witness.rising).check 46 40 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_40_8_checked :
    (Witness.rising).check 46 40 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_40_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_46_40_9_checked :
    (Witness.linear .positive case_46_40_9).check 46 40 9 = true := by
  change case_46_40_9.check 46 40 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_40_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_46_40_10_checked :
    (Witness.linear .positive case_46_40_10).check 46 40 10 = true := by
  change case_46_40_10.check 46 40 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_40_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_46_40_11_checked :
    (Witness.linear .positive case_46_40_11).check 46 40 11 = true := by
  change case_46_40_11.check 46 40 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_40_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_46_40_12_checked :
    (Witness.linear .positive case_46_40_12).check 46 40 12 = true := by
  change case_46_40_12.check 46 40 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_40_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_46_40_13_checked :
    (Witness.linear .positive case_46_40_13).check 46 40 13 = true := by
  change case_46_40_13.check 46 40 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_40_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429] }

theorem case_46_40_14_checked :
    (Witness.linear .positive case_46_40_14).check 46 40 14 = true := by
  change case_46_40_14.check 46 40 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_40_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430] }

theorem case_46_40_15_checked :
    (Witness.linear .positive case_46_40_15).check 46 40 15 = true := by
  change case_46_40_15.check 46 40 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_40_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862] }

theorem case_46_40_16_checked :
    (Witness.linear .positive case_46_40_16).check 46 40 16 = true := by
  change case_46_40_16.check 46 40 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_40_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796] }

theorem case_46_40_17_checked :
    (Witness.linear .positive case_46_40_17).check 46 40 17 = true := by
  change case_46_40_17.check 46 40 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_40_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_46_40_18_checked :
    (Witness.linear .positive case_46_40_18).check 46 40 18 = true := by
  change case_46_40_18.check 46 40 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_40_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_46_40_19_checked :
    (Witness.linear .positive case_46_40_19).check 46 40 19 = true := by
  change case_46_40_19.check 46 40 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_40_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_46_40_20_checked :
    (Witness.linear .positive case_46_40_20).check 46 40 20 = true := by
  change case_46_40_20.check 46 40 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_40_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 477638700, 477638700, 347993910] }

theorem case_46_40_21_checked :
    (Witness.linear .negative case_46_40_21).check 46 40 21 = true := by
  change case_46_40_21.check 46 40 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_40_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 129644790] }

theorem case_46_40_22_checked :
    (Witness.linear .negative case_46_40_22).check 46 40 22 = true := by
  change case_46_40_22.check 46 40 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_40_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_46_40_23_checked :
    (Witness.linear .negative case_46_40_23).check 46 40 23 = true := by
  change case_46_40_23.check 46 40 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_40_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_46_40_24_checked :
    (Witness.linear .negative case_46_40_24).check 46 40 24 = true := by
  change case_46_40_24.check 46 40 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_40_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_46_40_25_checked :
    (Witness.linear .negative case_46_40_25).check 46 40 25 = true := by
  change case_46_40_25.check 46 40 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_40_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_46_40_26_checked :
    (Witness.linear .negative case_46_40_26).check 46 40 26 = true := by
  change case_46_40_26.check 46 40 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_41_1_checked :
    (Witness.rising).check 46 41 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_41_2_checked :
    (Witness.rising).check 46 41 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_41_3_checked :
    (Witness.rising).check 46 41 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_41_4_checked :
    (Witness.rising).check 46 41 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_41_5_checked :
    (Witness.rising).check 46 41 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_41_6_checked :
    (Witness.rising).check 46 41 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_41_7_checked :
    (Witness.rising).check 46 41 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_41_8_checked :
    (Witness.rising).check 46 41 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_41_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_46_41_9_checked :
    (Witness.linear .positive case_46_41_9).check 46 41 9 = true := by
  change case_46_41_9.check 46 41 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_41_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_46_41_10_checked :
    (Witness.linear .positive case_46_41_10).check 46 41 10 = true := by
  change case_46_41_10.check 46 41 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_41_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_46_41_11_checked :
    (Witness.linear .positive case_46_41_11).check 46 41 11 = true := by
  change case_46_41_11.check 46 41 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_41_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_46_41_12_checked :
    (Witness.linear .positive case_46_41_12).check 46 41 12 = true := by
  change case_46_41_12.check 46 41 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_41_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_46_41_13_checked :
    (Witness.linear .positive case_46_41_13).check 46 41 13 = true := by
  change case_46_41_13.check 46 41 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_41_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_46_41_14_checked :
    (Witness.linear .positive case_46_41_14).check 46 41 14 = true := by
  change case_46_41_14.check 46 41 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_41_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862] }

theorem case_46_41_15_checked :
    (Witness.linear .positive case_46_41_15).check 46 41 15 = true := by
  change case_46_41_15.check 46 41 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_41_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796] }

theorem case_46_41_16_checked :
    (Witness.linear .positive case_46_41_16).check 46 41 16 = true := by
  change case_46_41_16.check 46 41 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_41_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786] }

theorem case_46_41_17_checked :
    (Witness.linear .positive case_46_41_17).check 46 41 17 = true := by
  change case_46_41_17.check 46 41 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_41_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012] }

theorem case_46_41_18_checked :
    (Witness.linear .positive case_46_41_18).check 46 41 18 = true := by
  change case_46_41_18.check 46 41 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_41_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900] }

theorem case_46_41_19_checked :
    (Witness.linear .positive case_46_41_19).check 46 41 19 = true := by
  change case_46_41_19.check 46 41 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_41_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440] }

theorem case_46_41_20_checked :
    (Witness.linear .positive case_46_41_20).check 46 41 20 = true := by
  change case_46_41_20.check 46 41 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_41_21 : Certificate := {
  objectiveScale := 537
  eta := 1332515925
  rows := #[⟨.assumptionRow 21, 398⟩]
  caps := #[0, 0, 434098665, 167640330, 59967325, 20470230] }

theorem case_46_41_21_checked :
    (Witness.linear .conditional case_46_41_21).check 46 41 21 = true := by
  change case_46_41_21.check 46 41 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_41_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 477638700] }

theorem case_46_41_22_checked :
    (Witness.linear .negative case_46_41_22).check 46 41 22 = true := by
  change case_46_41_22.check 46 41 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_41_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_46_41_23_checked :
    (Witness.linear .negative case_46_41_23).check 46 41 23 = true := by
  change case_46_41_23.check 46 41 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_41_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_46_41_24_checked :
    (Witness.linear .negative case_46_41_24).check 46 41 24 = true := by
  change case_46_41_24.check 46 41 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_41_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_46_41_25_checked :
    (Witness.linear .negative case_46_41_25).check 46 41 25 = true := by
  change case_46_41_25.check 46 41 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_41_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_46_41_26_checked :
    (Witness.linear .negative case_46_41_26).check 46 41 26 = true := by
  change case_46_41_26.check 46 41 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_42_1_checked :
    (Witness.rising).check 46 42 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_42_2_checked :
    (Witness.rising).check 46 42 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_42_3_checked :
    (Witness.rising).check 46 42 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_42_4_checked :
    (Witness.rising).check 46 42 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_42_5_checked :
    (Witness.rising).check 46 42 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_42_6_checked :
    (Witness.rising).check 46 42 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_42_7_checked :
    (Witness.rising).check 46 42 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_42_8_checked :
    (Witness.rising).check 46 42 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_42_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_46_42_9_checked :
    (Witness.linear .positive case_46_42_9).check 46 42 9 = true := by
  change case_46_42_9.check 46 42 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_42_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_46_42_10_checked :
    (Witness.linear .positive case_46_42_10).check 46 42 10 = true := by
  change case_46_42_10.check 46 42 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_42_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_46_42_11_checked :
    (Witness.linear .positive case_46_42_11).check 46 42 11 = true := by
  change case_46_42_11.check 46 42 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_42_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_46_42_12_checked :
    (Witness.linear .positive case_46_42_12).check 46 42 12 = true := by
  change case_46_42_12.check 46 42 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_42_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_46_42_13_checked :
    (Witness.linear .positive case_46_42_13).check 46 42 13 = true := by
  change case_46_42_13.check 46 42 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_42_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_46_42_14_checked :
    (Witness.linear .positive case_46_42_14).check 46 42 14 = true := by
  change case_46_42_14.check 46 42 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_42_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796] }

theorem case_46_42_15_checked :
    (Witness.linear .positive case_46_42_15).check 46 42 15 = true := by
  change case_46_42_15.check 46 42 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_42_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786] }

theorem case_46_42_16_checked :
    (Witness.linear .positive case_46_42_16).check 46 42 16 = true := by
  change case_46_42_16.check 46 42 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_42_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012] }

theorem case_46_42_17_checked :
    (Witness.linear .positive case_46_42_17).check 46 42 17 = true := by
  change case_46_42_17.check 46 42 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_42_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900] }

theorem case_46_42_18_checked :
    (Witness.linear .positive case_46_42_18).check 46 42 18 = true := by
  change case_46_42_18.check 46 42 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_42_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440] }

theorem case_46_42_19_checked :
    (Witness.linear .positive case_46_42_19).check 46 42 19 = true := by
  change case_46_42_19.check 46 42 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_42_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845] }

theorem case_46_42_20_checked :
    (Witness.linear .positive case_46_42_20).check 46 42 20 = true := by
  change case_46_42_20.check 46 42 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_42_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670] }

theorem case_46_42_21_checked :
    (Witness.linear .positive case_46_42_21).check 46 42 21 = true := by
  change case_46_42_21.check 46 42 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_42_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 1767263190] }

theorem case_46_42_22_checked :
    (Witness.linear .negative case_46_42_22).check 46 42 22 = true := by
  change case_46_42_22.check 46 42 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_42_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_46_42_23_checked :
    (Witness.linear .negative case_46_42_23).check 46 42 23 = true := by
  change case_46_42_23.check 46 42 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_42_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_46_42_24_checked :
    (Witness.linear .negative case_46_42_24).check 46 42 24 = true := by
  change case_46_42_24.check 46 42 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_42_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_46_42_25_checked :
    (Witness.linear .negative case_46_42_25).check 46 42 25 = true := by
  change case_46_42_25.check 46 42 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_42_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_46_42_26_checked :
    (Witness.linear .negative case_46_42_26).check 46 42 26 = true := by
  change case_46_42_26.check 46 42 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_42_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_46_42_27_checked :
    (Witness.linear .negative case_46_42_27).check 46 42 27 = true := by
  change case_46_42_27.check 46 42 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_43_1_checked :
    (Witness.rising).check 46 43 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_43_2_checked :
    (Witness.rising).check 46 43 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_43_3_checked :
    (Witness.rising).check 46 43 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_43_4_checked :
    (Witness.rising).check 46 43 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_43_5_checked :
    (Witness.rising).check 46 43 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_43_6_checked :
    (Witness.rising).check 46 43 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_43_7_checked :
    (Witness.rising).check 46 43 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_43_8_checked :
    (Witness.rising).check 46 43 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_43_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_46_43_9_checked :
    (Witness.linear .positive case_46_43_9).check 46 43 9 = true := by
  change case_46_43_9.check 46 43 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_43_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_46_43_10_checked :
    (Witness.linear .positive case_46_43_10).check 46 43 10 = true := by
  change case_46_43_10.check 46 43 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_43_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_46_43_11_checked :
    (Witness.linear .positive case_46_43_11).check 46 43 11 = true := by
  change case_46_43_11.check 46 43 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_43_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_46_43_12_checked :
    (Witness.linear .positive case_46_43_12).check 46 43 12 = true := by
  change case_46_43_12.check 46 43 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_43_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_46_43_13_checked :
    (Witness.linear .positive case_46_43_13).check 46 43 13 = true := by
  change case_46_43_13.check 46 43 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_43_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_46_43_14_checked :
    (Witness.linear .positive case_46_43_14).check 46 43 14 = true := by
  change case_46_43_14.check 46 43 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_43_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_46_43_15_checked :
    (Witness.linear .positive case_46_43_15).check 46 43 15 = true := by
  change case_46_43_15.check 46 43 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_43_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012] }

theorem case_46_43_16_checked :
    (Witness.linear .positive case_46_43_16).check 46 43 16 = true := by
  change case_46_43_16.check 46 43 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_43_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900] }

theorem case_46_43_17_checked :
    (Witness.linear .positive case_46_43_17).check 46 43 17 = true := by
  change case_46_43_17.check 46 43 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_43_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440] }

theorem case_46_43_18_checked :
    (Witness.linear .positive case_46_43_18).check 46 43 18 = true := by
  change case_46_43_18.check 46 43 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_43_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845] }

theorem case_46_43_19_checked :
    (Witness.linear .positive case_46_43_19).check 46 43 19 = true := by
  change case_46_43_19.check 46 43 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_43_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670] }

theorem case_46_43_20_checked :
    (Witness.linear .positive case_46_43_20).check 46 43 20 = true := by
  change case_46_43_20.check 46 43 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_43_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790] }

theorem case_46_43_21_checked :
    (Witness.linear .positive case_46_43_21).check 46 43 21 = true := by
  change case_46_43_21.check 46 43 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_43_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 6564120420] }

theorem case_46_43_22_checked :
    (Witness.linear .negative case_46_43_22).check 46 43 22 = true := by
  change case_46_43_22.check 46 43 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_43_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_46_43_23_checked :
    (Witness.linear .negative case_46_43_23).check 46 43 23 = true := by
  change case_46_43_23.check 46 43 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_43_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_46_43_24_checked :
    (Witness.linear .negative case_46_43_24).check 46 43 24 = true := by
  change case_46_43_24.check 46 43 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_43_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_46_43_25_checked :
    (Witness.linear .negative case_46_43_25).check 46 43 25 = true := by
  change case_46_43_25.check 46 43 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_43_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_46_43_26_checked :
    (Witness.linear .negative case_46_43_26).check 46 43 26 = true := by
  change case_46_43_26.check 46 43 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_43_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_46_43_27_checked :
    (Witness.linear .negative case_46_43_27).check 46 43 27 = true := by
  change case_46_43_27.check 46 43 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_43_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_46_43_28_checked :
    (Witness.linear .negative case_46_43_28).check 46 43 28 = true := by
  change case_46_43_28.check 46 43 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_44_1_checked :
    (Witness.rising).check 46 44 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_44_2_checked :
    (Witness.rising).check 46 44 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_44_3_checked :
    (Witness.rising).check 46 44 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_44_4_checked :
    (Witness.rising).check 46 44 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_44_5_checked :
    (Witness.rising).check 46 44 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_44_6_checked :
    (Witness.rising).check 46 44 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_44_7_checked :
    (Witness.rising).check 46 44 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_44_8_checked :
    (Witness.rising).check 46 44 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_44_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_46_44_9_checked :
    (Witness.linear .positive case_46_44_9).check 46 44 9 = true := by
  change case_46_44_9.check 46 44 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_44_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_46_44_10_checked :
    (Witness.linear .positive case_46_44_10).check 46 44 10 = true := by
  change case_46_44_10.check 46 44 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_44_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_46_44_11_checked :
    (Witness.linear .positive case_46_44_11).check 46 44 11 = true := by
  change case_46_44_11.check 46 44 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_44_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_46_44_12_checked :
    (Witness.linear .positive case_46_44_12).check 46 44 12 = true := by
  change case_46_44_12.check 46 44 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_44_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_46_44_13_checked :
    (Witness.linear .positive case_46_44_13).check 46 44 13 = true := by
  change case_46_44_13.check 46 44 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_44_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_46_44_14_checked :
    (Witness.linear .positive case_46_44_14).check 46 44 14 = true := by
  change case_46_44_14.check 46 44 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_44_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_46_44_15_checked :
    (Witness.linear .positive case_46_44_15).check 46 44 15 = true := by
  change case_46_44_15.check 46 44 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_44_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900] }

theorem case_46_44_16_checked :
    (Witness.linear .positive case_46_44_16).check 46 44 16 = true := by
  change case_46_44_16.check 46 44 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_44_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440] }

theorem case_46_44_17_checked :
    (Witness.linear .positive case_46_44_17).check 46 44 17 = true := by
  change case_46_44_17.check 46 44 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_44_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845] }

theorem case_46_44_18_checked :
    (Witness.linear .positive case_46_44_18).check 46 44 18 = true := by
  change case_46_44_18.check 46 44 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_44_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670] }

theorem case_46_44_19_checked :
    (Witness.linear .positive case_46_44_19).check 46 44 19 = true := by
  change case_46_44_19.check 46 44 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_44_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790] }

theorem case_46_44_20_checked :
    (Witness.linear .positive case_46_44_20).check 46 44 20 = true := by
  change case_46_44_20.check 46 44 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_44_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700] }

theorem case_46_44_21_checked :
    (Witness.linear .positive case_46_44_21).check 46 44 21 = true := by
  change case_46_44_21.check 46 44 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_44_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190] }

theorem case_46_44_22_checked :
    (Witness.linear .positive case_46_44_22).check 46 44 22 = true := by
  change case_46_44_22.check 46 44 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_44_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_46_44_23_checked :
    (Witness.linear .negative case_46_44_23).check 46 44 23 = true := by
  change case_46_44_23.check 46 44 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_44_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_46_44_24_checked :
    (Witness.linear .negative case_46_44_24).check 46 44 24 = true := by
  change case_46_44_24.check 46 44 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_44_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_46_44_25_checked :
    (Witness.linear .negative case_46_44_25).check 46 44 25 = true := by
  change case_46_44_25.check 46 44 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_44_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_46_44_26_checked :
    (Witness.linear .negative case_46_44_26).check 46 44 26 = true := by
  change case_46_44_26.check 46 44 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_44_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_46_44_27_checked :
    (Witness.linear .negative case_46_44_27).check 46 44 27 = true := by
  change case_46_44_27.check 46 44 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_44_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_46_44_28_checked :
    (Witness.linear .negative case_46_44_28).check 46 44 28 = true := by
  change case_46_44_28.check 46 44 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_45_1_checked :
    (Witness.rising).check 46 45 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_45_2_checked :
    (Witness.rising).check 46 45 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_45_3_checked :
    (Witness.rising).check 46 45 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_45_4_checked :
    (Witness.rising).check 46 45 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_45_5_checked :
    (Witness.rising).check 46 45 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_45_6_checked :
    (Witness.rising).check 46 45 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_45_7_checked :
    (Witness.rising).check 46 45 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_46_45_8_checked :
    (Witness.rising).check 46 45 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_45_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_46_45_9_checked :
    (Witness.linear .positive case_46_45_9).check 46 45 9 = true := by
  change case_46_45_9.check 46 45 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_45_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_46_45_10_checked :
    (Witness.linear .positive case_46_45_10).check 46 45 10 = true := by
  change case_46_45_10.check 46 45 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_45_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_46_45_11_checked :
    (Witness.linear .positive case_46_45_11).check 46 45 11 = true := by
  change case_46_45_11.check 46 45 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_45_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_46_45_12_checked :
    (Witness.linear .positive case_46_45_12).check 46 45 12 = true := by
  change case_46_45_12.check 46 45 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_45_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_46_45_13_checked :
    (Witness.linear .positive case_46_45_13).check 46 45 13 = true := by
  change case_46_45_13.check 46 45 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_45_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_46_45_14_checked :
    (Witness.linear .positive case_46_45_14).check 46 45 14 = true := by
  change case_46_45_14.check 46 45 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_45_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_46_45_15_checked :
    (Witness.linear .positive case_46_45_15).check 46 45 15 = true := by
  change case_46_45_15.check 46 45 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_45_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_46_45_16_checked :
    (Witness.linear .positive case_46_45_16).check 46 45 16 = true := by
  change case_46_45_16.check 46 45 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_45_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0] }

theorem case_46_45_17_checked :
    (Witness.linear .positive case_46_45_17).check 46 45 17 = true := by
  change case_46_45_17.check 46 45 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_45_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0] }

theorem case_46_45_18_checked :
    (Witness.linear .positive case_46_45_18).check 46 45 18 = true := by
  change case_46_45_18.check 46 45 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_45_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0] }

theorem case_46_45_19_checked :
    (Witness.linear .positive case_46_45_19).check 46 45 19 = true := by
  change case_46_45_19.check 46 45 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_45_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0] }

theorem case_46_45_20_checked :
    (Witness.linear .positive case_46_45_20).check 46 45 20 = true := by
  change case_46_45_20.check 46 45 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_45_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0] }

theorem case_46_45_21_checked :
    (Witness.linear .positive case_46_45_21).check 46 45 21 = true := by
  change case_46_45_21.check 46 45 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_45_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0] }

theorem case_46_45_22_checked :
    (Witness.linear .positive case_46_45_22).check 46 45 22 = true := by
  change case_46_45_22.check 46 45 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_45_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_46_45_23_checked :
    (Witness.linear .negative case_46_45_23).check 46 45 23 = true := by
  change case_46_45_23.check 46 45 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_45_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_46_45_24_checked :
    (Witness.linear .negative case_46_45_24).check 46 45 24 = true := by
  change case_46_45_24.check 46 45 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_45_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_46_45_25_checked :
    (Witness.linear .negative case_46_45_25).check 46 45 25 = true := by
  change case_46_45_25.check 46 45 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_45_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_46_45_26_checked :
    (Witness.linear .negative case_46_45_26).check 46 45 26 = true := by
  change case_46_45_26.check 46 45 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_45_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_46_45_27_checked :
    (Witness.linear .negative case_46_45_27).check 46 45 27 = true := by
  change case_46_45_27.check 46 45 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_45_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_46_45_28_checked :
    (Witness.linear .negative case_46_45_28).check 46 45 28 = true := by
  change case_46_45_28.check 46 45 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_46_45_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_46_45_29_checked :
    (Witness.linear .negative case_46_45_29).check 46 45 29 = true := by
  change case_46_45_29.check 46 45 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_46 (a k : ℕ) (h : Domain 46 a k) :
    ∃ w : Witness, w.check 46 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 23 ≤ a := by omega
  have haHi : a ≤ 45 := by omega
  interval_cases a

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_46_23_1_checked⟩

    · exact ⟨Witness.rising, case_46_23_2_checked⟩

    · exact ⟨Witness.rising, case_46_23_3_checked⟩

    · exact ⟨Witness.rising, case_46_23_4_checked⟩

    · exact ⟨Witness.rising, case_46_23_5_checked⟩

    · exact ⟨Witness.rising, case_46_23_6_checked⟩

    · exact ⟨Witness.rising, case_46_23_7_checked⟩

    · exact ⟨Witness.rising, case_46_23_8_checked⟩

    · exact ⟨Witness.rising, case_46_23_9_checked⟩

    · exact ⟨Witness.linear .positive case_46_23_10, case_46_23_10_checked⟩

    · exact ⟨Witness.linear .positive case_46_23_11, case_46_23_11_checked⟩

    · exact ⟨Witness.linear .positive case_46_23_12, case_46_23_12_checked⟩

    · exact ⟨Witness.linear .conditional case_46_23_13, case_46_23_13_checked⟩

    · exact ⟨Witness.linear .conditional case_46_23_14, case_46_23_14_checked⟩

  · have hkHi : k ≤ 15 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_46_24_1_checked⟩

    · exact ⟨Witness.rising, case_46_24_2_checked⟩

    · exact ⟨Witness.rising, case_46_24_3_checked⟩

    · exact ⟨Witness.rising, case_46_24_4_checked⟩

    · exact ⟨Witness.rising, case_46_24_5_checked⟩

    · exact ⟨Witness.rising, case_46_24_6_checked⟩

    · exact ⟨Witness.rising, case_46_24_7_checked⟩

    · exact ⟨Witness.rising, case_46_24_8_checked⟩

    · exact ⟨Witness.rising, case_46_24_9_checked⟩

    · exact ⟨Witness.linear .positive case_46_24_10, case_46_24_10_checked⟩

    · exact ⟨Witness.linear .positive case_46_24_11, case_46_24_11_checked⟩

    · exact ⟨Witness.linear .positive case_46_24_12, case_46_24_12_checked⟩

    · exact ⟨Witness.linear .positive case_46_24_13, case_46_24_13_checked⟩

    · exact ⟨Witness.linear .conditional case_46_24_14, case_46_24_14_checked⟩

    · exact ⟨Witness.linear .conditional case_46_24_15, case_46_24_15_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_46_25_1_checked⟩

    · exact ⟨Witness.rising, case_46_25_2_checked⟩

    · exact ⟨Witness.rising, case_46_25_3_checked⟩

    · exact ⟨Witness.rising, case_46_25_4_checked⟩

    · exact ⟨Witness.rising, case_46_25_5_checked⟩

    · exact ⟨Witness.rising, case_46_25_6_checked⟩

    · exact ⟨Witness.rising, case_46_25_7_checked⟩

    · exact ⟨Witness.rising, case_46_25_8_checked⟩

    · exact ⟨Witness.rising, case_46_25_9_checked⟩

    · exact ⟨Witness.linear .positive case_46_25_10, case_46_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_46_25_11, case_46_25_11_checked⟩

    · exact ⟨Witness.linear .positive case_46_25_12, case_46_25_12_checked⟩

    · exact ⟨Witness.linear .positive case_46_25_13, case_46_25_13_checked⟩

    · exact ⟨Witness.linear .conditional case_46_25_14, case_46_25_14_checked⟩

    · exact ⟨Witness.linear .conditional case_46_25_15, case_46_25_15_checked⟩

    · exact ⟨Witness.linear .conditional case_46_25_16, case_46_25_16_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_46_26_1_checked⟩

    · exact ⟨Witness.rising, case_46_26_2_checked⟩

    · exact ⟨Witness.rising, case_46_26_3_checked⟩

    · exact ⟨Witness.rising, case_46_26_4_checked⟩

    · exact ⟨Witness.rising, case_46_26_5_checked⟩

    · exact ⟨Witness.rising, case_46_26_6_checked⟩

    · exact ⟨Witness.rising, case_46_26_7_checked⟩

    · exact ⟨Witness.rising, case_46_26_8_checked⟩

    · exact ⟨Witness.rising, case_46_26_9_checked⟩

    · exact ⟨Witness.linear .positive case_46_26_10, case_46_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_46_26_11, case_46_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_46_26_12, case_46_26_12_checked⟩

    · exact ⟨Witness.linear .positive case_46_26_13, case_46_26_13_checked⟩

    · exact ⟨Witness.linear .conditional case_46_26_14, case_46_26_14_checked⟩

    · exact ⟨Witness.linear .conditional case_46_26_15, case_46_26_15_checked⟩

    · exact ⟨Witness.linear .conditional case_46_26_16, case_46_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_46_27_1_checked⟩

    · exact ⟨Witness.rising, case_46_27_2_checked⟩

    · exact ⟨Witness.rising, case_46_27_3_checked⟩

    · exact ⟨Witness.rising, case_46_27_4_checked⟩

    · exact ⟨Witness.rising, case_46_27_5_checked⟩

    · exact ⟨Witness.rising, case_46_27_6_checked⟩

    · exact ⟨Witness.rising, case_46_27_7_checked⟩

    · exact ⟨Witness.rising, case_46_27_8_checked⟩

    · exact ⟨Witness.rising, case_46_27_9_checked⟩

    · exact ⟨Witness.linear .positive case_46_27_10, case_46_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_46_27_11, case_46_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_46_27_12, case_46_27_12_checked⟩

    · exact ⟨Witness.linear .positive case_46_27_13, case_46_27_13_checked⟩

    · exact ⟨Witness.linear .conditional case_46_27_14, case_46_27_14_checked⟩

    · exact ⟨Witness.linear .conditional case_46_27_15, case_46_27_15_checked⟩

    · exact ⟨Witness.linear .conditional case_46_27_16, case_46_27_16_checked⟩

    · exact ⟨Witness.linear .negative case_46_27_17, case_46_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_46_28_1_checked⟩

    · exact ⟨Witness.rising, case_46_28_2_checked⟩

    · exact ⟨Witness.rising, case_46_28_3_checked⟩

    · exact ⟨Witness.rising, case_46_28_4_checked⟩

    · exact ⟨Witness.rising, case_46_28_5_checked⟩

    · exact ⟨Witness.rising, case_46_28_6_checked⟩

    · exact ⟨Witness.rising, case_46_28_7_checked⟩

    · exact ⟨Witness.rising, case_46_28_8_checked⟩

    · exact ⟨Witness.rising, case_46_28_9_checked⟩

    · exact ⟨Witness.linear .positive case_46_28_10, case_46_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_46_28_11, case_46_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_46_28_12, case_46_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_46_28_13, case_46_28_13_checked⟩

    · exact ⟨Witness.linear .conditional case_46_28_14, case_46_28_14_checked⟩

    · exact ⟨Witness.linear .conditional case_46_28_15, case_46_28_15_checked⟩

    · exact ⟨Witness.linear .conditional case_46_28_16, case_46_28_16_checked⟩

    · exact ⟨Witness.linear .conditional case_46_28_17, case_46_28_17_checked⟩

    · exact ⟨Witness.linear .negative case_46_28_18, case_46_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_46_29_1_checked⟩

    · exact ⟨Witness.rising, case_46_29_2_checked⟩

    · exact ⟨Witness.rising, case_46_29_3_checked⟩

    · exact ⟨Witness.rising, case_46_29_4_checked⟩

    · exact ⟨Witness.rising, case_46_29_5_checked⟩

    · exact ⟨Witness.rising, case_46_29_6_checked⟩

    · exact ⟨Witness.rising, case_46_29_7_checked⟩

    · exact ⟨Witness.rising, case_46_29_8_checked⟩

    · exact ⟨Witness.rising, case_46_29_9_checked⟩

    · exact ⟨Witness.linear .positive case_46_29_10, case_46_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_46_29_11, case_46_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_46_29_12, case_46_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_46_29_13, case_46_29_13_checked⟩

    · exact ⟨Witness.linear .positive case_46_29_14, case_46_29_14_checked⟩

    · exact ⟨Witness.linear .conditional case_46_29_15, case_46_29_15_checked⟩

    · exact ⟨Witness.linear .conditional case_46_29_16, case_46_29_16_checked⟩

    · exact ⟨Witness.linear .conditional case_46_29_17, case_46_29_17_checked⟩

    · exact ⟨Witness.linear .negative case_46_29_18, case_46_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_46_30_1_checked⟩

    · exact ⟨Witness.rising, case_46_30_2_checked⟩

    · exact ⟨Witness.rising, case_46_30_3_checked⟩

    · exact ⟨Witness.rising, case_46_30_4_checked⟩

    · exact ⟨Witness.rising, case_46_30_5_checked⟩

    · exact ⟨Witness.rising, case_46_30_6_checked⟩

    · exact ⟨Witness.rising, case_46_30_7_checked⟩

    · exact ⟨Witness.rising, case_46_30_8_checked⟩

    · exact ⟨Witness.rising, case_46_30_9_checked⟩

    · exact ⟨Witness.linear .positive case_46_30_10, case_46_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_46_30_11, case_46_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_46_30_12, case_46_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_46_30_13, case_46_30_13_checked⟩

    · exact ⟨Witness.linear .conditional case_46_30_14, case_46_30_14_checked⟩

    · exact ⟨Witness.linear .conditional case_46_30_15, case_46_30_15_checked⟩

    · exact ⟨Witness.linear .conditional case_46_30_16, case_46_30_16_checked⟩

    · exact ⟨Witness.linear .conditional case_46_30_17, case_46_30_17_checked⟩

    · exact ⟨Witness.linear .negative case_46_30_18, case_46_30_18_checked⟩

    · exact ⟨Witness.linear .negative case_46_30_19, case_46_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_46_31_1_checked⟩

    · exact ⟨Witness.rising, case_46_31_2_checked⟩

    · exact ⟨Witness.rising, case_46_31_3_checked⟩

    · exact ⟨Witness.rising, case_46_31_4_checked⟩

    · exact ⟨Witness.rising, case_46_31_5_checked⟩

    · exact ⟨Witness.rising, case_46_31_6_checked⟩

    · exact ⟨Witness.rising, case_46_31_7_checked⟩

    · exact ⟨Witness.rising, case_46_31_8_checked⟩

    · exact ⟨Witness.linear .positive case_46_31_9, case_46_31_9_checked⟩

    · exact ⟨Witness.linear .positive case_46_31_10, case_46_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_46_31_11, case_46_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_46_31_12, case_46_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_46_31_13, case_46_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_46_31_14, case_46_31_14_checked⟩

    · exact ⟨Witness.linear .conditional case_46_31_15, case_46_31_15_checked⟩

    · exact ⟨Witness.linear .conditional case_46_31_16, case_46_31_16_checked⟩

    · exact ⟨Witness.linear .conditional case_46_31_17, case_46_31_17_checked⟩

    · exact ⟨Witness.linear .negative case_46_31_18, case_46_31_18_checked⟩

    · exact ⟨Witness.linear .negative case_46_31_19, case_46_31_19_checked⟩

    · exact ⟨Witness.linear .negative case_46_31_20, case_46_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_46_32_1_checked⟩

    · exact ⟨Witness.rising, case_46_32_2_checked⟩

    · exact ⟨Witness.rising, case_46_32_3_checked⟩

    · exact ⟨Witness.rising, case_46_32_4_checked⟩

    · exact ⟨Witness.rising, case_46_32_5_checked⟩

    · exact ⟨Witness.rising, case_46_32_6_checked⟩

    · exact ⟨Witness.rising, case_46_32_7_checked⟩

    · exact ⟨Witness.rising, case_46_32_8_checked⟩

    · exact ⟨Witness.linear .positive case_46_32_9, case_46_32_9_checked⟩

    · exact ⟨Witness.linear .positive case_46_32_10, case_46_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_46_32_11, case_46_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_46_32_12, case_46_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_46_32_13, case_46_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_46_32_14, case_46_32_14_checked⟩

    · exact ⟨Witness.linear .positive case_46_32_15, case_46_32_15_checked⟩

    · exact ⟨Witness.linear .conditional case_46_32_16, case_46_32_16_checked⟩

    · exact ⟨Witness.linear .conditional case_46_32_17, case_46_32_17_checked⟩

    · exact ⟨Witness.linear .conditional case_46_32_18, case_46_32_18_checked⟩

    · exact ⟨Witness.linear .negative case_46_32_19, case_46_32_19_checked⟩

    · exact ⟨Witness.linear .negative case_46_32_20, case_46_32_20_checked⟩

  · have hkHi : k ≤ 21 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_46_33_1_checked⟩

    · exact ⟨Witness.rising, case_46_33_2_checked⟩

    · exact ⟨Witness.rising, case_46_33_3_checked⟩

    · exact ⟨Witness.rising, case_46_33_4_checked⟩

    · exact ⟨Witness.rising, case_46_33_5_checked⟩

    · exact ⟨Witness.rising, case_46_33_6_checked⟩

    · exact ⟨Witness.rising, case_46_33_7_checked⟩

    · exact ⟨Witness.rising, case_46_33_8_checked⟩

    · exact ⟨Witness.linear .positive case_46_33_9, case_46_33_9_checked⟩

    · exact ⟨Witness.linear .positive case_46_33_10, case_46_33_10_checked⟩

    · exact ⟨Witness.linear .positive case_46_33_11, case_46_33_11_checked⟩

    · exact ⟨Witness.linear .positive case_46_33_12, case_46_33_12_checked⟩

    · exact ⟨Witness.linear .positive case_46_33_13, case_46_33_13_checked⟩

    · exact ⟨Witness.linear .positive case_46_33_14, case_46_33_14_checked⟩

    · exact ⟨Witness.linear .positive case_46_33_15, case_46_33_15_checked⟩

    · exact ⟨Witness.linear .conditional case_46_33_16, case_46_33_16_checked⟩

    · exact ⟨Witness.linear .conditional case_46_33_17, case_46_33_17_checked⟩

    · exact ⟨Witness.linear .conditional case_46_33_18, case_46_33_18_checked⟩

    · exact ⟨Witness.linear .negative case_46_33_19, case_46_33_19_checked⟩

    · exact ⟨Witness.linear .conditional case_46_33_20, case_46_33_20_checked⟩

    · exact ⟨Witness.linear .negative case_46_33_21, case_46_33_21_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_46_34_1_checked⟩

    · exact ⟨Witness.rising, case_46_34_2_checked⟩

    · exact ⟨Witness.rising, case_46_34_3_checked⟩

    · exact ⟨Witness.rising, case_46_34_4_checked⟩

    · exact ⟨Witness.rising, case_46_34_5_checked⟩

    · exact ⟨Witness.rising, case_46_34_6_checked⟩

    · exact ⟨Witness.rising, case_46_34_7_checked⟩

    · exact ⟨Witness.rising, case_46_34_8_checked⟩

    · exact ⟨Witness.linear .positive case_46_34_9, case_46_34_9_checked⟩

    · exact ⟨Witness.linear .positive case_46_34_10, case_46_34_10_checked⟩

    · exact ⟨Witness.linear .positive case_46_34_11, case_46_34_11_checked⟩

    · exact ⟨Witness.linear .positive case_46_34_12, case_46_34_12_checked⟩

    · exact ⟨Witness.linear .positive case_46_34_13, case_46_34_13_checked⟩

    · exact ⟨Witness.linear .positive case_46_34_14, case_46_34_14_checked⟩

    · exact ⟨Witness.linear .positive case_46_34_15, case_46_34_15_checked⟩

    · exact ⟨Witness.linear .positive case_46_34_16, case_46_34_16_checked⟩

    · exact ⟨Witness.linear .conditional case_46_34_17, case_46_34_17_checked⟩

    · exact ⟨Witness.linear .conditional case_46_34_18, case_46_34_18_checked⟩

    · exact ⟨Witness.linear .conditional case_46_34_19, case_46_34_19_checked⟩

    · exact ⟨Witness.linear .conditional case_46_34_20, case_46_34_20_checked⟩

    · exact ⟨Witness.linear .negative case_46_34_21, case_46_34_21_checked⟩

    · exact ⟨Witness.linear .negative case_46_34_22, case_46_34_22_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_46_35_1_checked⟩

    · exact ⟨Witness.rising, case_46_35_2_checked⟩

    · exact ⟨Witness.rising, case_46_35_3_checked⟩

    · exact ⟨Witness.rising, case_46_35_4_checked⟩

    · exact ⟨Witness.rising, case_46_35_5_checked⟩

    · exact ⟨Witness.rising, case_46_35_6_checked⟩

    · exact ⟨Witness.rising, case_46_35_7_checked⟩

    · exact ⟨Witness.rising, case_46_35_8_checked⟩

    · exact ⟨Witness.linear .positive case_46_35_9, case_46_35_9_checked⟩

    · exact ⟨Witness.linear .positive case_46_35_10, case_46_35_10_checked⟩

    · exact ⟨Witness.linear .positive case_46_35_11, case_46_35_11_checked⟩

    · exact ⟨Witness.linear .positive case_46_35_12, case_46_35_12_checked⟩

    · exact ⟨Witness.linear .positive case_46_35_13, case_46_35_13_checked⟩

    · exact ⟨Witness.linear .positive case_46_35_14, case_46_35_14_checked⟩

    · exact ⟨Witness.linear .positive case_46_35_15, case_46_35_15_checked⟩

    · exact ⟨Witness.linear .positive case_46_35_16, case_46_35_16_checked⟩

    · exact ⟨Witness.linear .conditional case_46_35_17, case_46_35_17_checked⟩

    · exact ⟨Witness.linear .conditional case_46_35_18, case_46_35_18_checked⟩

    · exact ⟨Witness.linear .conditional case_46_35_19, case_46_35_19_checked⟩

    · exact ⟨Witness.linear .conditional case_46_35_20, case_46_35_20_checked⟩

    · exact ⟨Witness.linear .negative case_46_35_21, case_46_35_21_checked⟩

    · exact ⟨Witness.linear .negative case_46_35_22, case_46_35_22_checked⟩

  · have hkHi : k ≤ 23 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_46_36_1_checked⟩

    · exact ⟨Witness.rising, case_46_36_2_checked⟩

    · exact ⟨Witness.rising, case_46_36_3_checked⟩

    · exact ⟨Witness.rising, case_46_36_4_checked⟩

    · exact ⟨Witness.rising, case_46_36_5_checked⟩

    · exact ⟨Witness.rising, case_46_36_6_checked⟩

    · exact ⟨Witness.rising, case_46_36_7_checked⟩

    · exact ⟨Witness.rising, case_46_36_8_checked⟩

    · exact ⟨Witness.linear .positive case_46_36_9, case_46_36_9_checked⟩

    · exact ⟨Witness.linear .positive case_46_36_10, case_46_36_10_checked⟩

    · exact ⟨Witness.linear .positive case_46_36_11, case_46_36_11_checked⟩

    · exact ⟨Witness.linear .positive case_46_36_12, case_46_36_12_checked⟩

    · exact ⟨Witness.linear .positive case_46_36_13, case_46_36_13_checked⟩

    · exact ⟨Witness.linear .positive case_46_36_14, case_46_36_14_checked⟩

    · exact ⟨Witness.linear .positive case_46_36_15, case_46_36_15_checked⟩

    · exact ⟨Witness.linear .positive case_46_36_16, case_46_36_16_checked⟩

    · exact ⟨Witness.linear .positive case_46_36_17, case_46_36_17_checked⟩

    · exact ⟨Witness.linear .conditional case_46_36_18, case_46_36_18_checked⟩

    · exact ⟨Witness.linear .conditional case_46_36_19, case_46_36_19_checked⟩

    · exact ⟨Witness.linear .conditional case_46_36_20, case_46_36_20_checked⟩

    · exact ⟨Witness.linear .negative case_46_36_21, case_46_36_21_checked⟩

    · exact ⟨Witness.linear .negative case_46_36_22, case_46_36_22_checked⟩

    · exact ⟨Witness.linear .negative case_46_36_23, case_46_36_23_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_46_37_1_checked⟩

    · exact ⟨Witness.rising, case_46_37_2_checked⟩

    · exact ⟨Witness.rising, case_46_37_3_checked⟩

    · exact ⟨Witness.rising, case_46_37_4_checked⟩

    · exact ⟨Witness.rising, case_46_37_5_checked⟩

    · exact ⟨Witness.rising, case_46_37_6_checked⟩

    · exact ⟨Witness.rising, case_46_37_7_checked⟩

    · exact ⟨Witness.rising, case_46_37_8_checked⟩

    · exact ⟨Witness.linear .positive case_46_37_9, case_46_37_9_checked⟩

    · exact ⟨Witness.linear .positive case_46_37_10, case_46_37_10_checked⟩

    · exact ⟨Witness.linear .positive case_46_37_11, case_46_37_11_checked⟩

    · exact ⟨Witness.linear .positive case_46_37_12, case_46_37_12_checked⟩

    · exact ⟨Witness.linear .positive case_46_37_13, case_46_37_13_checked⟩

    · exact ⟨Witness.linear .positive case_46_37_14, case_46_37_14_checked⟩

    · exact ⟨Witness.linear .positive case_46_37_15, case_46_37_15_checked⟩

    · exact ⟨Witness.linear .positive case_46_37_16, case_46_37_16_checked⟩

    · exact ⟨Witness.linear .positive case_46_37_17, case_46_37_17_checked⟩

    · exact ⟨Witness.linear .positive case_46_37_18, case_46_37_18_checked⟩

    · exact ⟨Witness.linear .conditional case_46_37_19, case_46_37_19_checked⟩

    · exact ⟨Witness.linear .conditional case_46_37_20, case_46_37_20_checked⟩

    · exact ⟨Witness.linear .negative case_46_37_21, case_46_37_21_checked⟩

    · exact ⟨Witness.linear .negative case_46_37_22, case_46_37_22_checked⟩

    · exact ⟨Witness.linear .negative case_46_37_23, case_46_37_23_checked⟩

    · exact ⟨Witness.linear .negative case_46_37_24, case_46_37_24_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_46_38_1_checked⟩

    · exact ⟨Witness.rising, case_46_38_2_checked⟩

    · exact ⟨Witness.rising, case_46_38_3_checked⟩

    · exact ⟨Witness.rising, case_46_38_4_checked⟩

    · exact ⟨Witness.rising, case_46_38_5_checked⟩

    · exact ⟨Witness.rising, case_46_38_6_checked⟩

    · exact ⟨Witness.rising, case_46_38_7_checked⟩

    · exact ⟨Witness.rising, case_46_38_8_checked⟩

    · exact ⟨Witness.linear .positive case_46_38_9, case_46_38_9_checked⟩

    · exact ⟨Witness.linear .positive case_46_38_10, case_46_38_10_checked⟩

    · exact ⟨Witness.linear .positive case_46_38_11, case_46_38_11_checked⟩

    · exact ⟨Witness.linear .positive case_46_38_12, case_46_38_12_checked⟩

    · exact ⟨Witness.linear .positive case_46_38_13, case_46_38_13_checked⟩

    · exact ⟨Witness.linear .positive case_46_38_14, case_46_38_14_checked⟩

    · exact ⟨Witness.linear .positive case_46_38_15, case_46_38_15_checked⟩

    · exact ⟨Witness.linear .positive case_46_38_16, case_46_38_16_checked⟩

    · exact ⟨Witness.linear .positive case_46_38_17, case_46_38_17_checked⟩

    · exact ⟨Witness.linear .positive case_46_38_18, case_46_38_18_checked⟩

    · exact ⟨Witness.linear .conditional case_46_38_19, case_46_38_19_checked⟩

    · exact ⟨Witness.linear .conditional case_46_38_20, case_46_38_20_checked⟩

    · exact ⟨Witness.linear .negative case_46_38_21, case_46_38_21_checked⟩

    · exact ⟨Witness.linear .negative case_46_38_22, case_46_38_22_checked⟩

    · exact ⟨Witness.linear .negative case_46_38_23, case_46_38_23_checked⟩

    · exact ⟨Witness.linear .negative case_46_38_24, case_46_38_24_checked⟩

  · have hkHi : k ≤ 25 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_46_39_1_checked⟩

    · exact ⟨Witness.rising, case_46_39_2_checked⟩

    · exact ⟨Witness.rising, case_46_39_3_checked⟩

    · exact ⟨Witness.rising, case_46_39_4_checked⟩

    · exact ⟨Witness.rising, case_46_39_5_checked⟩

    · exact ⟨Witness.rising, case_46_39_6_checked⟩

    · exact ⟨Witness.rising, case_46_39_7_checked⟩

    · exact ⟨Witness.rising, case_46_39_8_checked⟩

    · exact ⟨Witness.linear .positive case_46_39_9, case_46_39_9_checked⟩

    · exact ⟨Witness.linear .positive case_46_39_10, case_46_39_10_checked⟩

    · exact ⟨Witness.linear .positive case_46_39_11, case_46_39_11_checked⟩

    · exact ⟨Witness.linear .positive case_46_39_12, case_46_39_12_checked⟩

    · exact ⟨Witness.linear .positive case_46_39_13, case_46_39_13_checked⟩

    · exact ⟨Witness.linear .positive case_46_39_14, case_46_39_14_checked⟩

    · exact ⟨Witness.linear .positive case_46_39_15, case_46_39_15_checked⟩

    · exact ⟨Witness.linear .positive case_46_39_16, case_46_39_16_checked⟩

    · exact ⟨Witness.linear .positive case_46_39_17, case_46_39_17_checked⟩

    · exact ⟨Witness.linear .positive case_46_39_18, case_46_39_18_checked⟩

    · exact ⟨Witness.linear .positive case_46_39_19, case_46_39_19_checked⟩

    · exact ⟨Witness.linear .conditional case_46_39_20, case_46_39_20_checked⟩

    · exact ⟨Witness.linear .negative case_46_39_21, case_46_39_21_checked⟩

    · exact ⟨Witness.linear .negative case_46_39_22, case_46_39_22_checked⟩

    · exact ⟨Witness.linear .negative case_46_39_23, case_46_39_23_checked⟩

    · exact ⟨Witness.linear .negative case_46_39_24, case_46_39_24_checked⟩

    · exact ⟨Witness.linear .negative case_46_39_25, case_46_39_25_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_46_40_1_checked⟩

    · exact ⟨Witness.rising, case_46_40_2_checked⟩

    · exact ⟨Witness.rising, case_46_40_3_checked⟩

    · exact ⟨Witness.rising, case_46_40_4_checked⟩

    · exact ⟨Witness.rising, case_46_40_5_checked⟩

    · exact ⟨Witness.rising, case_46_40_6_checked⟩

    · exact ⟨Witness.rising, case_46_40_7_checked⟩

    · exact ⟨Witness.rising, case_46_40_8_checked⟩

    · exact ⟨Witness.linear .positive case_46_40_9, case_46_40_9_checked⟩

    · exact ⟨Witness.linear .positive case_46_40_10, case_46_40_10_checked⟩

    · exact ⟨Witness.linear .positive case_46_40_11, case_46_40_11_checked⟩

    · exact ⟨Witness.linear .positive case_46_40_12, case_46_40_12_checked⟩

    · exact ⟨Witness.linear .positive case_46_40_13, case_46_40_13_checked⟩

    · exact ⟨Witness.linear .positive case_46_40_14, case_46_40_14_checked⟩

    · exact ⟨Witness.linear .positive case_46_40_15, case_46_40_15_checked⟩

    · exact ⟨Witness.linear .positive case_46_40_16, case_46_40_16_checked⟩

    · exact ⟨Witness.linear .positive case_46_40_17, case_46_40_17_checked⟩

    · exact ⟨Witness.linear .positive case_46_40_18, case_46_40_18_checked⟩

    · exact ⟨Witness.linear .positive case_46_40_19, case_46_40_19_checked⟩

    · exact ⟨Witness.linear .positive case_46_40_20, case_46_40_20_checked⟩

    · exact ⟨Witness.linear .negative case_46_40_21, case_46_40_21_checked⟩

    · exact ⟨Witness.linear .negative case_46_40_22, case_46_40_22_checked⟩

    · exact ⟨Witness.linear .negative case_46_40_23, case_46_40_23_checked⟩

    · exact ⟨Witness.linear .negative case_46_40_24, case_46_40_24_checked⟩

    · exact ⟨Witness.linear .negative case_46_40_25, case_46_40_25_checked⟩

    · exact ⟨Witness.linear .negative case_46_40_26, case_46_40_26_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_46_41_1_checked⟩

    · exact ⟨Witness.rising, case_46_41_2_checked⟩

    · exact ⟨Witness.rising, case_46_41_3_checked⟩

    · exact ⟨Witness.rising, case_46_41_4_checked⟩

    · exact ⟨Witness.rising, case_46_41_5_checked⟩

    · exact ⟨Witness.rising, case_46_41_6_checked⟩

    · exact ⟨Witness.rising, case_46_41_7_checked⟩

    · exact ⟨Witness.rising, case_46_41_8_checked⟩

    · exact ⟨Witness.linear .positive case_46_41_9, case_46_41_9_checked⟩

    · exact ⟨Witness.linear .positive case_46_41_10, case_46_41_10_checked⟩

    · exact ⟨Witness.linear .positive case_46_41_11, case_46_41_11_checked⟩

    · exact ⟨Witness.linear .positive case_46_41_12, case_46_41_12_checked⟩

    · exact ⟨Witness.linear .positive case_46_41_13, case_46_41_13_checked⟩

    · exact ⟨Witness.linear .positive case_46_41_14, case_46_41_14_checked⟩

    · exact ⟨Witness.linear .positive case_46_41_15, case_46_41_15_checked⟩

    · exact ⟨Witness.linear .positive case_46_41_16, case_46_41_16_checked⟩

    · exact ⟨Witness.linear .positive case_46_41_17, case_46_41_17_checked⟩

    · exact ⟨Witness.linear .positive case_46_41_18, case_46_41_18_checked⟩

    · exact ⟨Witness.linear .positive case_46_41_19, case_46_41_19_checked⟩

    · exact ⟨Witness.linear .positive case_46_41_20, case_46_41_20_checked⟩

    · exact ⟨Witness.linear .conditional case_46_41_21, case_46_41_21_checked⟩

    · exact ⟨Witness.linear .negative case_46_41_22, case_46_41_22_checked⟩

    · exact ⟨Witness.linear .negative case_46_41_23, case_46_41_23_checked⟩

    · exact ⟨Witness.linear .negative case_46_41_24, case_46_41_24_checked⟩

    · exact ⟨Witness.linear .negative case_46_41_25, case_46_41_25_checked⟩

    · exact ⟨Witness.linear .negative case_46_41_26, case_46_41_26_checked⟩

  · have hkHi : k ≤ 27 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_46_42_1_checked⟩

    · exact ⟨Witness.rising, case_46_42_2_checked⟩

    · exact ⟨Witness.rising, case_46_42_3_checked⟩

    · exact ⟨Witness.rising, case_46_42_4_checked⟩

    · exact ⟨Witness.rising, case_46_42_5_checked⟩

    · exact ⟨Witness.rising, case_46_42_6_checked⟩

    · exact ⟨Witness.rising, case_46_42_7_checked⟩

    · exact ⟨Witness.rising, case_46_42_8_checked⟩

    · exact ⟨Witness.linear .positive case_46_42_9, case_46_42_9_checked⟩

    · exact ⟨Witness.linear .positive case_46_42_10, case_46_42_10_checked⟩

    · exact ⟨Witness.linear .positive case_46_42_11, case_46_42_11_checked⟩

    · exact ⟨Witness.linear .positive case_46_42_12, case_46_42_12_checked⟩

    · exact ⟨Witness.linear .positive case_46_42_13, case_46_42_13_checked⟩

    · exact ⟨Witness.linear .positive case_46_42_14, case_46_42_14_checked⟩

    · exact ⟨Witness.linear .positive case_46_42_15, case_46_42_15_checked⟩

    · exact ⟨Witness.linear .positive case_46_42_16, case_46_42_16_checked⟩

    · exact ⟨Witness.linear .positive case_46_42_17, case_46_42_17_checked⟩

    · exact ⟨Witness.linear .positive case_46_42_18, case_46_42_18_checked⟩

    · exact ⟨Witness.linear .positive case_46_42_19, case_46_42_19_checked⟩

    · exact ⟨Witness.linear .positive case_46_42_20, case_46_42_20_checked⟩

    · exact ⟨Witness.linear .positive case_46_42_21, case_46_42_21_checked⟩

    · exact ⟨Witness.linear .negative case_46_42_22, case_46_42_22_checked⟩

    · exact ⟨Witness.linear .negative case_46_42_23, case_46_42_23_checked⟩

    · exact ⟨Witness.linear .negative case_46_42_24, case_46_42_24_checked⟩

    · exact ⟨Witness.linear .negative case_46_42_25, case_46_42_25_checked⟩

    · exact ⟨Witness.linear .negative case_46_42_26, case_46_42_26_checked⟩

    · exact ⟨Witness.linear .negative case_46_42_27, case_46_42_27_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_46_43_1_checked⟩

    · exact ⟨Witness.rising, case_46_43_2_checked⟩

    · exact ⟨Witness.rising, case_46_43_3_checked⟩

    · exact ⟨Witness.rising, case_46_43_4_checked⟩

    · exact ⟨Witness.rising, case_46_43_5_checked⟩

    · exact ⟨Witness.rising, case_46_43_6_checked⟩

    · exact ⟨Witness.rising, case_46_43_7_checked⟩

    · exact ⟨Witness.rising, case_46_43_8_checked⟩

    · exact ⟨Witness.linear .positive case_46_43_9, case_46_43_9_checked⟩

    · exact ⟨Witness.linear .positive case_46_43_10, case_46_43_10_checked⟩

    · exact ⟨Witness.linear .positive case_46_43_11, case_46_43_11_checked⟩

    · exact ⟨Witness.linear .positive case_46_43_12, case_46_43_12_checked⟩

    · exact ⟨Witness.linear .positive case_46_43_13, case_46_43_13_checked⟩

    · exact ⟨Witness.linear .positive case_46_43_14, case_46_43_14_checked⟩

    · exact ⟨Witness.linear .positive case_46_43_15, case_46_43_15_checked⟩

    · exact ⟨Witness.linear .positive case_46_43_16, case_46_43_16_checked⟩

    · exact ⟨Witness.linear .positive case_46_43_17, case_46_43_17_checked⟩

    · exact ⟨Witness.linear .positive case_46_43_18, case_46_43_18_checked⟩

    · exact ⟨Witness.linear .positive case_46_43_19, case_46_43_19_checked⟩

    · exact ⟨Witness.linear .positive case_46_43_20, case_46_43_20_checked⟩

    · exact ⟨Witness.linear .positive case_46_43_21, case_46_43_21_checked⟩

    · exact ⟨Witness.linear .negative case_46_43_22, case_46_43_22_checked⟩

    · exact ⟨Witness.linear .negative case_46_43_23, case_46_43_23_checked⟩

    · exact ⟨Witness.linear .negative case_46_43_24, case_46_43_24_checked⟩

    · exact ⟨Witness.linear .negative case_46_43_25, case_46_43_25_checked⟩

    · exact ⟨Witness.linear .negative case_46_43_26, case_46_43_26_checked⟩

    · exact ⟨Witness.linear .negative case_46_43_27, case_46_43_27_checked⟩

    · exact ⟨Witness.linear .negative case_46_43_28, case_46_43_28_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_46_44_1_checked⟩

    · exact ⟨Witness.rising, case_46_44_2_checked⟩

    · exact ⟨Witness.rising, case_46_44_3_checked⟩

    · exact ⟨Witness.rising, case_46_44_4_checked⟩

    · exact ⟨Witness.rising, case_46_44_5_checked⟩

    · exact ⟨Witness.rising, case_46_44_6_checked⟩

    · exact ⟨Witness.rising, case_46_44_7_checked⟩

    · exact ⟨Witness.rising, case_46_44_8_checked⟩

    · exact ⟨Witness.linear .positive case_46_44_9, case_46_44_9_checked⟩

    · exact ⟨Witness.linear .positive case_46_44_10, case_46_44_10_checked⟩

    · exact ⟨Witness.linear .positive case_46_44_11, case_46_44_11_checked⟩

    · exact ⟨Witness.linear .positive case_46_44_12, case_46_44_12_checked⟩

    · exact ⟨Witness.linear .positive case_46_44_13, case_46_44_13_checked⟩

    · exact ⟨Witness.linear .positive case_46_44_14, case_46_44_14_checked⟩

    · exact ⟨Witness.linear .positive case_46_44_15, case_46_44_15_checked⟩

    · exact ⟨Witness.linear .positive case_46_44_16, case_46_44_16_checked⟩

    · exact ⟨Witness.linear .positive case_46_44_17, case_46_44_17_checked⟩

    · exact ⟨Witness.linear .positive case_46_44_18, case_46_44_18_checked⟩

    · exact ⟨Witness.linear .positive case_46_44_19, case_46_44_19_checked⟩

    · exact ⟨Witness.linear .positive case_46_44_20, case_46_44_20_checked⟩

    · exact ⟨Witness.linear .positive case_46_44_21, case_46_44_21_checked⟩

    · exact ⟨Witness.linear .positive case_46_44_22, case_46_44_22_checked⟩

    · exact ⟨Witness.linear .negative case_46_44_23, case_46_44_23_checked⟩

    · exact ⟨Witness.linear .negative case_46_44_24, case_46_44_24_checked⟩

    · exact ⟨Witness.linear .negative case_46_44_25, case_46_44_25_checked⟩

    · exact ⟨Witness.linear .negative case_46_44_26, case_46_44_26_checked⟩

    · exact ⟨Witness.linear .negative case_46_44_27, case_46_44_27_checked⟩

    · exact ⟨Witness.linear .negative case_46_44_28, case_46_44_28_checked⟩

  · have hkHi : k ≤ 29 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_46_45_1_checked⟩

    · exact ⟨Witness.rising, case_46_45_2_checked⟩

    · exact ⟨Witness.rising, case_46_45_3_checked⟩

    · exact ⟨Witness.rising, case_46_45_4_checked⟩

    · exact ⟨Witness.rising, case_46_45_5_checked⟩

    · exact ⟨Witness.rising, case_46_45_6_checked⟩

    · exact ⟨Witness.rising, case_46_45_7_checked⟩

    · exact ⟨Witness.rising, case_46_45_8_checked⟩

    · exact ⟨Witness.linear .positive case_46_45_9, case_46_45_9_checked⟩

    · exact ⟨Witness.linear .positive case_46_45_10, case_46_45_10_checked⟩

    · exact ⟨Witness.linear .positive case_46_45_11, case_46_45_11_checked⟩

    · exact ⟨Witness.linear .positive case_46_45_12, case_46_45_12_checked⟩

    · exact ⟨Witness.linear .positive case_46_45_13, case_46_45_13_checked⟩

    · exact ⟨Witness.linear .positive case_46_45_14, case_46_45_14_checked⟩

    · exact ⟨Witness.linear .positive case_46_45_15, case_46_45_15_checked⟩

    · exact ⟨Witness.linear .positive case_46_45_16, case_46_45_16_checked⟩

    · exact ⟨Witness.linear .positive case_46_45_17, case_46_45_17_checked⟩

    · exact ⟨Witness.linear .positive case_46_45_18, case_46_45_18_checked⟩

    · exact ⟨Witness.linear .positive case_46_45_19, case_46_45_19_checked⟩

    · exact ⟨Witness.linear .positive case_46_45_20, case_46_45_20_checked⟩

    · exact ⟨Witness.linear .positive case_46_45_21, case_46_45_21_checked⟩

    · exact ⟨Witness.linear .positive case_46_45_22, case_46_45_22_checked⟩

    · exact ⟨Witness.linear .negative case_46_45_23, case_46_45_23_checked⟩

    · exact ⟨Witness.linear .negative case_46_45_24, case_46_45_24_checked⟩

    · exact ⟨Witness.linear .negative case_46_45_25, case_46_45_25_checked⟩

    · exact ⟨Witness.linear .negative case_46_45_26, case_46_45_26_checked⟩

    · exact ⟨Witness.linear .negative case_46_45_27, case_46_45_27_checked⟩

    · exact ⟨Witness.linear .negative case_46_45_28, case_46_45_28_checked⟩

    · exact ⟨Witness.linear .negative case_46_45_29, case_46_45_29_checked⟩


#print axioms coverage_46
end ForestUnimodality.FiniteRows.FiniteData
