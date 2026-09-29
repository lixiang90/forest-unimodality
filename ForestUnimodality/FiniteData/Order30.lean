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

theorem case_30_15_1_checked :
    (Witness.rising).check 30 15 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_15_2_checked :
    (Witness.rising).check 30 15 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_15_3_checked :
    (Witness.rising).check 30 15 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_15_4_checked :
    (Witness.rising).check 30 15 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_15_5_checked :
    (Witness.rising).check 30 15 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_15_6_checked :
    (Witness.rising).check 30 15 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_15_7_checked :
    (Witness.rising).check 30 15 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_15_8 : Certificate := {
  objectiveScale := 336000
  eta := 0
  rows := #[⟨.count 2, 27459432⟩, ⟨.count 3, 10095624⟩, ⟨.count 4, 2422728⟩, ⟨.count 5, 786240⟩, ⟨.count 6, 335664⟩, ⟨.count 7, 336336⟩, ⟨.path 9, 115296⟩, ⟨.privateRow 7 2, 888⟩, ⟨.privateRow 9 0, 16464⟩, ⟨.privateRow 10 0, 21966⟩, ⟨.hall 7 1, 16821⟩, ⟨.hall 7 2, 2002⟩, ⟨.hall 0 3, 487872⟩, ⟨.hall 1 3, 44352⟩, ⟨.hall 6 3, 4542⟩, ⟨.hall 0 4, 208152⟩, ⟨.hall 5 5, 3468⟩, ⟨.hall 4 8, 11536⟩, ⟨.hall 3 11, 279972⟩, ⟨.hall 1 13, 432432⟩]
  caps := #[0, 0, 10296, 5544, 0, 1056, 504, 0, 0, 552, 0, 0, 0, 0, 0, 0] }

theorem case_30_15_8_checked :
    (Witness.linear .positive case_30_15_8).check 30 15 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_15_9 : Certificate := {
  objectiveScale := 1800000
  eta := 0
  rows := #[⟨.count 2, 305945640⟩, ⟨.count 3, 79085160⟩, ⟨.count 4, 24365880⟩, ⟨.count 5, 8933400⟩, ⟨.count 6, 4029480⟩, ⟨.count 7, 2598960⟩, ⟨.count 8, 2598960⟩, ⟨.path 9, 628380⟩, ⟨.privateRow 10 0, 300090⟩, ⟨.hall 8 1, 260400⟩, ⟨.hall 7 2, 58450⟩, ⟨.hall 8 2, 27944⟩, ⟨.hall 0 3, 2356200⟩, ⟨.hall 7 3, 55209⟩, ⟨.hall 6 4, 78972⟩, ⟨.hall 0 5, 171360⟩, ⟨.hall 5 6, 51375⟩, ⟨.hall 5 8, 434840⟩, ⟨.hall 4 9, 940464⟩, ⟨.hall 3 11, 6590430⟩, ⟨.assumptionRow 9, 2598680⟩]
  caps := #[0, 0, 157080, 19200, 11620, 12600, 0, 3920, 680, 0, 0, 0, 0, 0, 0, 0] }

theorem case_30_15_9_checked :
    (Witness.linear .conditional case_30_15_9).check 30 15 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_16_1_checked :
    (Witness.rising).check 30 16 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_16_2_checked :
    (Witness.rising).check 30 16 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_16_3_checked :
    (Witness.rising).check 30 16 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_16_4_checked :
    (Witness.rising).check 30 16 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_16_5_checked :
    (Witness.rising).check 30 16 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_16_6_checked :
    (Witness.rising).check 30 16 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_16_7_checked :
    (Witness.rising).check 30 16 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_16_8 : Certificate := {
  objectiveScale := 1572480000
  eta := 1196560965600
  rows := #[⟨.count 2, 244497052800⟩, ⟨.count 3, 48281032800⟩, ⟨.count 4, 11891880000⟩, ⟨.count 5, 3805401600⟩, ⟨.count 6, 1614412800⟩, ⟨.count 7, 1576575000⟩, ⟨.path 8, 45252480⟩, ⟨.path 9, 490253400⟩, ⟨.privateRow 5 7, 320864544⟩, ⟨.privateRow 6 4, 101244000⟩, ⟨.privateRow 6 5, 213012800⟩, ⟨.privateRow 6 6, 205645440⟩, ⟨.privateRow 7 2, 149324175⟩, ⟨.privateRow 7 3, 37323000⟩, ⟨.privateRow 8 0, 82082000⟩, ⟨.privateRow 9 0, 61261200⟩, ⟨.hall 4 8, 16401840⟩, ⟨.hall 5 10, 60933600⟩, ⟨.hall 3 11, 309493800⟩]
  caps := #[0, 772972200, 0, 56216160, 19958400, 13920192, 6229600, 47970, 7280, 163800, 0, 0, 0, 0, 0] }

theorem case_30_16_8_checked :
    (Witness.linear .positive case_30_16_8).check 30 16 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_16_9 : Certificate := {
  objectiveScale := 80080000
  eta := 91674502920
  rows := #[⟨.count 2, 20620519920⟩, ⟨.count 3, 5369183820⟩, ⟨.count 4, 1500539040⟩, ⟨.count 5, 536215680⟩, ⟨.count 6, 230630400⟩, ⟨.count 7, 139369230⟩, ⟨.count 8, 131171040⟩, ⟨.path 9, 32031090⟩, ⟨.privateRow 3 13, 398377980⟩, ⟨.privateRow 6 5, 8428420⟩, ⟨.privateRow 6 6, 38606568⟩, ⟨.privateRow 7 3, 9060480⟩, ⟨.privateRow 7 4, 27027000⟩, ⟨.privateRow 7 5, 36504468⟩, ⟨.privateRow 8 1, 8153145⟩, ⟨.privateRow 8 2, 17696250⟩, ⟨.privateRow 9 0, 12087075⟩, ⟨.privateRow 10 0, 11428560⟩, ⟨.hall 5 6, 849888⟩, ⟨.hall 5 7, 1864044⟩, ⟨.hall 4 9, 15416856⟩, ⟨.hall 3 11, 67654125⟩, ⟨.assumptionRow 9, 139282416⟩]
  caps := #[0, 0, 0, 6552, 947674, 125398, 0, 0, 34853, 0, 80080, 0, 0, 0, 0] }

theorem case_30_16_9_checked :
    (Witness.linear .conditional case_30_16_9).check 30 16 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_16_10 : Certificate := {
  objectiveScale := 2108383200000
  eta := 1147625023184640
  rows := #[⟨.count 2, 311508557680320⟩, ⟨.count 3, 89002445051520⟩, ⟨.count 4, 27562471896960⟩, ⟨.count 5, 9587661763680⟩, ⟨.count 6, 3837257424000⟩, ⟨.count 7, 2570962474080⟩, ⟨.count 9, 953832559680⟩, ⟨.count 11, 2080341703440⟩, ⟨.path 7, 764891127000⟩, ⟨.privateRow 2 14, 12843848777760⟩, ⟨.privateRow 6 6, 1064564845344⟩, ⟨.privateRow 7 4, 454760686380⟩, ⟨.privateRow 7 5, 1432667468232⟩, ⟨.privateRow 8 1, 120085600635⟩, ⟨.privateRow 8 2, 19577844000⟩, ⟨.privateRow 8 3, 876859003020⟩, ⟨.privateRow 8 4, 535297410648⟩, ⟨.privateRow 9 1, 514244702400⟩, ⟨.privateRow 10 0, 156935997504⟩, ⟨.hall 6 7, 53142969880⟩, ⟨.hall 5 8, 459374531616⟩, ⟨.hall 6 8, 516750666432⟩, ⟨.hall 4 9, 657965061936⟩, ⟨.hall 3 11, 3537392623380⟩, ⟨.hall 2 13, 35068617286560⟩, ⟨.assumptionRow 10, 961019803744⟩]
  caps := #[0, 900254515160, 0, 25715341080, 14474504352, 0, 962050320, 162092007, 334998664, 7187244064, 7800348512, 28041496560, 0, 0, 0] }

theorem case_30_16_10_checked :
    (Witness.linear .conditional case_30_16_10).check 30 16 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_17_1_checked :
    (Witness.rising).check 30 17 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_17_2_checked :
    (Witness.rising).check 30 17 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_17_3_checked :
    (Witness.rising).check 30 17 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_17_4_checked :
    (Witness.rising).check 30 17 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_17_5_checked :
    (Witness.rising).check 30 17 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_17_6_checked :
    (Witness.rising).check 30 17 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_17_7 : Certificate := {
  objectiveScale := 45936000000
  eta := 38238577977600
  rows := #[⟨.count 2, 6265805145600⟩, ⟨.count 3, 965620656000⟩, ⟨.count 4, 197805928320⟩, ⟨.count 5, 62423961600⟩, ⟨.count 6, 45842596800⟩, ⟨.path 7, 16703812125⟩, ⟨.path 8, 6264417600⟩, ⟨.privateRow 5 8, 14097411328⟩, ⟨.privateRow 6 6, 3413810400⟩, ⟨.privateRow 7 3, 931830900⟩, ⟨.privateRow 8 0, 625865240⟩, ⟨.hall 6 2, 78536640⟩, ⟨.hall 4 8, 21462784⟩, ⟨.hall 3 10, 241164000⟩]
  caps := #[0, 0, 5984753775, 647972325, 735353388, 215850525, 93403200, 152500605, 5765200, 0, 0, 0, 0, 0] }

theorem case_30_17_7_checked :
    (Witness.linear .positive case_30_17_7).check 30 17 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_17_8 : Certificate := {
  objectiveScale := 151200000
  eta := 201924122400
  rows := #[⟨.count 2, 38945907000⟩, ⟨.count 3, 8043235200⟩, ⟨.count 4, 1835673840⟩, ⟨.count 5, 504504000⟩, ⟨.count 6, 191891700⟩, ⟨.count 7, 151351200⟩, ⟨.path 8, 40321800⟩, ⟨.path 9, 20160000⟩, ⟨.privateRow 3 14, 918918000⟩, ⟨.privateRow 7 10, 457528500⟩, ⟨.privateRow 8 0, 5180175⟩, ⟨.privateRow 9 0, 2242240⟩, ⟨.hall 6 4, 1237860⟩, ⟨.hall 8 4, 2779920⟩, ⟨.hall 9 4, 6764472⟩, ⟨.hall 7 5, 1720290⟩, ⟨.hall 5 6, 136500⟩, ⟨.hall 5 10, 66448200⟩, ⟨.hall 4 11, 76424040⟩]
  caps := #[0, 0, 0, 1058400, 0, 3168000, 0, 0, 567155, 0, 0, 0, 0, 0] }

theorem case_30_17_8_checked :
    (Witness.linear .positive case_30_17_8).check 30 17 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_17_9 : Certificate := {
  objectiveScale := 1456000000
  eta := 3180840062400
  rows := #[⟨.count 2, 647156109600⟩, ⟨.count 3, 150226876800⟩, ⟨.count 4, 42655092480⟩, ⟨.count 5, 12972960000⟩, ⟨.count 6, 5254048800⟩, ⟨.count 7, 2983780800⟩, ⟨.count 8, 2681078400⟩, ⟨.path 9, 741303360⟩, ⟨.privateRow 4 11, 5247562320⟩, ⟨.privateRow 5 8, 1153728576⟩, ⟨.privateRow 5 9, 2430267840⟩, ⟨.privateRow 5 10, 3992788800⟩, ⟨.privateRow 6 6, 1071170100⟩, ⟨.privateRow 6 7, 1498376880⟩, ⟨.privateRow 6 8, 1282431150⟩, ⟨.privateRow 7 3, 98455500⟩, ⟨.privateRow 7 4, 690346800⟩, ⟨.privateRow 7 5, 655597800⟩, ⟨.privateRow 8 1, 151951800⟩, ⟨.privateRow 8 2, 315540225⟩, ⟨.privateRow 9 0, 188348160⟩, ⟨.privateRow 10 0, 182432250⟩, ⟨.hall 4 12, 1802243520⟩, ⟨.hall 3 13, 12009254400⟩, ⟨.hall 2 14, 10369719360⟩, ⟨.assumptionRow 9, 2991990960⟩]
  caps := #[0, 0, 296456160, 78244320, 0, 4289824, 25721850, 8313320, 7008960, 29728720, 0, 0, 0, 0] }

theorem case_30_17_9_checked :
    (Witness.linear .conditional case_30_17_9).check 30 17 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_17_10 : Certificate := {
  objectiveScale := 332514000000
  eta := 353996532489600
  rows := #[⟨.count 2, 85747114252800⟩, ⟨.count 3, 24544321401600⟩, ⟨.count 4, 7437034725120⟩, ⟨.count 5, 2446238995200⟩, ⟨.count 6, 895393699200⟩, ⟨.count 7, 364302338400⟩, ⟨.count 8, 193124131200⟩, ⟨.count 9, 221214913920⟩, ⟨.count 11, 289686196800⟩, ⟨.path 7, 140004589725⟩, ⟨.privateRow 2 15, 4586698116000⟩, ⟨.privateRow 4 10, 375275300400⟩, ⟨.privateRow 4 11, 1703881539360⟩, ⟨.privateRow 5 8, 293548679424⟩, ⟨.privateRow 5 9, 823411068480⟩, ⟨.privateRow 5 10, 1469303996160⟩, ⟨.privateRow 6 6, 166301335200⟩, ⟨.privateRow 6 7, 342356414400⟩, ⟨.privateRow 6 8, 979519741200⟩, ⟨.privateRow 6 9, 325287362400⟩, ⟨.privateRow 7 4, 82498759200⟩, ⟨.privateRow 7 5, 253736683200⟩, ⟨.privateRow 7 6, 403930406880⟩, ⟨.privateRow 8 2, 32004472500⟩, ⟨.privateRow 8 3, 161354793600⟩, ⟨.privateRow 8 4, 86686399800⟩, ⟨.privateRow 9 1, 88515226800⟩, ⟨.privateRow 10 0, 25018353360⟩, ⟨.hall 4 12, 1947987740160⟩, ⟨.hall 3 13, 6124793875200⟩, ⟨.hall 2 14, 9694831386240⟩, ⟨.assumptionRow 10, 223153840000⟩]
  caps := #[0, 143402284025, 27421368975, 8847844005, 6129873750, 0, 1572179700, 3301615005, 0, 2600998400, 0, 42827803200, 0, 0] }

theorem case_30_17_10_checked :
    (Witness.linear .conditional case_30_17_10).check 30 17 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_18_1_checked :
    (Witness.rising).check 30 18 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_18_2_checked :
    (Witness.rising).check 30 18 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_18_3_checked :
    (Witness.rising).check 30 18 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_18_4_checked :
    (Witness.rising).check 30 18 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_18_5_checked :
    (Witness.rising).check 30 18 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_18_6_checked :
    (Witness.rising).check 30 18 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_18_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_30_18_7_checked :
    (Witness.linear .positive case_30_18_7).check 30 18 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_18_8 : Certificate := {
  objectiveScale := 19800000
  eta := 32702670000
  rows := #[⟨.count 2, 6605398800⟩, ⟨.count 3, 1452971520⟩, ⟨.count 4, 338738400⟩, ⟨.count 5, 88288200⟩, ⟨.count 6, 28571400⟩, ⟨.count 7, 19819800⟩, ⟨.path 8, 8799840⟩, ⟨.hall 8 2, 88088⟩, ⟨.hall 8 3, 33033⟩, ⟨.hall 7 7, 91455⟩]
  caps := #[0, 13899600, 926640, 0, 50400, 0, 28440, 0, 411968, 0, 0, 0, 0] }

theorem case_30_18_8_checked :
    (Witness.linear .positive case_30_18_8).check 30 18 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_18_9 : Certificate := {
  objectiveScale := 80000
  eta := 190600410
  rows := #[⟨.count 2, 45765720⟩, ⟨.count 3, 12324312⟩, ⟨.count 4, 3363360⟩, ⟨.count 5, 930930⟩, ⟨.count 6, 321750⟩, ⟨.count 7, 135135⟩, ⟨.count 8, 104104⟩, ⟨.path 8, 26664⟩]
  caps := #[0, 35750, 0, 0, 0, 2350, 0, 0, 2560, 0, 0, 0, 0] }

theorem case_30_18_9_checked :
    (Witness.linear .positive case_30_18_9).check 30 18 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_18_10 : Certificate := {
  objectiveScale := 5586000000
  eta := 18188630460000
  rows := #[⟨.count 2, 3761380022400⟩, ⟨.count 3, 826468362720⟩, ⟨.count 4, 209348979840⟩, ⟨.count 5, 53918865000⟩, ⟨.count 6, 14583769200⟩, ⟨.count 7, 4313509200⟩, ⟨.count 8, 2683961280⟩, ⟨.path 6, 7135128000⟩, ⟨.privateRow 2 16, 107837730000⟩, ⟨.privateRow 3 13, 35562486960⟩, ⟨.privateRow 3 14, 119915555760⟩, ⟨.privateRow 4 11, 42272390160⟩, ⟨.privateRow 4 12, 58663725120⟩, ⟨.privateRow 4 13, 75534338880⟩, ⟨.privateRow 5 8, 4848703860⟩, ⟨.privateRow 5 9, 21740086368⟩, ⟨.privateRow 5 10, 32387264910⟩, ⟨.privateRow 5 11, 37351794480⟩, ⟨.privateRow 6 6, 4460227200⟩, ⟨.privateRow 6 7, 11571159600⟩, ⟨.privateRow 6 8, 17966108160⟩, ⟨.privateRow 6 9, 7745487750⟩, ⟨.privateRow 7 4, 2837159325⟩, ⟨.privateRow 7 5, 7463055600⟩, ⟨.privateRow 7 6, 5779874100⟩, ⟨.privateRow 8 2, 1384583200⟩, ⟨.privateRow 8 3, 4169725560⟩, ⟨.privateRow 9 0, 287567280⟩, ⟨.privateRow 9 1, 1427185760⟩, ⟨.privateRow 10 0, 415374960⟩, ⟨.hall 3 14, 21740086368⟩, ⟨.hall 2 15, 99390441150⟩, ⟨.assumptionRow 10, 4324904640⟩]
  caps := #[0, 0, 428588160, 147315168, 142270128, 0, 0, 11395440, 103489960, 22046080, 1131723600, 5586000000, 0] }

theorem case_30_18_10_checked :
    (Witness.linear .conditional case_30_18_10).check 30 18 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_18_11 : Certificate := {
  objectiveScale := 52227118440000
  eta := 286030257520807800
  rows := #[⟨.count 2, 52005501367419600⟩, ⟨.count 3, 7393793157550800⟩, ⟨.count 4, 1301174822787840⟩, ⟨.count 5, 134847518305500⟩, ⟨.path 4, 413544416004720⟩, ⟨.path 5, 134346968355600⟩, ⟨.privateRow 2 16, 4941642901595400⟩, ⟨.privateRow 3 6, 53275142616696⟩, ⟨.privateRow 3 13, 1348475183055000⟩, ⟨.privateRow 3 14, 1845958796742060⟩, ⟨.privateRow 4 10, 251770689562392⟩, ⟨.privateRow 4 11, 657226058448960⟩, ⟨.privateRow 4 12, 900919727427720⟩, ⟨.privateRow 4 13, 1116537451569540⟩, ⟨.privateRow 5 7, 22346160176340⟩, ⟨.privateRow 5 8, 154348544029680⟩, ⟨.privateRow 5 9, 296415591007536⟩, ⟨.privateRow 5 10, 419790697371045⟩, ⟨.privateRow 5 11, 649342665071100⟩, ⟨.privateRow 6 5, 17041169895750⟩, ⟨.privateRow 6 6, 77140401366600⟩, ⟨.privateRow 6 7, 153617502538500⟩, ⟨.privateRow 6 8, 231463542410100⟩, ⟨.privateRow 6 9, 196566190145325⟩, ⟨.privateRow 7 3, 8528817397100⟩, ⟨.privateRow 7 4, 40083795276525⟩, ⟨.privateRow 7 5, 90265277559600⟩, ⟨.privateRow 7 6, 133316282749650⟩, ⟨.privateRow 8 1, 5103459923562⟩, ⟨.privateRow 8 2, 21160687487940⟩, ⟨.privateRow 8 3, 60577654377240⟩, ⟨.privateRow 8 4, 18493373939040⟩, ⟨.privateRow 9 0, 23401230869016⟩, ⟨.privateRow 9 1, 13185090678760⟩, ⟨.privateRow 10 0, 13553904404040⟩, ⟨.privateRow 11 0, 4667798710575⟩, ⟨.hall 3 14, 402799910064552⟩, ⟨.hall 2 15, 1789322839053750⟩]
  caps := #[0, 0, 0, 2515966114662, 571253266080, 756051099804, 49394695350, 632360660250, 4054275144234, 0, 21360891441960, 0, 52227118440000] }

theorem case_30_18_11_checked :
    (Witness.linear .negative case_30_18_11).check 30 18 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_19_1_checked :
    (Witness.rising).check 30 19 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_19_2_checked :
    (Witness.rising).check 30 19 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_19_3_checked :
    (Witness.rising).check 30 19 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_19_4_checked :
    (Witness.rising).check 30 19 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_19_5_checked :
    (Witness.rising).check 30 19 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_19_6_checked :
    (Witness.rising).check 30 19 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_19_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_30_19_7_checked :
    (Witness.linear .positive case_30_19_7).check 30 19 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_19_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_30_19_8_checked :
    (Witness.linear .positive case_30_19_8).check 30 19 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_19_9 : Certificate := {
  objectiveScale := 158414000
  eta := 1277517029880
  rows := #[⟨.count 2, 243740215992⟩, ⟨.count 3, 48206013856⟩, ⟨.count 4, 9975646408⟩, ⟨.count 5, 2450664580⟩, ⟨.count 6, 597220780⟩, ⟨.count 7, 144156740⟩, ⟨.count 8, 172988088⟩, ⟨.path 3, 2445603160⟩, ⟨.path 6, 277243725⟩]
  caps := #[0, 460302180, 59590973, 0, 5127692, 4867770, 0, 14257260, 0, 0, 0, 0] }

theorem case_30_19_9_checked :
    (Witness.linear .positive case_30_19_9).check 30 19 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_19_10 : Certificate := {
  objectiveScale := 1816920000
  eta := 7942683949200
  rows := #[⟨.count 2, 1601008128720⟩, ⟨.count 3, 363227744880⟩, ⟨.count 4, 85480635240⟩, ⟨.count 5, 21899077200⟩, ⟨.count 6, 5753147400⟩, ⟨.count 7, 1558917360⟩, ⟨.path 6, 2711691675⟩, ⟨.privateRow 2 17, 148876607880⟩, ⟨.privateRow 3 13, 433032600⟩, ⟨.privateRow 3 14, 54388894560⟩, ⟨.privateRow 3 15, 63742398720⟩, ⟨.privateRow 4 11, 11445051618⟩, ⟨.privateRow 4 12, 30041636625⟩, ⟨.privateRow 4 13, 33430116720⟩, ⟨.privateRow 4 14, 23903399520⟩, ⟨.privateRow 5 8, 901414800⟩, ⟨.privateRow 5 9, 9786536760⟩, ⟨.privateRow 5 10, 15344200872⟩, ⟨.privateRow 5 11, 17417189790⟩, ⟨.privateRow 6 6, 1360959600⟩, ⟨.privateRow 6 7, 6287810100⟩, ⟨.privateRow 6 8, 9634975350⟩, ⟨.privateRow 6 9, 272191920⟩, ⟨.privateRow 7 4, 1253732480⟩, ⟨.privateRow 7 5, 4440130695⟩, ⟨.privateRow 7 6, 784761120⟩, ⟨.privateRow 8 2, 987314328⟩, ⟨.privateRow 8 3, 1154753600⟩, ⟨.privateRow 9 0, 440905920⟩, ⟨.privateRow 9 1, 138570432⟩, ⟨.privateRow 10 0, 155891736⟩, ⟨.hall 2 16, 35855099280⟩, ⟨.assumptionRow 10, 1634319540⟩]
  caps := #[0, 3399095700, 0, 854681520, 0, 0, 52543250, 258561930, 0, 515944716, 0, 1816920000] }

theorem case_30_19_10_checked :
    (Witness.linear .conditional case_30_19_10).check 30 19 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_19_11 : Certificate := {
  objectiveScale := 1023472800000
  eta := 7307439200661600
  rows := #[⟨.count 2, 1305237522869280⟩, ⟨.count 3, 240180954773760⟩, ⟨.count 4, 42877608293520⟩, ⟨.count 5, 6042437200800⟩, ⟨.count 6, 296197902000⟩, ⟨.path 5, 5469491827800⟩, ⟨.privateRow 2 17, 125647150028400⟩, ⟨.privateRow 3 13, 2653933201920⟩, ⟨.privateRow 3 14, 40877943346240⟩, ⟨.privateRow 3 15, 51613471749840⟩, ⟨.privateRow 4 11, 9064840592808⟩, ⟨.privateRow 4 12, 21314401027920⟩, ⟨.privateRow 4 13, 26504775597300⟩, ⟨.privateRow 4 14, 27130246833690⟩, ⟨.privateRow 5 8, 885208587120⟩, ⟨.privateRow 5 9, 6056259769560⟩, ⟨.privateRow 5 10, 10480666564368⟩, ⟨.privateRow 5 11, 14116792009320⟩, ⟨.privateRow 5 12, 7424694076800⟩, ⟨.privateRow 6 6, 824417493900⟩, ⟨.privateRow 6 7, 3438716595600⟩, ⟨.privateRow 6 8, 6152688642100⟩, ⟨.privateRow 6 9, 6105626086560⟩, ⟨.privateRow 7 4, 510776826560⟩, ⟨.privateRow 7 5, 2193345464310⟩, ⟨.privateRow 7 6, 3897964390320⟩, ⟨.privateRow 8 2, 304787641158⟩, ⟨.privateRow 8 3, 1656404489740⟩, ⟨.privateRow 8 4, 533896718355⟩, ⟨.privateRow 9 0, 306609707040⟩, ⟨.privateRow 9 1, 530786640384⟩, ⟨.privateRow 10 0, 273686861448⟩, ⟨.hall 2 16, 32871694695840⟩, ⟨.assumptionRow 11, 314400609432⟩]
  caps := #[0, 617825505024, 0, 98202824720, 23595197472, 0, 27547787696, 23995157340, 5466197646, 0, 213056332776, 6849908990568] }

theorem case_30_19_11_checked :
    (Witness.linear .conditional case_30_19_11).check 30 19 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_19_12 : Certificate := {
  objectiveScale := 375306528100000
  eta := 5158648277778996000
  rows := #[⟨.count 2, 715641693666419520⟩, ⟨.count 3, 97763147136935280⟩, ⟨.count 4, 12816117444170040⟩, ⟨.count 5, 2208089150467200⟩, ⟨.count 6, 230009286507000⟩, ⟨.path 3, 29580809394536400⟩, ⟨.path 5, 887759731158300⟩, ⟨.path 6, 217392272247150⟩, ⟨.privateRow 10 2, 24150975083235⟩, ⟨.hall 8 5, 20073537731520⟩, ⟨.hall 9 5, 22234231029010⟩, ⟨.hall 6 6, 19612446854140⟩, ⟨.hall 7 6, 20909935137000⟩, ⟨.hall 5 9, 39223361844900⟩, ⟨.hall 4 11, 128215433042620⟩, ⟨.hall 3 12, 102566448760083⟩]
  caps := #[0, 59971850229200, 179828385739730, 685155687370, 23459595509350, 0, 0, 0, 79264738734720, 0, 0, 7506130562000000] }

theorem case_30_19_12_checked :
    (Witness.linear .negative case_30_19_12).check 30 19 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_20_1_checked :
    (Witness.rising).check 30 20 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_20_2_checked :
    (Witness.rising).check 30 20 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_20_3_checked :
    (Witness.rising).check 30 20 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_20_4_checked :
    (Witness.rising).check 30 20 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_20_5_checked :
    (Witness.rising).check 30 20 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_20_6_checked :
    (Witness.rising).check 30 20 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_20_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_30_20_7_checked :
    (Witness.linear .positive case_30_20_7).check 30 20 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_20_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_30_20_8_checked :
    (Witness.linear .positive case_30_20_8).check 30 20 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_20_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_30_20_9_checked :
    (Witness.linear .positive case_30_20_9).check 30 20 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_20_10 : Certificate := {
  objectiveScale := 10769119200000
  eta := 127909842840299520
  rows := #[⟨.count 2, 21335554961360640⟩, ⟨.count 3, 3790208733030720⟩, ⟨.count 4, 687448877955840⟩, ⟨.count 5, 117038787465600⟩, ⟨.count 6, 22175770256640⟩, ⟨.count 7, 12935865983040⟩, ⟨.path 5, 75753394516800⟩, ⟨.privateRow 2 18, 1362577883546880⟩, ⟨.privateRow 3 14, 284050057210920⟩, ⟨.privateRow 3 15, 615890952636960⟩, ⟨.privateRow 3 16, 570256092085680⟩, ⟨.privateRow 4 11, 84083128889760⟩, ⟨.privateRow 4 12, 270174800960064⟩, ⟨.privateRow 4 13, 323627647182840⟩, ⟨.privateRow 4 14, 179562139716960⟩, ⟨.privateRow 5 8, 12935865983040⟩, ⟨.privateRow 5 9, 91871048206080⟩, ⟨.privateRow 5 10, 164162299260960⟩, ⟨.privateRow 5 11, 95848606998144⟩, ⟨.privateRow 6 6, 19095802165440⟩, ⟨.privateRow 6 7, 76460207864040⟩, ⟨.privateRow 6 8, 43207552365120⟩, ⟨.privateRow 7 4, 21898573128432⟩, ⟨.privateRow 7 5, 26077063172160⟩, ⟨.privateRow 8 2, 14503849738560⟩, ⟨.privateRow 9 0, 3593296106400⟩, ⟨.hall 2 17, 110194413929600⟩, ⟨.assumptionRow 10, 10595447356725⟩]
  caps := #[0, 23778559284480, 8607494185290, 0, 80422558290, 228037261725, 967100274855, 0, 0, 8557160592750, 86326625443275] }

theorem case_30_20_10_checked :
    (Witness.linear .conditional case_30_20_10).check 30 20 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_20_11 : Certificate := {
  objectiveScale := 12335400000
  eta := 256753870813440
  rows := #[⟨.count 2, 34415608106880⟩, ⟨.count 3, 4337759446020⟩, ⟨.count 4, 431817946560⟩, ⟨.count 5, 15875659800⟩, ⟨.count 6, 6350263920⟩, ⟨.path 3, 311121310500⟩, ⟨.path 4, 402078418560⟩, ⟨.privateRow 2 18, 2346069726000⟩, ⟨.privateRow 3 14, 489279015225⟩, ⟨.privateRow 3 15, 922787425560⟩, ⟨.privateRow 3 16, 955097333190⟩, ⟨.privateRow 4 11, 123741948330⟩, ⟨.privateRow 4 12, 372442978908⟩, ⟨.privateRow 4 13, 474020742195⟩, ⟨.privateRow 4 14, 472036284720⟩, ⟨.privateRow 5 8, 13979400435⟩, ⟨.privateRow 5 9, 105888130920⟩, ⟨.privateRow 5 10, 210499489200⟩, ⟨.privateRow 5 11, 268122254400⟩, ⟨.privateRow 5 12, 39071762730⟩, ⟨.privateRow 6 6, 13053320280⟩, ⟨.privateRow 6 7, 79907487660⟩, ⟨.privateRow 6 8, 139907401920⟩, ⟨.privateRow 6 9, 28164596460⟩, ⟨.privateRow 7 4, 11800907118⟩, ⟨.privateRow 7 5, 69558909420⟩, ⟨.privateRow 7 6, 19579980420⟩, ⟨.privateRow 8 2, 13807013220⟩, ⟨.privateRow 8 3, 22719833136⟩, ⟨.privateRow 9 0, 11524553040⟩, ⟨.privateRow 10 0, 4041077040⟩, ⟨.hall 2 17, 265613508160⟩, ⟨.assumptionRow 11, 5811823710⟩]
  caps := #[0, 0, 0, 84965790, 680000139, 848058750, 1154975250, 687945258, 0, 0, 0] }

theorem case_30_20_11_checked :
    (Witness.linear .conditional case_30_20_11).check 30 20 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_20_12 : Certificate := {
  objectiveScale := 36583331400000
  eta := 805956194207324160
  rows := #[⟨.count 2, 126499833448148160⟩, ⟨.count 3, 19316481879174480⟩, ⟨.count 4, 2632448727548640⟩, ⟨.count 5, 254097367524000⟩, ⟨.path 4, 621929556743040⟩, ⟨.path 5, 256082597971200⟩, ⟨.privateRow 4 13, 3332486975077260⟩, ⟨.privateRow 5 9, 121966736411520⟩, ⟨.privateRow 5 11, 1665862341487344⟩, ⟨.privateRow 5 14, 880870874083200⟩, ⟨.privateRow 6 6, 3011524355840⟩, ⟨.privateRow 6 7, 2117478062700⟩, ⟨.privateRow 7 4, 254097367524⟩, ⟨.hall 8 4, 527016762272⟩, ⟨.hall 6 5, 2865893385960⟩, ⟨.hall 7 5, 2621263441720⟩, ⟨.hall 9 6, 1385985641040⟩, ⟨.hall 5 7, 1865355033696⟩, ⟨.hall 8 7, 3293854764200⟩, ⟨.hall 4 11, 2371575430224⟩, ⟨.hall 3 13, 10675826162001⟩, ⟨.hall 2 15, 105790864779600⟩]
  caps := #[0, 56099522868480, 9348730896960, 0, 2438724916404, 4695602367456, 4480196068348, 0, 0, 0, 636257299708800] }

theorem case_30_20_12_checked :
    (Witness.linear .negative case_30_20_12).check 30 20 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_21_1_checked :
    (Witness.rising).check 30 21 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_21_2_checked :
    (Witness.rising).check 30 21 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_21_3_checked :
    (Witness.rising).check 30 21 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_21_4_checked :
    (Witness.rising).check 30 21 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_21_5_checked :
    (Witness.rising).check 30 21 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_21_6_checked :
    (Witness.rising).check 30 21 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_21_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_30_21_7_checked :
    (Witness.linear .positive case_30_21_7).check 30 21 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_21_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_30_21_8_checked :
    (Witness.linear .positive case_30_21_8).check 30 21 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_21_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_30_21_9_checked :
    (Witness.linear .positive case_30_21_9).check 30 21 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_21_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_30_21_10_checked :
    (Witness.linear .positive case_30_21_10).check 30 21 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_21_11 : Certificate := {
  objectiveScale := 183
  eta := 146692
  rows := #[⟨.assumptionRow 11, 223⟩]
  caps := #[0, 0, 49049, 16665, 6345, 2584, 1092, 41132, 32123, 16140] }

theorem case_30_21_11_checked :
    (Witness.linear .conditional case_30_21_11).check 30 21 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_21_12 : Certificate := {
  objectiveScale := 504
  eta := 129402
  rows := #[⟨.assumptionRow 12, 359⟩]
  caps := #[0, 0, 49179, 21109, 9285, 3652, 2002, 145145, 134277, 83314] }

theorem case_30_21_12_checked :
    (Witness.linear .conditional case_30_21_12).check 30 21 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_21_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 429, 429, 297] }

theorem case_30_21_13_checked :
    (Witness.linear .negative case_30_21_13).check 30 21 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_22_1_checked :
    (Witness.rising).check 30 22 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_22_2_checked :
    (Witness.rising).check 30 22 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_22_3_checked :
    (Witness.rising).check 30 22 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_22_4_checked :
    (Witness.rising).check 30 22 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_22_5_checked :
    (Witness.rising).check 30 22 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_22_6_checked :
    (Witness.rising).check 30 22 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_22_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0, 0] }

theorem case_30_22_7_checked :
    (Witness.linear .positive case_30_22_7).check 30 22 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_22_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0] }

theorem case_30_22_8_checked :
    (Witness.linear .positive case_30_22_8).check 30 22 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_22_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1] }

theorem case_30_22_9_checked :
    (Witness.linear .positive case_30_22_9).check 30 22 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_22_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_30_22_10_checked :
    (Witness.linear .positive case_30_22_10).check 30 22 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_22_11 : Certificate := {
  objectiveScale := 745
  eta := 932984
  rows := #[⟨.assumptionRow 11, 1062⟩]
  caps := #[0, 0, 317317, 110539, 39705, 14836, 5833, 253890, 184639] }

theorem case_30_22_11_checked :
    (Witness.linear .conditional case_30_22_11).check 30 22 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_22_12 : Certificate := {
  objectiveScale := 4
  eta := 1274
  rows := #[⟨.assumptionRow 12, 3⟩]
  caps := #[0, 0, 455, 209, 85, 36, 2808, 3094, 2093] }

theorem case_30_22_12_checked :
    (Witness.linear .conditional case_30_22_12).check 30 22 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_22_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 1430, 1430, 1001] }

theorem case_30_22_13_checked :
    (Witness.linear .negative case_30_22_13).check 30 22 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_22_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 429] }

theorem case_30_22_14_checked :
    (Witness.linear .negative case_30_22_14).check 30 22 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_23_1_checked :
    (Witness.rising).check 30 23 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_23_2_checked :
    (Witness.rising).check 30 23 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_23_3_checked :
    (Witness.rising).check 30 23 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_23_4_checked :
    (Witness.rising).check 30 23 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_23_5_checked :
    (Witness.rising).check 30 23 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_23_6_checked :
    (Witness.rising).check 30 23 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_23_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1, 0] }

theorem case_30_23_7_checked :
    (Witness.linear .positive case_30_23_7).check 30 23 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_23_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1] }

theorem case_30_23_8_checked :
    (Witness.linear .positive case_30_23_8).check 30 23 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_23_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_30_23_9_checked :
    (Witness.linear .positive case_30_23_9).check 30 23 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_23_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_30_23_10_checked :
    (Witness.linear .positive case_30_23_10).check 30 23 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_23_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_30_23_11_checked :
    (Witness.linear .positive case_30_23_11).check 30 23 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_23_12 : Certificate := {
  objectiveScale := 247
  eta := 178724
  rows := #[⟨.assumptionRow 12, 222⟩]
  caps := #[0, 0, 64883, 23012, 9460, 3987, 373048, 333424] }

theorem case_30_23_12_checked :
    (Witness.linear .conditional case_30_23_12).check 30 23 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_23_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 4862, 4862, 3432] }

theorem case_30_23_13_checked :
    (Witness.linear .negative case_30_23_13).check 30 23 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_23_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 1430] }

theorem case_30_23_14_checked :
    (Witness.linear .negative case_30_23_14).check 30 23 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_24_1_checked :
    (Witness.rising).check 30 24 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_24_2_checked :
    (Witness.rising).check 30 24 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_24_3_checked :
    (Witness.rising).check 30 24 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_24_4_checked :
    (Witness.rising).check 30 24 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_24_5_checked :
    (Witness.rising).check 30 24 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_24_6_checked :
    (Witness.rising).check 30 24 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_24_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1, 1] }

theorem case_30_24_7_checked :
    (Witness.linear .positive case_30_24_7).check 30 24 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_24_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1] }

theorem case_30_24_8_checked :
    (Witness.linear .positive case_30_24_8).check 30 24 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_24_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_30_24_9_checked :
    (Witness.linear .positive case_30_24_9).check 30 24 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_24_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_30_24_10_checked :
    (Witness.linear .positive case_30_24_10).check 30 24 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_24_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_30_24_11_checked :
    (Witness.linear .positive case_30_24_11).check 30 24 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_24_12 : Certificate := {
  objectiveScale := 11
  eta := 176358
  rows := #[⟨.assumptionRow 12, 27⟩]
  caps := #[0, 0, 53482, 16588, 5291, 1749, 606] }

theorem case_30_24_12_checked :
    (Witness.linear .conditional case_30_24_12).check 30 24 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_24_13 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 16796, 16796, 11934] }

theorem case_30_24_13_checked :
    (Witness.linear .negative case_30_24_13).check 30 24 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_24_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 4862] }

theorem case_30_24_14_checked :
    (Witness.linear .negative case_30_24_14).check 30 24 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_24_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_30_24_15_checked :
    (Witness.linear .negative case_30_24_15).check 30 24 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_25_1_checked :
    (Witness.rising).check 30 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_25_2_checked :
    (Witness.rising).check 30 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_25_3_checked :
    (Witness.rising).check 30 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_25_4_checked :
    (Witness.rising).check 30 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_25_5_checked :
    (Witness.rising).check 30 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_25_6_checked :
    (Witness.rising).check 30 25 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_25_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2, 1] }

theorem case_30_25_7_checked :
    (Witness.linear .positive case_30_25_7).check 30 25 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_25_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2] }

theorem case_30_25_8_checked :
    (Witness.linear .positive case_30_25_8).check 30 25 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_25_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_30_25_9_checked :
    (Witness.linear .positive case_30_25_9).check 30 25 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_25_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_30_25_10_checked :
    (Witness.linear .positive case_30_25_10).check 30 25 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_25_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_30_25_11_checked :
    (Witness.linear .positive case_30_25_11).check 30 25 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_25_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_30_25_12_checked :
    (Witness.linear .positive case_30_25_12).check 30 25 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_25_13 : Certificate := {
  objectiveScale := 10
  eta := 5236
  rows := #[⟨.assumptionRow 13, 7⟩]
  caps := #[0, 0, 2366, 923, 385, 80750] }

theorem case_30_25_13_checked :
    (Witness.linear .conditional case_30_25_13).check 30 25 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_25_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 16796] }

theorem case_30_25_14_checked :
    (Witness.linear .negative case_30_25_14).check 30 25 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_25_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_30_25_15_checked :
    (Witness.linear .negative case_30_25_15).check 30 25 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_25_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_30_25_16_checked :
    (Witness.linear .negative case_30_25_16).check 30 25 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_26_1_checked :
    (Witness.rising).check 30 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_26_2_checked :
    (Witness.rising).check 30 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_26_3_checked :
    (Witness.rising).check 30 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_26_4_checked :
    (Witness.rising).check 30 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_26_5_checked :
    (Witness.rising).check 30 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_26_6_checked :
    (Witness.rising).check 30 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_26_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5, 2] }

theorem case_30_26_7_checked :
    (Witness.linear .positive case_30_26_7).check 30 26 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_26_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5] }

theorem case_30_26_8_checked :
    (Witness.linear .positive case_30_26_8).check 30 26 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_26_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_30_26_9_checked :
    (Witness.linear .positive case_30_26_9).check 30 26 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_26_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_30_26_10_checked :
    (Witness.linear .positive case_30_26_10).check 30 26 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_26_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_30_26_11_checked :
    (Witness.linear .positive case_30_26_11).check 30 26 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_26_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_30_26_12_checked :
    (Witness.linear .positive case_30_26_12).check 30 26 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_26_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_30_26_13_checked :
    (Witness.linear .positive case_30_26_13).check 30 26 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_26_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 58786] }

theorem case_30_26_14_checked :
    (Witness.linear .negative case_30_26_14).check 30 26 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_26_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_30_26_15_checked :
    (Witness.linear .negative case_30_26_15).check 30 26 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_26_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_30_26_16_checked :
    (Witness.linear .negative case_30_26_16).check 30 26 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_27_1_checked :
    (Witness.rising).check 30 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_27_2_checked :
    (Witness.rising).check 30 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_27_3_checked :
    (Witness.rising).check 30 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_27_4_checked :
    (Witness.rising).check 30 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_27_5_checked :
    (Witness.rising).check 30 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_27_6_checked :
    (Witness.rising).check 30 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_27_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14, 5] }

theorem case_30_27_7_checked :
    (Witness.linear .positive case_30_27_7).check 30 27 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_27_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14] }

theorem case_30_27_8_checked :
    (Witness.linear .positive case_30_27_8).check 30 27 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_27_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_30_27_9_checked :
    (Witness.linear .positive case_30_27_9).check 30 27 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_27_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_30_27_10_checked :
    (Witness.linear .positive case_30_27_10).check 30 27 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_27_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_30_27_11_checked :
    (Witness.linear .positive case_30_27_11).check 30 27 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_27_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_30_27_12_checked :
    (Witness.linear .positive case_30_27_12).check 30 27 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_27_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_30_27_13_checked :
    (Witness.linear .positive case_30_27_13).check 30 27 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_27_14 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 208012] }

theorem case_30_27_14_checked :
    (Witness.linear .negative case_30_27_14).check 30 27 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_27_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_30_27_15_checked :
    (Witness.linear .negative case_30_27_15).check 30 27 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_27_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_30_27_16_checked :
    (Witness.linear .negative case_30_27_16).check 30 27 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_27_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_30_27_17_checked :
    (Witness.linear .negative case_30_27_17).check 30 27 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_28_1_checked :
    (Witness.rising).check 30 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_28_2_checked :
    (Witness.rising).check 30 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_28_3_checked :
    (Witness.rising).check 30 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_28_4_checked :
    (Witness.rising).check 30 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_28_5_checked :
    (Witness.rising).check 30 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_28_6_checked :
    (Witness.rising).check 30 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_28_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0, 14] }

theorem case_30_28_7_checked :
    (Witness.linear .positive case_30_28_7).check 30 28 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_28_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_30_28_8_checked :
    (Witness.linear .positive case_30_28_8).check 30 28 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_28_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_30_28_9_checked :
    (Witness.linear .positive case_30_28_9).check 30 28 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_28_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_30_28_10_checked :
    (Witness.linear .positive case_30_28_10).check 30 28 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_28_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_30_28_11_checked :
    (Witness.linear .positive case_30_28_11).check 30 28 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_28_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_30_28_12_checked :
    (Witness.linear .positive case_30_28_12).check 30 28 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_28_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_30_28_13_checked :
    (Witness.linear .positive case_30_28_13).check 30 28 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_28_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_30_28_14_checked :
    (Witness.linear .positive case_30_28_14).check 30 28 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_28_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_30_28_15_checked :
    (Witness.linear .negative case_30_28_15).check 30 28 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_28_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_30_28_16_checked :
    (Witness.linear .negative case_30_28_16).check 30 28 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_28_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_30_28_17_checked :
    (Witness.linear .negative case_30_28_17).check 30 28 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_28_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_30_28_18_checked :
    (Witness.linear .negative case_30_28_18).check 30 28 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_29_1_checked :
    (Witness.rising).check 30 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_29_2_checked :
    (Witness.rising).check 30 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_29_3_checked :
    (Witness.rising).check 30 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_29_4_checked :
    (Witness.rising).check 30 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_29_5_checked :
    (Witness.rising).check 30 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_30_29_6_checked :
    (Witness.rising).check 30 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_29_7 : Certificate := {
  objectiveScale := 1
  eta := 42
  rows := #[]
  caps := #[0, 0] }

theorem case_30_29_7_checked :
    (Witness.linear .positive case_30_29_7).check 30 29 7 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_29_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_30_29_8_checked :
    (Witness.linear .positive case_30_29_8).check 30 29 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_29_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_30_29_9_checked :
    (Witness.linear .positive case_30_29_9).check 30 29 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_29_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_30_29_10_checked :
    (Witness.linear .positive case_30_29_10).check 30 29 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_29_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_30_29_11_checked :
    (Witness.linear .positive case_30_29_11).check 30 29 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_29_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_30_29_12_checked :
    (Witness.linear .positive case_30_29_12).check 30 29 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_29_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_30_29_13_checked :
    (Witness.linear .positive case_30_29_13).check 30 29 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_29_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_30_29_14_checked :
    (Witness.linear .positive case_30_29_14).check 30 29 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_29_15 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_30_29_15_checked :
    (Witness.linear .negative case_30_29_15).check 30 29 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_29_16 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_30_29_16_checked :
    (Witness.linear .negative case_30_29_16).check 30 29 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_29_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_30_29_17_checked :
    (Witness.linear .negative case_30_29_17).check 30 29 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_30_29_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_30_29_18_checked :
    (Witness.linear .negative case_30_29_18).check 30 29 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_30 (a k : ℕ) (h : Domain 30 a k) :
    ∃ w : Witness, w.check 30 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 15 ≤ a := by omega
  have haHi : a ≤ 29 := by omega
  interval_cases a

  · have hkHi : k ≤ 9 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_30_15_1_checked⟩

    · exact ⟨Witness.rising, case_30_15_2_checked⟩

    · exact ⟨Witness.rising, case_30_15_3_checked⟩

    · exact ⟨Witness.rising, case_30_15_4_checked⟩

    · exact ⟨Witness.rising, case_30_15_5_checked⟩

    · exact ⟨Witness.rising, case_30_15_6_checked⟩

    · exact ⟨Witness.rising, case_30_15_7_checked⟩

    · exact ⟨Witness.linear .positive case_30_15_8, case_30_15_8_checked⟩

    · exact ⟨Witness.linear .conditional case_30_15_9, case_30_15_9_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_30_16_1_checked⟩

    · exact ⟨Witness.rising, case_30_16_2_checked⟩

    · exact ⟨Witness.rising, case_30_16_3_checked⟩

    · exact ⟨Witness.rising, case_30_16_4_checked⟩

    · exact ⟨Witness.rising, case_30_16_5_checked⟩

    · exact ⟨Witness.rising, case_30_16_6_checked⟩

    · exact ⟨Witness.rising, case_30_16_7_checked⟩

    · exact ⟨Witness.linear .positive case_30_16_8, case_30_16_8_checked⟩

    · exact ⟨Witness.linear .conditional case_30_16_9, case_30_16_9_checked⟩

    · exact ⟨Witness.linear .conditional case_30_16_10, case_30_16_10_checked⟩

  · have hkHi : k ≤ 10 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_30_17_1_checked⟩

    · exact ⟨Witness.rising, case_30_17_2_checked⟩

    · exact ⟨Witness.rising, case_30_17_3_checked⟩

    · exact ⟨Witness.rising, case_30_17_4_checked⟩

    · exact ⟨Witness.rising, case_30_17_5_checked⟩

    · exact ⟨Witness.rising, case_30_17_6_checked⟩

    · exact ⟨Witness.linear .positive case_30_17_7, case_30_17_7_checked⟩

    · exact ⟨Witness.linear .positive case_30_17_8, case_30_17_8_checked⟩

    · exact ⟨Witness.linear .conditional case_30_17_9, case_30_17_9_checked⟩

    · exact ⟨Witness.linear .conditional case_30_17_10, case_30_17_10_checked⟩

  · have hkHi : k ≤ 11 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_30_18_1_checked⟩

    · exact ⟨Witness.rising, case_30_18_2_checked⟩

    · exact ⟨Witness.rising, case_30_18_3_checked⟩

    · exact ⟨Witness.rising, case_30_18_4_checked⟩

    · exact ⟨Witness.rising, case_30_18_5_checked⟩

    · exact ⟨Witness.rising, case_30_18_6_checked⟩

    · exact ⟨Witness.linear .positive case_30_18_7, case_30_18_7_checked⟩

    · exact ⟨Witness.linear .positive case_30_18_8, case_30_18_8_checked⟩

    · exact ⟨Witness.linear .positive case_30_18_9, case_30_18_9_checked⟩

    · exact ⟨Witness.linear .conditional case_30_18_10, case_30_18_10_checked⟩

    · exact ⟨Witness.linear .negative case_30_18_11, case_30_18_11_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_30_19_1_checked⟩

    · exact ⟨Witness.rising, case_30_19_2_checked⟩

    · exact ⟨Witness.rising, case_30_19_3_checked⟩

    · exact ⟨Witness.rising, case_30_19_4_checked⟩

    · exact ⟨Witness.rising, case_30_19_5_checked⟩

    · exact ⟨Witness.rising, case_30_19_6_checked⟩

    · exact ⟨Witness.linear .positive case_30_19_7, case_30_19_7_checked⟩

    · exact ⟨Witness.linear .positive case_30_19_8, case_30_19_8_checked⟩

    · exact ⟨Witness.linear .positive case_30_19_9, case_30_19_9_checked⟩

    · exact ⟨Witness.linear .conditional case_30_19_10, case_30_19_10_checked⟩

    · exact ⟨Witness.linear .conditional case_30_19_11, case_30_19_11_checked⟩

    · exact ⟨Witness.linear .negative case_30_19_12, case_30_19_12_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_30_20_1_checked⟩

    · exact ⟨Witness.rising, case_30_20_2_checked⟩

    · exact ⟨Witness.rising, case_30_20_3_checked⟩

    · exact ⟨Witness.rising, case_30_20_4_checked⟩

    · exact ⟨Witness.rising, case_30_20_5_checked⟩

    · exact ⟨Witness.rising, case_30_20_6_checked⟩

    · exact ⟨Witness.linear .positive case_30_20_7, case_30_20_7_checked⟩

    · exact ⟨Witness.linear .positive case_30_20_8, case_30_20_8_checked⟩

    · exact ⟨Witness.linear .positive case_30_20_9, case_30_20_9_checked⟩

    · exact ⟨Witness.linear .conditional case_30_20_10, case_30_20_10_checked⟩

    · exact ⟨Witness.linear .conditional case_30_20_11, case_30_20_11_checked⟩

    · exact ⟨Witness.linear .negative case_30_20_12, case_30_20_12_checked⟩

  · have hkHi : k ≤ 13 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_30_21_1_checked⟩

    · exact ⟨Witness.rising, case_30_21_2_checked⟩

    · exact ⟨Witness.rising, case_30_21_3_checked⟩

    · exact ⟨Witness.rising, case_30_21_4_checked⟩

    · exact ⟨Witness.rising, case_30_21_5_checked⟩

    · exact ⟨Witness.rising, case_30_21_6_checked⟩

    · exact ⟨Witness.linear .positive case_30_21_7, case_30_21_7_checked⟩

    · exact ⟨Witness.linear .positive case_30_21_8, case_30_21_8_checked⟩

    · exact ⟨Witness.linear .positive case_30_21_9, case_30_21_9_checked⟩

    · exact ⟨Witness.linear .positive case_30_21_10, case_30_21_10_checked⟩

    · exact ⟨Witness.linear .conditional case_30_21_11, case_30_21_11_checked⟩

    · exact ⟨Witness.linear .conditional case_30_21_12, case_30_21_12_checked⟩

    · exact ⟨Witness.linear .negative case_30_21_13, case_30_21_13_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_30_22_1_checked⟩

    · exact ⟨Witness.rising, case_30_22_2_checked⟩

    · exact ⟨Witness.rising, case_30_22_3_checked⟩

    · exact ⟨Witness.rising, case_30_22_4_checked⟩

    · exact ⟨Witness.rising, case_30_22_5_checked⟩

    · exact ⟨Witness.rising, case_30_22_6_checked⟩

    · exact ⟨Witness.linear .positive case_30_22_7, case_30_22_7_checked⟩

    · exact ⟨Witness.linear .positive case_30_22_8, case_30_22_8_checked⟩

    · exact ⟨Witness.linear .positive case_30_22_9, case_30_22_9_checked⟩

    · exact ⟨Witness.linear .positive case_30_22_10, case_30_22_10_checked⟩

    · exact ⟨Witness.linear .conditional case_30_22_11, case_30_22_11_checked⟩

    · exact ⟨Witness.linear .conditional case_30_22_12, case_30_22_12_checked⟩

    · exact ⟨Witness.linear .negative case_30_22_13, case_30_22_13_checked⟩

    · exact ⟨Witness.linear .negative case_30_22_14, case_30_22_14_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_30_23_1_checked⟩

    · exact ⟨Witness.rising, case_30_23_2_checked⟩

    · exact ⟨Witness.rising, case_30_23_3_checked⟩

    · exact ⟨Witness.rising, case_30_23_4_checked⟩

    · exact ⟨Witness.rising, case_30_23_5_checked⟩

    · exact ⟨Witness.rising, case_30_23_6_checked⟩

    · exact ⟨Witness.linear .positive case_30_23_7, case_30_23_7_checked⟩

    · exact ⟨Witness.linear .positive case_30_23_8, case_30_23_8_checked⟩

    · exact ⟨Witness.linear .positive case_30_23_9, case_30_23_9_checked⟩

    · exact ⟨Witness.linear .positive case_30_23_10, case_30_23_10_checked⟩

    · exact ⟨Witness.linear .positive case_30_23_11, case_30_23_11_checked⟩

    · exact ⟨Witness.linear .conditional case_30_23_12, case_30_23_12_checked⟩

    · exact ⟨Witness.linear .negative case_30_23_13, case_30_23_13_checked⟩

    · exact ⟨Witness.linear .negative case_30_23_14, case_30_23_14_checked⟩

  · have hkHi : k ≤ 15 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_30_24_1_checked⟩

    · exact ⟨Witness.rising, case_30_24_2_checked⟩

    · exact ⟨Witness.rising, case_30_24_3_checked⟩

    · exact ⟨Witness.rising, case_30_24_4_checked⟩

    · exact ⟨Witness.rising, case_30_24_5_checked⟩

    · exact ⟨Witness.rising, case_30_24_6_checked⟩

    · exact ⟨Witness.linear .positive case_30_24_7, case_30_24_7_checked⟩

    · exact ⟨Witness.linear .positive case_30_24_8, case_30_24_8_checked⟩

    · exact ⟨Witness.linear .positive case_30_24_9, case_30_24_9_checked⟩

    · exact ⟨Witness.linear .positive case_30_24_10, case_30_24_10_checked⟩

    · exact ⟨Witness.linear .positive case_30_24_11, case_30_24_11_checked⟩

    · exact ⟨Witness.linear .conditional case_30_24_12, case_30_24_12_checked⟩

    · exact ⟨Witness.linear .negative case_30_24_13, case_30_24_13_checked⟩

    · exact ⟨Witness.linear .negative case_30_24_14, case_30_24_14_checked⟩

    · exact ⟨Witness.linear .negative case_30_24_15, case_30_24_15_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_30_25_1_checked⟩

    · exact ⟨Witness.rising, case_30_25_2_checked⟩

    · exact ⟨Witness.rising, case_30_25_3_checked⟩

    · exact ⟨Witness.rising, case_30_25_4_checked⟩

    · exact ⟨Witness.rising, case_30_25_5_checked⟩

    · exact ⟨Witness.rising, case_30_25_6_checked⟩

    · exact ⟨Witness.linear .positive case_30_25_7, case_30_25_7_checked⟩

    · exact ⟨Witness.linear .positive case_30_25_8, case_30_25_8_checked⟩

    · exact ⟨Witness.linear .positive case_30_25_9, case_30_25_9_checked⟩

    · exact ⟨Witness.linear .positive case_30_25_10, case_30_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_30_25_11, case_30_25_11_checked⟩

    · exact ⟨Witness.linear .positive case_30_25_12, case_30_25_12_checked⟩

    · exact ⟨Witness.linear .conditional case_30_25_13, case_30_25_13_checked⟩

    · exact ⟨Witness.linear .negative case_30_25_14, case_30_25_14_checked⟩

    · exact ⟨Witness.linear .negative case_30_25_15, case_30_25_15_checked⟩

    · exact ⟨Witness.linear .negative case_30_25_16, case_30_25_16_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_30_26_1_checked⟩

    · exact ⟨Witness.rising, case_30_26_2_checked⟩

    · exact ⟨Witness.rising, case_30_26_3_checked⟩

    · exact ⟨Witness.rising, case_30_26_4_checked⟩

    · exact ⟨Witness.rising, case_30_26_5_checked⟩

    · exact ⟨Witness.rising, case_30_26_6_checked⟩

    · exact ⟨Witness.linear .positive case_30_26_7, case_30_26_7_checked⟩

    · exact ⟨Witness.linear .positive case_30_26_8, case_30_26_8_checked⟩

    · exact ⟨Witness.linear .positive case_30_26_9, case_30_26_9_checked⟩

    · exact ⟨Witness.linear .positive case_30_26_10, case_30_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_30_26_11, case_30_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_30_26_12, case_30_26_12_checked⟩

    · exact ⟨Witness.linear .positive case_30_26_13, case_30_26_13_checked⟩

    · exact ⟨Witness.linear .negative case_30_26_14, case_30_26_14_checked⟩

    · exact ⟨Witness.linear .negative case_30_26_15, case_30_26_15_checked⟩

    · exact ⟨Witness.linear .negative case_30_26_16, case_30_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_30_27_1_checked⟩

    · exact ⟨Witness.rising, case_30_27_2_checked⟩

    · exact ⟨Witness.rising, case_30_27_3_checked⟩

    · exact ⟨Witness.rising, case_30_27_4_checked⟩

    · exact ⟨Witness.rising, case_30_27_5_checked⟩

    · exact ⟨Witness.rising, case_30_27_6_checked⟩

    · exact ⟨Witness.linear .positive case_30_27_7, case_30_27_7_checked⟩

    · exact ⟨Witness.linear .positive case_30_27_8, case_30_27_8_checked⟩

    · exact ⟨Witness.linear .positive case_30_27_9, case_30_27_9_checked⟩

    · exact ⟨Witness.linear .positive case_30_27_10, case_30_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_30_27_11, case_30_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_30_27_12, case_30_27_12_checked⟩

    · exact ⟨Witness.linear .positive case_30_27_13, case_30_27_13_checked⟩

    · exact ⟨Witness.linear .negative case_30_27_14, case_30_27_14_checked⟩

    · exact ⟨Witness.linear .negative case_30_27_15, case_30_27_15_checked⟩

    · exact ⟨Witness.linear .negative case_30_27_16, case_30_27_16_checked⟩

    · exact ⟨Witness.linear .negative case_30_27_17, case_30_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_30_28_1_checked⟩

    · exact ⟨Witness.rising, case_30_28_2_checked⟩

    · exact ⟨Witness.rising, case_30_28_3_checked⟩

    · exact ⟨Witness.rising, case_30_28_4_checked⟩

    · exact ⟨Witness.rising, case_30_28_5_checked⟩

    · exact ⟨Witness.rising, case_30_28_6_checked⟩

    · exact ⟨Witness.linear .positive case_30_28_7, case_30_28_7_checked⟩

    · exact ⟨Witness.linear .positive case_30_28_8, case_30_28_8_checked⟩

    · exact ⟨Witness.linear .positive case_30_28_9, case_30_28_9_checked⟩

    · exact ⟨Witness.linear .positive case_30_28_10, case_30_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_30_28_11, case_30_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_30_28_12, case_30_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_30_28_13, case_30_28_13_checked⟩

    · exact ⟨Witness.linear .positive case_30_28_14, case_30_28_14_checked⟩

    · exact ⟨Witness.linear .negative case_30_28_15, case_30_28_15_checked⟩

    · exact ⟨Witness.linear .negative case_30_28_16, case_30_28_16_checked⟩

    · exact ⟨Witness.linear .negative case_30_28_17, case_30_28_17_checked⟩

    · exact ⟨Witness.linear .negative case_30_28_18, case_30_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_30_29_1_checked⟩

    · exact ⟨Witness.rising, case_30_29_2_checked⟩

    · exact ⟨Witness.rising, case_30_29_3_checked⟩

    · exact ⟨Witness.rising, case_30_29_4_checked⟩

    · exact ⟨Witness.rising, case_30_29_5_checked⟩

    · exact ⟨Witness.rising, case_30_29_6_checked⟩

    · exact ⟨Witness.linear .positive case_30_29_7, case_30_29_7_checked⟩

    · exact ⟨Witness.linear .positive case_30_29_8, case_30_29_8_checked⟩

    · exact ⟨Witness.linear .positive case_30_29_9, case_30_29_9_checked⟩

    · exact ⟨Witness.linear .positive case_30_29_10, case_30_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_30_29_11, case_30_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_30_29_12, case_30_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_30_29_13, case_30_29_13_checked⟩

    · exact ⟨Witness.linear .positive case_30_29_14, case_30_29_14_checked⟩

    · exact ⟨Witness.linear .negative case_30_29_15, case_30_29_15_checked⟩

    · exact ⟨Witness.linear .negative case_30_29_16, case_30_29_16_checked⟩

    · exact ⟨Witness.linear .negative case_30_29_17, case_30_29_17_checked⟩

    · exact ⟨Witness.linear .negative case_30_29_18, case_30_29_18_checked⟩


#print axioms coverage_30
end ForestUnimodality.FiniteRows.FiniteData
