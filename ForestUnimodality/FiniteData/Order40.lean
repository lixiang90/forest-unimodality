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

theorem case_40_20_1_checked :
    (Witness.rising).check 40 20 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_20_2_checked :
    (Witness.rising).check 40 20 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_20_3_checked :
    (Witness.rising).check 40 20 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_20_4_checked :
    (Witness.rising).check 40 20 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_20_5_checked :
    (Witness.rising).check 40 20 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_20_6_checked :
    (Witness.rising).check 40 20 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_20_7_checked :
    (Witness.rising).check 40 20 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_20_8_checked :
    (Witness.rising).check 40 20 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_20_9 : Certificate := {
  objectiveScale := 530808300000
  eta := 0
  rows := #[⟨.count 2, 607001797321920⟩, ⟨.count 3, 216129427834320⟩, ⟨.count 4, 34314845685120⟩, ⟨.count 5, 7004015518500⟩, ⟨.count 6, 1758249412920⟩, ⟨.count 7, 656928352080⟩, ⟨.count 8, 529109713440⟩, ⟨.count 10, 97282684800⟩, ⟨.path 9, 126862991640⟩, ⟨.path 10, 98955535200⟩, ⟨.hall 8 1, 2837411640⟩, ⟨.hall 8 2, 819696696⟩, ⟨.hall 7 3, 408722391⟩, ⟨.hall 7 4, 474403216⟩, ⟨.hall 0 5, 1053017505540⟩, ⟨.hall 1 5, 32892420990⟩, ⟨.hall 1 6, 4352628060⟩, ⟨.hall 6 6, 603995505⟩, ⟨.hall 5 9, 1088961270⟩, ⟨.hall 4 13, 24749821668⟩, ⟨.hall 3 16, 386428442400⟩]
  caps := #[0, 2065756836000, 0, 341728392720, 0, 0, 5158179480, 3665290200, 3076575480, 0, 1672850400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_40_20_9_checked :
    (Witness.linear .positive case_40_20_9).check 40 20 9 = true := by
  change case_40_20_9.check 40 20 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_20_10 : Certificate := {
  objectiveScale := 16500000
  eta := 0
  rows := #[⟨.count 2, 17422685280⟩, ⟨.count 3, 12938365440⟩, ⟨.count 4, 2361078720⟩, ⟨.count 5, 497296800⟩, ⟨.count 6, 127567440⟩, ⟨.count 7, 41621580⟩, ⟨.count 8, 17297280⟩, ⟨.count 9, 16465680⟩, ⟨.path 10, 856800⟩, ⟨.path 11, 4642920⟩, ⟨.privateRow 4 16, 4324320⟩, ⟨.privateRow 9 2, 404712⟩, ⟨.privateRow 11 0, 464940⟩, ⟨.privateRow 12 0, 514360⟩, ⟨.hall 0 1, 330810480⟩, ⟨.hall 9 1, 694008⟩, ⟨.hall 1 3, 4054050⟩, ⟨.hall 8 3, 90888⟩, ⟨.hall 9 3, 6426⟩, ⟨.hall 7 4, 49308⟩, ⟨.hall 0 5, 59459400⟩, ⟨.hall 1 5, 2458170⟩, ⟨.hall 7 5, 32025⟩, ⟨.hall 6 7, 46440⟩, ⟨.hall 6 8, 20040⟩, ⟨.hall 5 11, 453915⟩, ⟨.hall 4 14, 10198188⟩]
  caps := #[0, 0, 157528800, 0, 0, 665280, 246960, 0, 59520, 34320, 168000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_40_20_10_checked :
    (Witness.linear .positive case_40_20_10).check 40 20 10 = true := by
  change case_40_20_10.check 40 20 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_20_11 : Certificate := {
  objectiveScale := 21600000
  eta := 0
  rows := #[⟨.count 3, 28596728160⟩, ⟨.count 4, 6140534400⟩, ⟨.count 5, 1518917400⟩, ⟨.count 6, 412972560⟩, ⟨.count 7, 129729600⟩, ⟨.count 8, 46569600⟩, ⟨.count 9, 21455280⟩, ⟨.count 10, 21772800⟩, ⟨.path 12, 3110400⟩, ⟨.path 13, 2980530⟩, ⟨.privateRow 9 4, 332640⟩, ⟨.privateRow 12 0, 344960⟩, ⟨.privateRow 13 0, 374220⟩, ⟨.hall 10 1, 912240⟩, ⟨.hall 11 1, 180180⟩, ⟨.hall 9 3, 245322⟩, ⟨.hall 10 3, 69660⟩, ⟨.hall 0 4, 285405120⟩, ⟨.hall 1 4, 18882864⟩, ⟨.hall 9 4, 60912⟩, ⟨.hall 1 5, 617760⟩, ⟨.hall 8 5, 232800⟩, ⟨.hall 0 6, 17451720⟩, ⟨.hall 7 7, 292005⟩, ⟨.hall 6 9, 545184⟩, ⟨.hall 5 12, 5480640⟩, ⟨.hall 4 15, 383783400⟩]
  caps := #[0, 3958985160, 0, 0, 0, 0, 362880, 0, 0, 196020, 0, 0, 146320, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_40_20_11_checked :
    (Witness.linear .positive case_40_20_11).check 40 20 11 = true := by
  change case_40_20_11.check 40 20 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_20_12 : Certificate := {
  objectiveScale := 22400000
  eta := 0
  rows := #[⟨.count 2, 59545886400⟩, ⟨.count 3, 16172956800⟩, ⟨.count 4, 4566481920⟩, ⟨.count 5, 1372971600⟩, ⟨.count 6, 447567120⟩, ⟨.count 7, 165405240⟩, ⟨.count 8, 72515520⟩, ⟨.count 9, 37422000⟩, ⟨.count 10, 27669600⟩, ⟨.count 11, 27941760⟩, ⟨.path 11, 4275720⟩, ⟨.privateRow 3 17, 269549280⟩, ⟨.privateRow 10 3, 1207710⟩, ⟨.privateRow 13 0, 2796255⟩, ⟨.hall 11 1, 3173940⟩, ⟨.hall 10 2, 1050840⟩, ⟨.hall 0 3, 43243200⟩, ⟨.hall 10 3, 229500⟩, ⟨.hall 9 4, 648216⟩, ⟨.hall 0 5, 15495480⟩, ⟨.hall 8 5, 350640⟩, ⟨.hall 8 6, 351840⟩, ⟨.hall 7 7, 334110⟩, ⟨.hall 11 7, 76230⟩, ⟨.hall 7 8, 721896⟩, ⟨.hall 6 10, 3591540⟩, ⟨.hall 5 12, 15859800⟩, ⟨.hall 4 14, 109189080⟩, ⟨.hall 3 16, 1258377120⟩, ⟨.assumptionRow 12, 23418990⟩]
  caps := #[0, 1898115960, 0, 0, 4600310, 0, 690690, 806520, 191110, 399300, 25110, 0, 325010, 29960, 0, 0, 0, 0, 0, 0, 0] }

theorem case_40_20_12_checked :
    (Witness.linear .conditional case_40_20_12).check 40 20 12 = true := by
  change case_40_20_12.check 40 20 12 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_21_1_checked :
    (Witness.rising).check 40 21 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_21_2_checked :
    (Witness.rising).check 40 21 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_21_3_checked :
    (Witness.rising).check 40 21 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_21_4_checked :
    (Witness.rising).check 40 21 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_21_5_checked :
    (Witness.rising).check 40 21 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_21_6_checked :
    (Witness.rising).check 40 21 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_21_7_checked :
    (Witness.rising).check 40 21 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_21_8_checked :
    (Witness.rising).check 40 21 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_21_9 : Certificate := {
  objectiveScale := 4371392025000
  eta := 65200074423644160
  rows := #[⟨.count 2, 14979415246635840⟩, ⟨.count 3, 2230598951380800⟩, ⟨.count 4, 351236103538320⟩, ⟨.count 5, 66585043324800⟩, ⟨.count 6, 16170653378880⟩, ⟨.count 7, 5634119050560⟩, ⟨.count 8, 4353637448160⟩, ⟨.path 9, 1267874887104⟩, ⟨.path 10, 698040317975⟩, ⟨.privateRow 6 8, 178352794620⟩, ⟨.privateRow 6 9, 900256963320⟩, ⟨.privateRow 7 5, 168291867744⟩, ⟨.privateRow 7 6, 361786865440⟩, ⟨.privateRow 7 7, 457314858000⟩, ⟨.privateRow 7 8, 324040242240⟩, ⟨.privateRow 8 2, 95146896845⟩, ⟨.privateRow 8 3, 198862673100⟩, ⟨.privateRow 8 4, 77895964146⟩, ⟨.privateRow 9 0, 112228690560⟩, ⟨.privateRow 10 0, 58203709200⟩, ⟨.hall 5 9, 3381358344⟩, ⟨.hall 4 13, 57702374730⟩, ⟨.hall 6 14, 1173165049056⟩, ⟨.hall 3 17, 9617839591360⟩]
  caps := #[0, 0, 4454944546962, 0, 0, 56968229080, 0, 126367660796, 17754576840, 24484510764, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_40_21_9_checked :
    (Witness.linear .positive case_40_21_9).check 40 21 9 = true := by
  change case_40_21_9.check 40 21 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_21_10 : Certificate := {
  objectiveScale := 7405200000
  eta := 148962635902080
  rows := #[⟨.count 2, 37978415354880⟩, ⟨.count 3, 6475651902720⟩, ⟨.count 4, 1205693929440⟩, ⟨.count 5, 252837224640⟩, ⟨.count 6, 63074531520⟩, ⟨.count 7, 19594159200⟩, ⟨.count 8, 8127947520⟩, ⟨.count 9, 7362653760⟩, ⟨.path 10, 672145320⟩, ⟨.path 11, 1880954460⟩, ⟨.privateRow 6 10, 920960040⟩, ⟨.privateRow 7 7, 1096339860⟩, ⟨.privateRow 7 8, 1839451680⟩, ⟨.privateRow 8 4, 272141100⟩, ⟨.privateRow 8 5, 346727920⟩, ⟨.privateRow 8 6, 2181664485⟩, ⟨.privateRow 8 7, 228080160⟩, ⟨.privateRow 9 2, 453418560⟩, ⟨.privateRow 9 3, 432786816⟩, ⟨.privateRow 10 0, 279068328⟩, ⟨.privateRow 11 0, 170331840⟩, ⟨.hall 11 6, 20388984⟩, ⟨.hall 6 8, 14074368⟩, ⟨.hall 5 11, 79482480⟩, ⟨.hall 7 13, 3172387680⟩, ⟨.hall 4 14, 1148755608⟩, ⟨.hall 3 17, 54089555520⟩]
  caps := #[0, 504166256880, 15874527240, 6928058280, 0, 1331890560, 56156100, 0, 71038495, 127475928, 0, 100866780, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_40_21_10_checked :
    (Witness.linear .positive case_40_21_10).check 40 21 10 = true := by
  change case_40_21_10.check 40 21 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_21_11 : Certificate := {
  objectiveScale := 64178400000
  eta := 1726349927702400
  rows := #[⟨.count 2, 485379544890240⟩, ⟨.count 3, 98017821982080⟩, ⟨.count 4, 22002499078560⟩, ⟨.count 5, 5298260647680⟩, ⟨.count 6, 1335077583840⟩, ⟨.count 7, 413219046240⟩, ⟨.count 8, 143400216960⟩, ⟨.count 9, 64838854080⟩, ⟨.count 10, 64838854080⟩, ⟨.path 12, 14669081856⟩, ⟨.path 13, 2751036288⟩, ⟨.privateRow 8 6, 6898776885⟩, ⟨.privateRow 11 1, 1921151232⟩, ⟨.privateRow 12 0, 1462304844⟩, ⟨.privateRow 13 0, 1886844960⟩, ⟨.hall 9 3, 531747216⟩, ⟨.hall 10 3, 114614136⟩, ⟨.hall 8 5, 296514680⟩, ⟨.hall 7 7, 232792560⟩, ⟨.hall 6 10, 369667584⟩, ⟨.hall 5 12, 7018389378⟩, ⟨.hall 4 15, 192624672240⟩]
  caps := #[0, 6076695630720, 0, 54330866304, 23794783584, 0, 0, 0, 378411891, 0, 908999520, 0, 46033416, 0, 0, 0, 0, 0, 0, 0] }

theorem case_40_21_11_checked :
    (Witness.linear .positive case_40_21_11).check 40 21 11 = true := by
  change case_40_21_11.check 40 21 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_21_12 : Certificate := {
  objectiveScale := 1285200000
  eta := 33435235753920
  rows := #[⟨.count 2, 8415671584320⟩, ⟨.count 3, 2113952480640⟩, ⟨.count 4, 531832981680⟩, ⟨.count 5, 156651014520⟩, ⟨.count 6, 48978329400⟩, ⟨.count 7, 16595659080⟩, ⟨.count 8, 6432426000⟩, ⟨.count 9, 3017392560⟩, ⟨.count 10, 1964813760⟩, ⟨.count 11, 1972610640⟩, ⟨.count 13, 477837360⟩, ⟨.path 11, 321273225⟩, ⟨.privateRow 3 18, 17839261440⟩, ⟨.privateRow 8 7, 545224680⟩, ⟨.privateRow 8 8, 1268617350⟩, ⟨.privateRow 9 5, 292383000⟩, ⟨.privateRow 9 6, 959016240⟩, ⟨.privateRow 9 7, 1307276880⟩, ⟨.privateRow 10 3, 160615728⟩, ⟨.privateRow 10 4, 535938039⟩, ⟨.privateRow 10 5, 883163736⟩, ⟨.privateRow 11 1, 106817256⟩, ⟨.privateRow 11 2, 318805760⟩, ⟨.privateRow 12 0, 135080946⟩, ⟨.privateRow 13 0, 95975880⟩, ⟨.hall 8 7, 2115820⟩, ⟨.hall 7 8, 33322380⟩, ⟨.hall 8 8, 19525520⟩, ⟨.hall 7 9, 2724624⟩, ⟨.hall 6 10, 97747416⟩, ⟨.hall 5 12, 321774453⟩, ⟨.hall 4 15, 10821610800⟩, ⟨.hall 3 17, 135281065920⟩, ⟨.assumptionRow 12, 1669805280⟩]
  caps := #[0, 2421687060, 0, 0, 683937540, 133512390, 0, 33377715, 123689280, 4307715, 26264745, 53452505, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_40_21_12_checked :
    (Witness.linear .conditional case_40_21_12).check 40 21 12 = true := by
  change case_40_21_12.check 40 21 12 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_21_13 : Certificate := {
  objectiveScale := 87964800000
  eta := 1306021249653120
  rows := #[⟨.count 2, 340266072706560⟩, ⟨.count 3, 91542170079360⟩, ⟨.count 4, 27300759726240⟩, ⟨.count 5, 8462499645600⟩, ⟨.count 6, 2743742121120⟩, ⟨.count 7, 933988255200⟩, ⟨.count 8, 358500542400⟩, ⟨.count 9, 157465788480⟩, ⟨.count 10, 77189112000⟩, ⟨.count 11, 56605348800⟩, ⟨.count 12, 56605348800⟩, ⟨.count 14, 98115937920⟩, ⟨.path 10, 18885296430⟩, ⟨.privateRow 3 18, 10105941605760⟩, ⟨.privateRow 7 9, 18464125680⟩, ⟨.privateRow 8 7, 3032429400⟩, ⟨.privateRow 8 8, 98587649160⟩, ⟨.privateRow 9 6, 37638881280⟩, ⟨.privateRow 9 7, 115898022240⟩, ⟨.privateRow 10 4, 13083554484⟩, ⟨.privateRow 10 5, 55355620320⟩, ⟨.privateRow 10 6, 101838168432⟩, ⟨.privateRow 11 2, 3430627200⟩, ⟨.privateRow 11 3, 27745197480⟩, ⟨.privateRow 11 4, 55380124800⟩, ⟨.privateRow 12 1, 14885110240⟩, ⟨.privateRow 12 2, 8903549655⟩, ⟨.privateRow 13 0, 5301135840⟩, ⟨.hall 8 7, 30421160⟩, ⟨.hall 8 8, 4322003840⟩, ⟨.hall 9 8, 653378544⟩, ⟨.hall 7 9, 5424160896⟩, ⟨.hall 7 10, 4231263960⟩, ⟨.hall 9 10, 30618347760⟩, ⟨.hall 6 11, 25312602744⟩, ⟨.hall 5 12, 29707700022⟩, ⟨.hall 4 14, 138191969916⟩, ⟨.hall 3 17, 15175265064960⟩, ⟨.assumptionRow 13, 57052084320⟩]
  caps := #[0, 0, 985046402340, 127643836320, 3301978680, 11204793600, 0, 0, 0, 1266850200, 0, 5567229360, 446735520, 2082252480, 0, 0, 0, 0, 0, 0] }

theorem case_40_21_13_checked :
    (Witness.linear .conditional case_40_21_13).check 40 21 13 = true := by
  change case_40_21_13.check 40 21 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_22_1_checked :
    (Witness.rising).check 40 22 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_22_2_checked :
    (Witness.rising).check 40 22 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_22_3_checked :
    (Witness.rising).check 40 22 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_22_4_checked :
    (Witness.rising).check 40 22 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_22_5_checked :
    (Witness.rising).check 40 22 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_22_6_checked :
    (Witness.rising).check 40 22 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_22_7_checked :
    (Witness.rising).check 40 22 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_22_8_checked :
    (Witness.rising).check 40 22 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_22_9 : Certificate := {
  objectiveScale := 39437871873400000
  eta := 646240799879094420000
  rows := #[⟨.count 2, 118169746263605836800⟩, ⟨.count 3, 16373243795256047700⟩, ⟨.count 4, 2758742238139327440⟩, ⟨.count 5, 558575481288052800⟩, ⟨.count 6, 139643870322013200⟩, ⟨.count 7, 50128568833543200⟩, ⟨.count 8, 39495236050670400⟩, ⟨.path 9, 10757787103823760⟩, ⟨.path 10, 6453292649789700⟩, ⟨.privateRow 5 12, 27670174304547060⟩, ⟨.privateRow 5 13, 40031242825643784⟩, ⟨.privateRow 5 14, 34523067940719930⟩, ⟨.privateRow 6 8, 3845842582467600⟩, ⟨.privateRow 6 9, 9697490994584250⟩, ⟨.privateRow 6 11, 46050649543512900⟩, ⟨.privateRow 6 12, 596768676589800⟩, ⟨.privateRow 7 5, 2088690368064300⟩, ⟨.privateRow 7 6, 1133860485520620⟩, ⟨.privateRow 7 7, 12598449839118000⟩, ⟨.privateRow 8 2, 1037042070857100⟩, ⟨.privateRow 8 3, 2389335193770525⟩, ⟨.privateRow 8 4, 86309519341500⟩, ⟨.privateRow 9 0, 954829882543680⟩, ⟨.privateRow 10 0, 490769205363360⟩, ⟨.hall 10 10, 402777756927000⟩, ⟨.hall 4 14, 58565239731999⟩, ⟨.hall 4 15, 1038201977067255⟩, ⟨.hall 3 17, 31678470582308550⟩]
  caps := #[0, 300800351475023400, 83271305836547400, 64817357249536320, 26384675742865440, 5244954086182096, 1521123540572350, 1435749631250220, 0, 0, 236882715187140, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_40_22_9_checked :
    (Witness.linear .positive case_40_22_9).check 40 22 9 = true := by
  change case_40_22_9.check 40 22 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_22_10 : Certificate := {
  objectiveScale := 23005125000
  eta := 525410847561600
  rows := #[⟨.count 2, 100568836368000⟩, ⟨.count 3, 17476901442000⟩, ⟨.count 4, 3335941889280⟩, ⟨.count 5, 727109182800⟩, ⟨.count 6, 185989003200⟩, ⟨.count 7, 58963905000⟩, ⟨.count 8, 24014390400⟩, ⟨.count 9, 23156733600⟩, ⟨.path 10, 1863061200⟩, ⟨.path 11, 5836931100⟩, ⟨.privateRow 5 13, 53262937728⟩, ⟨.privateRow 5 14, 73148935860⟩, ⟨.privateRow 6 10, 16076689200⟩, ⟨.privateRow 6 11, 25382557200⟩, ⟨.privateRow 6 12, 35176181040⟩, ⟨.privateRow 6 13, 41274733500⟩, ⟨.privateRow 7 7, 4380175800⟩, ⟨.privateRow 7 8, 9223639425⟩, ⟨.privateRow 7 9, 12899858400⟩, ⟨.privateRow 7 10, 13758244500⟩, ⟨.privateRow 7 11, 6806119320⟩, ⟨.privateRow 8 4, 1052578800⟩, ⟨.privateRow 8 5, 1029188160⟩, ⟨.privateRow 8 6, 10268057800⟩, ⟨.privateRow 9 2, 1758196440⟩, ⟨.privateRow 9 3, 1060375680⟩, ⟨.privateRow 10 0, 791683200⟩, ⟨.privateRow 11 0, 482431950⟩, ⟨.privateRow 12 2, 861060200⟩, ⟨.hall 4 15, 571140570⟩, ⟨.hall 4 16, 24288504240⟩, ⟨.hall 5 16, 85026942000⟩, ⟨.hall 3 17, 51102051000⟩]
  caps := #[0, 394215822000, 0, 35667145800, 21024843840, 15067804752, 1793691900, 3236431770, 853795800, 595291320, 0, 1227025800, 0, 0, 0, 0, 0, 0, 0] }

theorem case_40_22_10_checked :
    (Witness.linear .positive case_40_22_10).check 40 22 10 = true := by
  change case_40_22_10.check 40 22 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_22_11 : Certificate := {
  objectiveScale := 14157000000
  eta := 500391283392000
  rows := #[⟨.count 2, 110871009849600⟩, ⟨.count 3, 22903939258200⟩, ⟨.count 4, 5273731663200⟩, ⟨.count 5, 1243969927200⟩, ⟨.count 6, 315372657600⟩, ⟨.count 7, 94342248000⟩, ⟨.count 8, 32590958400⟩, ⟨.count 9, 13894040160⟩, ⟨.count 10, 13722508800⟩, ⟨.path 12, 3775221450⟩, ⟨.privateRow 11 1, 370351800⟩, ⟨.privateRow 12 0, 336936600⟩, ⟨.privateRow 13 8, 3032429400⟩, ⟨.hall 9 4, 30707712⟩, ⟨.hall 10 4, 6497400⟩, ⟨.hall 8 5, 33034400⟩, ⟨.hall 7 7, 31841425⟩, ⟨.hall 9 9, 13494600⟩]
  caps := #[0, 0, 95425258500, 40360191300, 0, 1853151300, 1745944200, 0, 0, 262959840, 494762850, 0, 68918850, 0, 0, 0, 0, 0, 0] }

theorem case_40_22_11_checked :
    (Witness.linear .positive case_40_22_11).check 40 22 11 = true := by
  change case_40_22_11.check 40 22 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_22_12 : Certificate := {
  objectiveScale := 111919500000
  eta := 4040659613390400
  rows := #[⟨.count 2, 904138367932800⟩, ⟨.count 3, 231568944106500⟩, ⟨.count 4, 59887515607920⟩, ⟨.count 5, 16478221359600⟩, ⟨.count 6, 5108632729200⟩, ⟨.count 7, 1725283860300⟩, ⟨.count 8, 651819168000⟩, ⟨.count 9, 293318625600⟩, ⟨.count 10, 195545750400⟩, ⟨.count 11, 179250271200⟩, ⟨.path 11, 30139545150⟩, ⟨.privateRow 3 19, 24758943709500⟩, ⟨.privateRow 5 14, 1847558152440⟩, ⟨.privateRow 6 11, 65084919900⟩, ⟨.privateRow 6 12, 852719147280⟩, ⟨.privateRow 6 13, 1902933682650⟩, ⟨.privateRow 7 9, 80479713600⟩, ⟨.privateRow 7 10, 368103235500⟩, ⟨.privateRow 7 11, 852719147280⟩, ⟨.privateRow 7 12, 1139519581200⟩, ⟨.privateRow 8 7, 53978774850⟩, ⟨.privateRow 8 8, 181869187500⟩, ⟨.privateRow 8 9, 387357120150⟩, ⟨.privateRow 8 10, 557305388640⟩, ⟨.privateRow 8 11, 467985793275⟩, ⟨.privateRow 9 5, 31142471360⟩, ⟨.privateRow 9 6, 96958101240⟩, ⟨.privateRow 9 7, 196709713200⟩, ⟨.privateRow 9 8, 212927594880⟩, ⟨.privateRow 10 3, 18250936704⟩, ⟨.privateRow 10 4, 56309933680⟩, ⟨.privateRow 10 5, 82903250430⟩, ⟨.privateRow 11 1, 12591961200⟩, ⟨.privateRow 11 2, 27702314640⟩, ⟨.privateRow 12 0, 12512600100⟩, ⟨.privateRow 13 0, 10883052180⟩, ⟨.hall 6 11, 339435855⟩, ⟨.hall 6 12, 8869300605⟩, ⟨.hall 5 14, 93789440745⟩, ⟨.hall 5 15, 153596017575⟩, ⟨.hall 4 16, 1609854886640⟩, ⟨.hall 3 17, 1913771809950⟩, ⟨.assumptionRow 12, 159351943410⟩]
  caps := #[0, 10740466737000, 368153119620, 92557050300, 7167122820, 13987529820, 9595582920, 19689555600, 0, 6127650100, 12933955386, 0, 0, 3088978200, 0, 0, 0, 0, 0] }

theorem case_40_22_12_checked :
    (Witness.linear .conditional case_40_22_12).check 40 22 12 = true := by
  change case_40_22_12.check 40 22 12 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_22_13 : Certificate := {
  objectiveScale := 11360398272300000
  eta := 183819605298942412800
  rows := #[⟨.count 2, 49333938186848515200⟩, ⟨.count 3, 13621742350392676500⟩, ⟨.count 4, 3919682760050977920⟩, ⟨.count 5, 1212832873722670200⟩, ⟨.count 6, 389888868705336000⟩, ⟨.count 7, 138085640999806500⟩, ⟨.count 8, 54348145334683200⟩, ⟨.count 9, 23393332122320160⟩, ⟨.count 10, 12996295623511200⟩, ⟨.count 11, 6498147811755600⟩, ⟨.count 12, 8354761472257200⟩, ⟨.count 14, 16895184310564560⟩, ⟨.path 9, 407193406860240⟩, ⟨.path 10, 1802917481104740⟩, ⟨.privateRow 2 20, 3885892391429848800⟩, ⟨.privateRow 5 14, 247695469981669710⟩, ⟨.privateRow 6 11, 1237742440334400⟩, ⟨.privateRow 6 12, 90695577315503160⟩, ⟨.privateRow 6 13, 250990959229060050⟩, ⟨.privateRow 7 10, 34463391073060950⟩, ⟨.privateRow 7 11, 102160166669100540⟩, ⟨.privateRow 7 12, 174521684087150400⟩, ⟨.privateRow 8 8, 12511044325880100⟩, ⟨.privateRow 8 9, 43444056392987250⟩, ⟨.privateRow 8 10, 79513699587482160⟩, ⟨.privateRow 8 11, 101792008619376075⟩, ⟨.privateRow 9 6, 4578240503736900⟩, ⟨.privateRow 9 7, 18785554583075280⟩, ⟨.privateRow 9 8, 38555677016416560⟩, ⟨.privateRow 9 9, 53379330570021456⟩, ⟨.privateRow 9 10, 7709166267582780⟩, ⟨.privateRow 10 4, 1575308560425600⟩, ⟨.privateRow 10 5, 6114166350151860⟩, ⟨.privateRow 10 6, 24625448460653040⟩, ⟨.privateRow 10 7, 10337962427793000⟩, ⟨.privateRow 11 1, 281944429848900⟩, ⟨.privateRow 11 3, 4315689076999300⟩, ⟨.privateRow 11 4, 8381133825389325⟩, ⟨.privateRow 12 1, 2042275026551760⟩, ⟨.privateRow 12 2, 1315101342855300⟩, ⟨.privateRow 13 0, 696230122688100⟩, ⟨.hall 6 13, 538749499699125⟩, ⟨.hall 6 14, 62022500096131575⟩, ⟨.hall 7 14, 228734802973797120⟩, ⟨.hall 5 15, 145658850030418725⟩, ⟨.hall 4 16, 253924681844073240⟩, ⟨.hall 3 17, 351983006470095000⟩, ⟨.hall 2 19, 5964000061629289680⟩, ⟨.assumptionRow 13, 9057483251100900⟩]
  caps := #[0, 204993710385941400, 0, 0, 5451112966899600, 0, 213165703200450, 1234296628336695, 0, 55339278857940, 119660547485640, 1306437604778950, 702721778843700, 0, 0, 0, 0, 0, 0] }

theorem case_40_22_13_checked :
    (Witness.linear .conditional case_40_22_13).check 40 22 13 = true := by
  change case_40_22_13.check 40 22 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_22_14 : Certificate := {
  objectiveScale := 42872702418000000
  eta := 1091428906462470576000
  rows := #[⟨.count 2, 276650963456262595200⟩, ⟨.count 3, 70913696328978703200⟩, ⟨.count 4, 18560127928078376640⟩, ⟨.count 5, 5169487563076636800⟩, ⟨.count 6, 1443095163389880000⟩, ⟨.count 7, 398454609002650200⟩, ⟨.count 8, 114281475565420800⟩, ⟨.count 9, 36733331431742400⟩, ⟨.count 11, 11224073493032400⟩, ⟨.count 12, 9620634422599200⟩, ⟨.path 9, 18247791676514400⟩, ⟨.privateRow 2 20, 15758599184217489600⟩, ⟨.privateRow 5 14, 1092262694779095840⟩, ⟨.privateRow 6 11, 12560272718393400⟩, ⟨.privateRow 6 12, 371997864340502400⟩, ⟨.privateRow 6 13, 1128019386049756200⟩, ⟨.privateRow 7 9, 5382974022168600⟩, ⟨.privateRow 7 10, 129344085014944800⟩, ⟨.privateRow 7 11, 428599263526794360⟩, ⟨.privateRow 7 12, 824167682202664800⟩, ⟨.privateRow 8 7, 382638869080650⟩, ⟨.privateRow 8 8, 43438622089917600⟩, ⟨.privateRow 8 9, 166065269181002100⟩, ⟨.privateRow 8 10, 356007203792636760⟩, ⟨.privateRow 8 11, 523449972902329200⟩, ⟨.privateRow 9 6, 11479166072419500⟩, ⟨.privateRow 9 7, 64312483443193440⟩, ⟨.privateRow 9 8, 159653942352406320⟩, ⟨.privateRow 9 9, 267663541699296288⟩, ⟨.privateRow 9 10, 321824798154765360⟩, ⟨.privateRow 10 3, 938740692144528⟩, ⟨.privateRow 10 4, 725596670256640⟩, ⟨.privateRow 10 5, 22397128470187380⟩, ⟨.privateRow 10 6, 73874810990504160⟩, ⟨.privateRow 10 7, 142579745705429760⟩, ⟨.privateRow 10 8, 86853921429719808⟩, ⟨.privateRow 11 3, 4875102628286800⟩, ⟨.privateRow 11 4, 33098262175476225⟩, ⟨.privateRow 11 5, 79224466798222200⟩, ⟨.privateRow 12 2, 11045913596317600⟩, ⟨.privateRow 12 3, 28461043500189300⟩, ⟨.privateRow 13 1, 11402233389747200⟩, ⟨.privateRow 14 0, 2779294388750880⟩, ⟨.hall 7 11, 2506915315888830⟩, ⟨.hall 7 12, 13937585766073200⟩, ⟨.hall 6 13, 27350089287103440⟩, ⟨.hall 8 13, 57140737782710400⟩, ⟨.hall 6 14, 212134989018312360⟩, ⟨.hall 5 15, 780067212769169325⟩, ⟨.hall 4 16, 1274687949021126640⟩, ⟨.hall 3 17, 1705517658623278500⟩, ⟨.hall 2 19, 28132017802936407360⟩, ⟨.assumptionRow 14, 9344237408010540⟩]
  caps := #[0, 0, 0, 0, 15935704688177820, 0, 1459362473875020, 0, 0, 1852469981426064, 0, 1028844088859650, 3862024334483000, 10642807592249280, 0, 42872702418000000, 0, 0, 0] }

theorem case_40_22_14_checked :
    (Witness.linear .conditional case_40_22_14).check 40 22 14 = true := by
  change case_40_22_14.check 40 22 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_23_1_checked :
    (Witness.rising).check 40 23 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_23_2_checked :
    (Witness.rising).check 40 23 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_23_3_checked :
    (Witness.rising).check 40 23 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_23_4_checked :
    (Witness.rising).check 40 23 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_23_5_checked :
    (Witness.rising).check 40 23 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_23_6_checked :
    (Witness.rising).check 40 23 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_23_7_checked :
    (Witness.rising).check 40 23 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_23_8_checked :
    (Witness.rising).check 40 23 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_23_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_40_23_9_checked :
    (Witness.linear .positive case_40_23_9).check 40 23 9 = true := by
  change case_40_23_9.check 40 23 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_23_10 : Certificate := {
  objectiveScale := 35135100000
  eta := 1418488873401600
  rows := #[⟨.count 2, 255480522897600⟩, ⟨.count 3, 46520334020160⟩, ⟨.count 4, 9042594200640⟩, ⟨.count 5, 1885619736000⟩, ⟨.count 6, 429502273200⟩, ⟨.count 7, 119993983200⟩, ⟨.count 8, 42664527360⟩, ⟨.count 9, 37331461440⟩, ⟨.path 10, 9582847560⟩, ⟨.path 11, 4471346880⟩, ⟨.privateRow 3 20, 3686037395040⟩, ⟨.privateRow 5 14, 202808878272⟩, ⟨.privateRow 5 15, 273414861720⟩, ⟨.privateRow 5 16, 236051655840⟩, ⟨.privateRow 6 13, 412042831200⟩, ⟨.privateRow 7 12, 13713598080⟩, ⟨.privateRow 8 8, 30915116505⟩, ⟨.privateRow 9 6, 1448487040⟩, ⟨.privateRow 10 4, 666633240⟩, ⟨.privateRow 10 10, 166658310⟩, ⟨.privateRow 11 0, 366282000⟩, ⟨.hall 11 1, 581981400⟩, ⟨.hall 12 8, 169303680⟩, ⟨.hall 13 8, 1210521312⟩, ⟨.hall 5 11, 138065400⟩, ⟨.hall 4 15, 3425672250⟩, ⟨.hall 3 18, 278961450768⟩]
  caps := #[0, 0, 382611200400, 80413201440, 43578767232, 0, 0, 322948080, 2053420200, 0, 1469795760, 0, 6983776800, 9904265280, 0, 0, 0, 0] }

theorem case_40_23_10_checked :
    (Witness.linear .positive case_40_23_10).check 40 23 10 = true := by
  change case_40_23_10.check 40 23 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_23_11 : Certificate := {
  objectiveScale := 11954800000
  eta := 595923501613440
  rows := #[⟨.count 2, 139193810595840⟩, ⟨.count 3, 31318607384064⟩, ⟨.count 4, 7487881328928⟩, ⟨.count 5, 1816402748160⟩, ⟨.count 6, 466050705120⟩, ⟨.count 7, 129277468320⟩, ⟨.count 8, 39543696192⟩, ⟨.count 9, 15209113920⟩, ⟨.count 10, 11406835440⟩, ⟨.path 11, 3678114440⟩, ⟨.privateRow 10 11, 10266151896⟩, ⟨.hall 10 4, 56977200⟩, ⟨.hall 7 8, 166848234⟩, ⟨.hall 7 9, 11015592⟩, ⟨.hall 9 10, 88884432⟩, ⟨.hall 6 11, 312767455⟩]
  caps := #[0, 0, 0, 0, 6798229152, 4141394400, 0, 0, 0, 1260611352, 648748640, 0, 0, 0, 0, 0, 0, 0] }

theorem case_40_23_11_checked :
    (Witness.linear .positive case_40_23_11).check 40 23 11 = true := by
  change case_40_23_11.check 40 23 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_23_12 : Certificate := {
  objectiveScale := 18104625000
  eta := 1015990537161600
  rows := #[⟨.count 2, 228364845508800⟩, ⟨.count 3, 51964653620880⟩, ⟨.count 4, 13648627792800⟩, ⟨.count 5, 3636219787200⟩, ⟨.count 6, 1037090854800⟩, ⟨.count 7, 342205063200⟩, ⟨.count 8, 123845641920⟩, ⟨.count 9, 52145533440⟩, ⟨.count 10, 48886437600⟩, ⟨.path 11, 5760955200⟩, ⟨.privateRow 4 17, 1714400808120⟩, ⟨.privateRow 5 14, 190517431104⟩, ⟨.privateRow 5 15, 669627798840⟩, ⟨.privateRow 5 16, 1382787806400⟩, ⟨.privateRow 6 12, 142617775300⟩, ⟨.privateRow 6 13, 303445101960⟩, ⟨.privateRow 6 14, 566558892900⟩, ⟨.privateRow 6 15, 689259971400⟩, ⟨.privateRow 7 9, 3200897700⟩, ⟨.privateRow 7 10, 75823862400⟩, ⟨.privateRow 7 11, 148793244600⟩, ⟨.privateRow 7 12, 129199870800⟩, ⟨.privateRow 7 13, 551136385800⟩, ⟨.privateRow 7 14, 41126685600⟩, ⟨.privateRow 8 7, 5793948160⟩, ⟨.privateRow 8 8, 35951900985⟩, ⟨.privateRow 8 9, 74842808040⟩, ⟨.privateRow 8 10, 126833146440⟩, ⟨.privateRow 8 11, 85551265800⟩, ⟨.privateRow 9 5, 4924855936⟩, ⟨.privateRow 9 6, 19554575040⟩, ⟨.privateRow 9 7, 38022784800⟩, ⟨.privateRow 9 8, 42213050880⟩, ⟨.privateRow 10 3, 3629447640⟩, ⟨.privateRow 10 4, 12466041588⟩, ⟨.privateRow 10 5, 12764792040⟩, ⟨.privateRow 11 0, 2596532400⟩, ⟨.privateRow 11 1, 193993800⟩, ⟨.privateRow 11 2, 3915147600⟩, ⟨.privateRow 12 0, 1778276500⟩, ⟨.privateRow 13 0, 1862340480⟩, ⟨.hall 5 17, 1068388521200⟩, ⟨.hall 4 18, 3619777281120⟩, ⟨.hall 3 19, 7550021422944⟩, ⟨.hall 2 20, 8544262927200⟩, ⟨.assumptionRow 12, 27984439560⟩]
  caps := #[0, 0, 0, 134010917040, 10231773552, 3775214520, 0, 0, 1267607880, 14237070848, 3034683960, 30341640, 18979762340, 0, 0, 0, 0, 0] }

theorem case_40_23_12_checked :
    (Witness.linear .conditional case_40_23_12).check 40 23 12 = true := by
  change case_40_23_12.check 40 23 12 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_23_13 : Certificate := {
  objectiveScale := 23740500000
  eta := 1071916621776000
  rows := #[⟨.count 2, 247006873713600⟩, ⟨.count 3, 63848946601440⟩, ⟨.count 4, 16844404056480⟩, ⟨.count 5, 4558078324800⟩, ⟨.count 6, 1280359080000⟩, ⟨.count 7, 391091500800⟩, ⟨.count 8, 130363833600⟩, ⟨.count 9, 52145533440⟩, ⟨.count 10, 24443218800⟩, ⟨.count 11, 25607181600⟩, ⟨.path 9, 9739449720⟩, ⟨.privateRow 2 21, 16311774679200⟩, ⟨.privateRow 4 16, 628336218510⟩, ⟨.privateRow 4 17, 3312288939960⟩, ⟨.privateRow 5 14, 430200650880⟩, ⟨.privateRow 5 15, 1303405543440⟩, ⟨.privateRow 5 16, 2743382722080⟩, ⟨.privateRow 6 12, 213037524700⟩, ⟨.privateRow 6 13, 547140113520⟩, ⟨.privateRow 6 14, 1125115541550⟩, ⟨.privateRow 6 15, 1519359441600⟩, ⟨.privateRow 7 10, 93283304400⟩, ⟨.privateRow 7 11, 239776336800⟩, ⟨.privateRow 7 12, 492123471840⟩, ⟨.privateRow 7 13, 683246163600⟩, ⟨.privateRow 7 14, 676262386800⟩, ⟨.privateRow 8 8, 38498069610⟩, ⟨.privateRow 8 9, 108364936680⟩, ⟨.privateRow 8 10, 171509918580⟩, ⟨.privateRow 8 11, 455132734056⟩, ⟨.privateRow 8 12, 136678331790⟩, ⟨.privateRow 9 6, 15209113920⟩, ⟨.privateRow 9 7, 50515985520⟩, ⟨.privateRow 9 8, 117120523520⟩, ⟨.privateRow 9 9, 143038095200⟩, ⟨.privateRow 10 4, 5540462928⟩, ⟨.privateRow 10 5, 10411000600⟩, ⟨.privateRow 10 6, 92069457480⟩, ⟨.privateRow 11 2, 1163962800⟩, ⟨.privateRow 11 3, 12687194520⟩, ⟨.privateRow 11 4, 17847429600⟩, ⟨.privateRow 12 0, 1778276500⟩, ⟨.privateRow 12 1, 4073869800⟩, ⟨.privateRow 12 2, 1707145440⟩, ⟨.privateRow 13 0, 1396755360⟩, ⟨.hall 5 16, 19414595200⟩, ⟨.hall 6 16, 368291523600⟩, ⟨.hall 5 17, 2816789976000⟩, ⟨.hall 4 18, 8483524489440⟩, ⟨.hall 3 19, 17022502004508⟩, ⟨.hall 2 20, 25077966513600⟩, ⟨.assumptionRow 13, 21091888125⟩]
  caps := #[0, 2780917063050, 212828834400, 166437862500, 2713796085, 4164930770, 29671692050, 0, 0, 6906474575, 0, 4990402725, 0, 9597659715, 23740500000, 0, 0, 0] }

theorem case_40_23_13_checked :
    (Witness.linear .conditional case_40_23_13).check 40 23 13 = true := by
  change case_40_23_13.check 40 23 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_23_14 : Certificate := {
  objectiveScale := 10342724792400000
  eta := 659080042896292617600
  rows := #[⟨.count 2, 140753717648055111600⟩, ⟨.count 3, 33258005854637644080⟩, ⟨.count 4, 7782494971469137920⟩, ⟨.count 5, 1797296658074517600⟩, ⟨.count 6, 410906113277259600⟩, ⟨.count 7, 93539603022465600⟩, ⟨.count 8, 20408640659447040⟩, ⟨.count 9, 3401440109907840⟩, ⟨.count 10, 4251800137384800⟩, ⟨.count 11, 3340700107945200⟩, ⟨.count 12, 6681400215890400⟩, ⟨.path 8, 10146408058987200⟩, ⟨.privateRow 2 21, 8664105729955876200⟩, ⟨.privateRow 4 16, 338746990945643280⟩, ⟨.privateRow 4 17, 1699525501581988080⟩, ⟨.privateRow 5 14, 214339318925764032⟩, ⟨.privateRow 5 15, 638741860639122240⟩, ⟨.privateRow 5 16, 1448082140123979360⟩, ⟨.privateRow 6 12, 94931561400776100⟩, ⟨.privateRow 6 13, 253113711511981320⟩, ⟨.privateRow 6 14, 571677305972122350⟩, ⟨.privateRow 6 15, 870252378119724600⟩, ⟨.privateRow 7 10, 35489515432456800⟩, ⟨.privateRow 7 11, 102144436633839600⟩, ⟨.privateRow 7 12, 238283027699436720⟩, ⟨.privateRow 7 13, 381523137327832500⟩, ⟨.privateRow 7 14, 452513014621668000⟩, ⟨.privateRow 8 8, 11453286620080305⟩, ⟨.privateRow 8 9, 40817281318894080⟩, ⟨.privateRow 8 10, 104736010050912240⟩, ⟨.privateRow 8 11, 120751123901728320⟩, ⟨.privateRow 8 12, 350932953839397930⟩, ⟨.privateRow 8 13, 25723390831178040⟩, ⟨.privateRow 9 6, 2813536881034880⟩, ⟨.privateRow 9 7, 15637176060826320⟩, ⟨.privateRow 9 8, 47836125990132480⟩, ⟨.privateRow 9 9, 92468779284161280⟩, ⟨.privateRow 9 10, 98339412955335552⟩, ⟨.privateRow 10 4, 63777002060772⟩, ⟨.privateRow 10 5, 5291129059856640⟩, ⟨.privateRow 10 6, 22109360714400960⟩, ⟨.privateRow 10 7, 50960861646654960⟩, ⟨.privateRow 10 8, 19558280631970080⟩, ⟨.privateRow 11 3, 364440011775840⟩, ⟨.privateRow 11 4, 9752144759557200⟩, ⟨.privateRow 11 5, 24296000785056000⟩, ⟨.privateRow 12 2, 1614671718840180⟩, ⟨.privateRow 12 3, 9465316972511400⟩, ⟨.privateRow 13 1, 2939816094991776⟩, ⟨.privateRow 14 0, 434291014032876⟩, ⟨.hall 6 16, 575582977421852400⟩, ⟨.hall 5 17, 2191870459712934000⟩, ⟨.hall 4 18, 5067947559545750880⟩, ⟨.hall 3 19, 9509236043263852896⟩, ⟨.hall 2 20, 13665690574901164800⟩, ⟨.assumptionRow 14, 4207200835244400⟩]
  caps := #[0, 393357265235272800, 74843683816192200, 22968379091352240, 5032062041662656, 0, 1151413971557850, 253642888132920, 585800898928245, 2649785661739216, 0, 1534162807900800, 0, 4207200835244400, 23379638721780348, 10342724792400000, 0, 0] }

theorem case_40_23_14_checked :
    (Witness.linear .conditional case_40_23_14).check 40 23 14 = true := by
  change case_40_23_14.check 40 23 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_24_1_checked :
    (Witness.rising).check 40 24 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_24_2_checked :
    (Witness.rising).check 40 24 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_24_3_checked :
    (Witness.rising).check 40 24 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_24_4_checked :
    (Witness.rising).check 40 24 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_24_5_checked :
    (Witness.rising).check 40 24 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_24_6_checked :
    (Witness.rising).check 40 24 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_24_7_checked :
    (Witness.rising).check 40 24 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_24_8_checked :
    (Witness.rising).check 40 24 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_24_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_40_24_9_checked :
    (Witness.linear .positive case_40_24_9).check 40 24 9 = true := by
  change case_40_24_9.check 40 24 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_24_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_40_24_10_checked :
    (Witness.linear .positive case_40_24_10).check 40 24 10 = true := by
  change case_40_24_10.check 40 24 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_24_11 : Certificate := {
  objectiveScale := 3963960000
  eta := 394977972589200
  rows := #[⟨.count 2, 83190050863920⟩, ⟨.count 3, 19274525590320⟩, ⟨.count 4, 4255913581920⟩, ⟨.count 5, 1043492650200⟩, ⟨.count 6, 251415964800⟩, ⟨.count 7, 68441012640⟩, ⟨.count 8, 19554575040⟩, ⟨.count 9, 7332965640⟩, ⟨.count 10, 6983776800⟩, ⟨.path 10, 1981980000⟩, ⟨.hall 8 8, 83883100⟩, ⟨.hall 7 9, 68422914⟩, ⟨.hall 6 12, 255690600⟩, ⟨.hall 7 12, 104361642⟩, ⟨.hall 5 13, 242359975⟩]
  caps := #[0, 0, 33289336080, 0, 0, 2992789800, 551350800, 1135974840, 265224960, 594954360, 0, 0, 0, 0, 0, 0, 0] }

theorem case_40_24_11_checked :
    (Witness.linear .positive case_40_24_11).check 40 24 11 = true := by
  change case_40_24_11.check 40 24 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_24_12 : Certificate := {
  objectiveScale := 5082000000
  eta := 681599156238000
  rows := #[⟨.count 2, 144941769292320⟩, ⟨.count 3, 34554330851040⟩, ⟨.count 4, 7989440659200⟩, ⟨.count 5, 2112592482000⟩, ⟨.count 6, 565685920800⟩, ⟨.count 7, 161325244080⟩, ⟨.count 8, 56490994560⟩, ⟨.count 9, 24443218800⟩, ⟨.count 10, 13967553600⟩, ⟨.path 10, 3049078032⟩, ⟨.privateRow 7 14, 447136309620⟩, ⟨.privateRow 8 7, 814773960⟩, ⟨.privateRow 8 11, 105105840840⟩, ⟨.privateRow 9 5, 1580167680⟩, ⟨.privateRow 9 12, 75502386960⟩, ⟨.privateRow 10 3, 1687746060⟩, ⟨.privateRow 10 10, 4469617152⟩, ⟨.privateRow 10 11, 11174042880⟩, ⟨.privateRow 10 12, 4423058640⟩, ⟨.privateRow 10 13, 7332965640⟩, ⟨.privateRow 11 0, 332560800⟩, ⟨.privateRow 11 1, 1343034000⟩, ⟨.privateRow 11 11, 4655851200⟩, ⟨.privateRow 12 0, 393956640⟩, ⟨.privateRow 12 6, 365816880⟩, ⟨.privateRow 12 8, 3585005424⟩, ⟨.privateRow 13 0, 640179540⟩, ⟨.hall 7 9, 74732301⟩, ⟨.hall 6 12, 207035400⟩, ⟨.hall 5 13, 499191550⟩, ⟨.hall 10 13, 498841200⟩, ⟨.hall 4 16, 6172678512⟩, ⟨.assumptionRow 12, 9147388250⟩]
  caps := #[0, 0, 156374522304, 35454715296, 21552711180, 4097149056, 1430772420, 4248123880, 0, 0, 5063188130, 9836347730, 0, 0, 0, 0, 0] }

theorem case_40_24_12_checked :
    (Witness.linear .conditional case_40_24_12).check 40 24 12 = true := by
  change case_40_24_12.check 40 24 12 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_24_13 : Certificate := {
  objectiveScale := 233170014000000
  eta := 35932093414497680400
  rows := #[⟨.count 2, 7056431781658459200⟩, ⟨.count 3, 1535967669767010480⟩, ⟨.count 4, 330578932512628800⟩, ⟨.count 5, 77033053718220600⟩, ⟨.count 6, 18087231155994000⟩, ⟨.count 7, 4285282458497040⟩, ⟨.count 8, 1211999079170880⟩, ⟨.count 9, 389571132590640⟩, ⟨.count 10, 278265094707600⟩, ⟨.path 8, 336742818572160⟩, ⟨.privateRow 2 22, 120702122580999960⟩, ⟨.privateRow 3 20, 163810023502785660⟩, ⟨.privateRow 4 17, 25558648948893060⟩, ⟨.privateRow 4 18, 66932030780334720⟩, ⟨.privateRow 4 19, 116008717983598440⟩, ⟨.privateRow 5 14, 1156346060229360⟩, ⟨.privateRow 5 15, 15998387845055616⟩, ⟨.privateRow 5 16, 28262458119135240⟩, ⟨.privateRow 5 17, 50267043441735120⟩, ⟨.privateRow 5 18, 51015267363060000⟩, ⟨.privateRow 6 12, 1768970959212600⟩, ⟨.privateRow 6 13, 6809765234372100⟩, ⟨.privateRow 6 14, 12781643350235760⟩, ⟨.privateRow 6 15, 21333657260916000⟩, ⟨.privateRow 6 16, 24085389864135600⟩, ⟨.privateRow 6 17, 15188636419456500⟩, ⟨.privateRow 7 10, 1165235084088075⟩, ⟨.privateRow 7 11, 3108618629447760⟩, ⟨.privateRow 7 12, 5671970180456580⟩, ⟨.privateRow 7 13, 9995282201896992⟩, ⟨.privateRow 7 14, 11429738765114670⟩, ⟨.privateRow 7 15, 361744623119880⟩, ⟨.privateRow 8 8, 596380499274560⟩, ⟨.privateRow 8 9, 1577222015974605⟩, ⟨.privateRow 8 10, 1113060378830400⟩, ⟨.privateRow 8 11, 8292815128017420⟩, ⟨.privateRow 8 12, 268371224673552⟩, ⟨.privateRow 9 6, 270535508743500⟩, ⟨.privateRow 9 7, 856094587668320⟩, ⟨.privateRow 9 8, 1579927371062040⟩, ⟨.privateRow 9 9, 1357315295295960⟩, ⟨.privateRow 10 4, 111306037883040⟩, ⟨.privateRow 10 5, 484181264791224⟩, ⟨.privateRow 10 6, 667836227298240⟩, ⟨.privateRow 11 2, 38647929820500⟩, ⟨.privateRow 11 3, 286697370304800⟩, ⟨.privateRow 11 4, 18551006313840⟩, ⟨.privateRow 12 1, 85025445605100⟩, ⟨.privateRow 13 0, 25507633681530⟩, ⟨.hall 5 18, 2658163931022600⟩, ⟨.hall 4 19, 39730690222351128⟩, ⟨.hall 3 20, 108764550018043920⟩, ⟨.hall 2 21, 203421059734412520⟩, ⟨.assumptionRow 13, 226120302708300⟩]
  caps := #[0, 0, 10361432106065040, 0, 1071526364448540, 86342422019700, 0, 196694985817902, 47706105766319, 55619761534260, 0, 509513798948700, 141094857103200, 0, 233170014000000, 0, 0] }

theorem case_40_24_13_checked :
    (Witness.linear .conditional case_40_24_13).check 40 24 13 = true := by
  change case_40_24_13.check 40 24 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_24_14 : Certificate := {
  objectiveScale := 22915548347441400000
  eta := 2381894044781162765653800
  rows := #[⟨.count 2, 503463891739697280231840⟩, ⟨.count 3, 101284553265897508907400⟩, ⟨.count 4, 22200313490260681295520⟩, ⟨.count 5, 4727196090197463682800⟩, ⟨.count 6, 1002738564587340781200⟩, ⟨.count 7, 211689252523994164920⟩, ⟨.count 8, 49517953806782260800⟩, ⟨.count 9, 11141539606526008680⟩, ⟨.count 10, 15916485152180012400⟩, ⟨.path 7, 36565146504957470400⟩, ⟨.path 8, 10847233731540286080⟩, ⟨.privateRow 2 22, 60543126221862331167120⟩, ⟨.privateRow 3 19, 7005198815144471901960⟩, ⟨.privateRow 3 20, 19953436336277936211720⟩, ⟨.privateRow 4 17, 4398918583933750927050⟩, ⟨.privateRow 4 18, 8158790289007474356240⟩, ⟨.privateRow 4 19, 14102801669089099987020⟩, ⟨.privateRow 5 14, 255813286362537643740⟩, ⟨.privateRow 5 15, 1702957801382246793384⟩, ⟨.privateRow 5 16, 3323627374527722922660⟩, ⟨.privateRow 5 17, 6114229346292439652280⟩, ⟨.privateRow 5 18, 6769811684727231940800⟩, ⟨.privateRow 6 12, 174323408809590612000⟩, ⟨.privateRow 6 13, 653902265002062176100⟩, ⟨.privateRow 6 14, 1342290247833847712400⟩, ⟨.privateRow 6 15, 2575817847127798673400⟩, ⟨.privateRow 6 16, 3285869934750051448800⟩, ⟨.privateRow 6 17, 2602345322381432027400⟩, ⟨.privateRow 7 10, 78985557567693311535⟩, ⟨.privateRow 7 11, 270125490868426496160⟩, ⟨.privateRow 7 12, 562913024882099771880⟩, ⟨.privateRow 7 13, 1138665347786958087096⟩, ⟨.privateRow 7 14, 1569365436004949222640⟩, ⟨.privateRow 7 15, 1214427817111334946120⟩, ⟨.privateRow 8 8, 28060173823843281120⟩, ⟨.privateRow 8 9, 116831422262876896575⟩, ⟨.privateRow 8 10, 256962810290195089080⟩, ⟨.privateRow 8 11, 540983645339096199240⟩, ⟨.privateRow 8 12, 817046237811907303200⟩, ⟨.privateRow 8 13, 175479248802784636710⟩, ⟨.privateRow 9 6, 7180103301983427816⟩, ⟨.privateRow 9 7, 50068153293524285920⟩, ⟨.privateRow 9 8, 127663474658110516125⟩, ⟨.privateRow 9 9, 287027282244312890280⟩, ⟨.privateRow 9 10, 278951139778206735840⟩, ⟨.privateRow 10 5, 19418111885659615128⟩, ⟨.privateRow 10 6, 66495537969107607360⟩, ⟨.privateRow 10 7, 171301171450337383455⟩, ⟨.privateRow 10 8, 13187944840377724560⟩, ⟨.privateRow 11 3, 2893906391305456800⟩, ⟨.privateRow 11 4, 33689893572114359580⟩, ⟨.privateRow 11 5, 55707698032630043400⟩, ⟨.privateRow 12 2, 7958242576090006200⟩, ⟨.privateRow 12 3, 20426155945297682580⟩, ⟨.privateRow 13 1, 6366594060872004960⟩, ⟨.hall 5 18, 1251677977099068519000⟩, ⟨.hall 4 19, 6075322382587110733080⟩, ⟨.hall 3 20, 14685989264343619536600⟩, ⟨.hall 2 21, 28147242892620206595240⟩, ⟨.assumptionRow 14, 12586213371972748200⟩]
  caps := #[0, 4210607018476113014760, 695633390399977592640, 71465539296452978040, 102514750489305474450, 7460863147082351292, 8190416273843000340, 2969192840650758120, 2318130290923562115, 4671378583443740168, 5702057275328255127, 23650907081447919000, 12586213371972748200, 48398171593461468240, 193653721754999851800, 22915548347441400000, 0] }

theorem case_40_24_14_checked :
    (Witness.linear .conditional case_40_24_14).check 40 24 14 = true := by
  change case_40_24_14.check 40 24 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_24_15 : Certificate := {
  objectiveScale := 1986858720000
  eta := 211626051871033800
  rows := #[⟨.count 2, 47702852947910160⟩, ⟨.count 3, 10818551530626840⟩, ⟨.count 4, 2502845929584000⟩, ⟨.count 5, 590949733374000⟩, ⟨.count 6, 149791536694800⟩, ⟨.count 7, 37163469863520⟩, ⟨.count 8, 8258548858560⟩, ⟨.count 9, 1327266780840⟩, ⟨.path 5, 8670358897200⟩, ⟨.path 9, 1390585269645⟩, ⟨.privateRow 5 15, 111515690862576⟩, ⟨.privateRow 5 16, 267144041234070⟩, ⟨.privateRow 6 14, 225635352742800⟩, ⟨.privateRow 6 15, 209123521957350⟩, ⟨.privateRow 6 17, 682436336481900⟩, ⟨.privateRow 7 10, 687334582935⟩, ⟨.privateRow 7 11, 13516451502840⟩, ⟨.privateRow 7 13, 232612983819216⟩, ⟨.privateRow 7 14, 134954590180410⟩, ⟨.privateRow 7 15, 97964929062000⟩, ⟨.privateRow 8 8, 458808269920⟩, ⟨.privateRow 8 9, 6064871818005⟩, ⟨.privateRow 8 13, 366362500033530⟩, ⟨.privateRow 9 6, 191716312788⟩, ⟨.privateRow 9 7, 2294041349600⟩, ⟨.privateRow 9 11, 6400375365384⟩, ⟨.privateRow 9 12, 195145085305170⟩, ⟨.privateRow 10 5, 549867666348⟩, ⟨.privateRow 10 7, 6825943444320⟩, ⟨.privateRow 10 9, 505625440320⟩, ⟨.privateRow 10 11, 52000416377910⟩, ⟨.privateRow 11 4, 853242930540⟩, ⟨.privateRow 13 6, 3476174902200⟩, ⟨.privateRow 13 11, 12514229647920⟩, ⟨.hall 11 3, 29170698480⟩, ⟨.hall 10 4, 79240750200⟩, ⟨.hall 9 5, 54426714480⟩, ⟨.hall 10 5, 62035089300⟩, ⟨.hall 11 5, 63743378160⟩, ⟨.hall 13 5, 19562889060⟩, ⟨.hall 5 14, 168188510490⟩, ⟨.hall 6 14, 423678179925⟩, ⟨.hall 4 16, 2317736925504⟩, ⟨.hall 3 18, 33508757858004⟩, ⟨.hall 2 20, 324822209952240⟩]
  caps := #[0, 19212269249250, 0, 5584899446280, 0, 0, 332767118970, 0, 1782079621465, 63318488805, 0, 1602372528900, 0, 3726850244040, 24399869376960, 15894869760000, 1986858720000] }

theorem case_40_24_15_checked :
    (Witness.linear .negative case_40_24_15).check 40 24 15 = true := by
  change case_40_24_15.check 40 24 15 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_25_1_checked :
    (Witness.rising).check 40 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_25_2_checked :
    (Witness.rising).check 40 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_25_3_checked :
    (Witness.rising).check 40 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_25_4_checked :
    (Witness.rising).check 40 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_25_5_checked :
    (Witness.rising).check 40 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_25_6_checked :
    (Witness.rising).check 40 25 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_25_7_checked :
    (Witness.rising).check 40 25 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_25_8_checked :
    (Witness.rising).check 40 25 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_25_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_40_25_9_checked :
    (Witness.linear .positive case_40_25_9).check 40 25 9 = true := by
  change case_40_25_9.check 40 25 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_25_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_40_25_10_checked :
    (Witness.linear .positive case_40_25_10).check 40 25 10 = true := by
  change case_40_25_10.check 40 25 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_25_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_40_25_11_checked :
    (Witness.linear .positive case_40_25_11).check 40 25 11 = true := by
  change case_40_25_11.check 40 25 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_25_12 : Certificate := {
  objectiveScale := 83677000
  eta := 23640887602332
  rows := #[⟨.count 2, 5084877911256⟩, ⟨.count 3, 1035511159023⟩, ⟨.count 4, 228410847621⟩, ⟨.count 5, 47765265840⟩, ⟨.count 6, 10946206755⟩, ⟨.count 7, 2476717488⟩, ⟨.count 8, 619179372⟩, ⟨.count 9, 199021941⟩, ⟨.path 8, 167358555⟩]
  caps := #[0, 0, 0, 103579317, 33579954, 99280890, 99362220, 33628952, 0, 0, 83677000, 83677000, 0, 0, 0, 0] }

theorem case_40_25_12_checked :
    (Witness.linear .positive case_40_25_12).check 40 25 12 = true := by
  change case_40_25_12.check 40 25 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_25_13 : Certificate := {
  objectiveScale := 7199801635118400000
  eta := 1428375794354202721547520
  rows := #[⟨.count 2, 283600036651439765537280⟩, ⟨.count 3, 58462577911964248102080⟩, ⟨.count 4, 11971858958081415993600⟩, ⟨.count 5, 2720877035927594544000⟩, ⟨.count 6, 616732128143588096640⟩, ⟨.count 7, 141082512974023420800⟩, ⟨.count 8, 42324753892207026240⟩, ⟨.count 9, 18139180239517296960⟩, ⟨.path 7, 6097020329701501200⟩, ⟨.path 8, 9431393102795664000⟩, ⟨.privateRow 2 23, 28965247645802537028960⟩, ⟨.privateRow 3 20, 5476016967863166204480⟩, ⟨.privateRow 3 21, 10076314623051858461280⟩, ⟨.privateRow 4 17, 701683955598660770736⟩, ⟨.privateRow 4 18, 2893199248203008865120⟩, ⟨.privateRow 4 19, 4278831072055024605120⟩, ⟨.privateRow 4 20, 6168832879789174074480⟩, ⟨.privateRow 5 15, 614716663672530619200⟩, ⟨.privateRow 5 16, 1203232289221314031680⟩, ⟨.privateRow 5 17, 1818452819011609020240⟩, ⟨.privateRow 5 18, 2682583210977502472640⟩, ⟨.privateRow 5 19, 2149492858382799689760⟩, ⟨.privateRow 6 12, 45347950598793242400⟩, ⟨.privateRow 6 13, 305342867365207832160⟩, ⟨.privateRow 6 14, 552237265069748818560⟩, ⟨.privateRow 6 15, 789658979760319660992⟩, ⟨.privateRow 6 16, 1185093108981796734720⟩, ⟨.privateRow 6 17, 778977018063715030560⟩, ⟨.privateRow 7 10, 40981110911502041280⟩, ⟨.privateRow 7 11, 145365374975020560360⟩, ⟨.privateRow 7 12, 272087703592759454400⟩, ⟨.privateRow 7 13, 386297356952683176000⟩, ⟨.privateRow 7 14, 509509418283330296832⟩, ⟨.privateRow 8 8, 26276618041411862124⟩, ⟨.privateRow 8 9, 77399434201026737800⟩, ⟨.privateRow 8 10, 146152665784027387485⟩, ⟨.privateRow 8 11, 216662430638678824800⟩, ⟨.privateRow 8 12, 7054125648701171040⟩, ⟨.privateRow 9 6, 15207595554342784320⟩, ⟨.privateRow 9 7, 47564961516956467584⟩, ⟨.privateRow 9 8, 90919841694370648960⟩, ⟨.privateRow 10 4, 8565724001994279120⟩, ⟨.privateRow 10 5, 33255163772448377760⟩, ⟨.privateRow 10 6, 3627836047903459392⟩, ⟨.privateRow 11 2, 5116179041915135040⟩, ⟨.privateRow 11 3, 7054125648701171040⟩, ⟨.privateRow 12 0, 2375368840889169840⟩, ⟨.hall 4 20, 718944969175788738240⟩, ⟨.hall 3 21, 4035967603292598573600⟩, ⟨.hall 2 22, 10450796684663342367360⟩, ⟨.assumptionRow 13, 7502769287924182272⟩]
  caps := #[0, 3703916589592921865856, 194027027910891935760, 8749840902167212848, 0, 46046429202568560480, 4246138755484640784, 20379619945681476480, 0, 0, 41949428232968304048, 1655707525735456512, 5020966808006147856, 71695048698378217728, 7199801635118400000, 0] }

theorem case_40_25_13_checked :
    (Witness.linear .conditional case_40_25_13).check 40 25 13 = true := by
  change case_40_25_13.check 40 25 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_25_14 : Certificate := {
  objectiveScale := 444367933178400000
  eta := 113560224623945076257280
  rows := #[⟨.count 2, 20634376654726862227200⟩, ⟨.count 3, 3793003454038651332480⟩, ⟨.count 4, 670480408542185841600⟩, ⟨.count 5, 124393396761073440000⟩, ⟨.count 6, 22390811416993219200⟩, ⟨.count 7, 4063517627528399040⟩, ⟨.count 8, 1161005036436685440⟩, ⟨.path 6, 1748859880022695440⟩, ⟨.path 7, 1373303033207305200⟩, ⟨.privateRow 2 23, 2187955455630520736160⟩, ⟨.privateRow 3 20, 388604971481593426560⟩, ⟨.privateRow 3 21, 745738413582635272800⟩, ⟨.privateRow 4 17, 44744304814958116368⟩, ⟨.privateRow 4 18, 194473526661343189260⟩, ⟨.privateRow 4 19, 311750584516043552880⟩, ⟨.privateRow 4 20, 485414132510898831240⟩, ⟨.privateRow 5 15, 35161866817796759040⟩, ⟨.privateRow 5 16, 77472207502796538432⟩, ⟨.privateRow 5 17, 129306935933135840880⟩, ⟨.privateRow 5 18, 213210282048479876160⟩, ⟨.privateRow 5 19, 200646548975611458720⟩, ⟨.privateRow 6 12, 1632663332489088900⟩, ⟨.privateRow 6 13, 16188912064191129120⟩, ⟨.privateRow 6 14, 33710610522250902240⟩, ⟨.privateRow 6 15, 54832609292281172352⟩, ⟨.privateRow 6 16, 65088844855231677480⟩, ⟨.privateRow 6 17, 158891832129477807360⟩, ⟨.privateRow 7 10, 1142576385064674560⟩, ⟨.privateRow 7 11, 7028226917000649360⟩, ⟨.privateRow 7 12, 15661721001727532160⟩, ⟨.privateRow 7 13, 25818540572187242880⟩, ⟨.privateRow 7 14, 44516250254229481728⟩, ⟨.privateRow 7 15, 37981450477714423680⟩, ⟨.privateRow 8 8, 507939703441049880⟩, ⟨.privateRow 8 9, 3225013990101904000⟩, ⟨.privateRow 8 10, 7809572940406141905⟩, ⟨.privateRow 8 11, 12232017348172221600⟩, ⟨.privateRow 8 12, 27102211319318875740⟩, ⟨.privateRow 9 6, 158318868605002560⟩, ⟨.privateRow 9 7, 1575649692306930240⟩, ⟨.privateRow 9 8, 4312304421050545920⟩, ⟨.privateRow 9 9, 8168499720643822560⟩, ⟨.privateRow 9 10, 4809878008094839680⟩, ⟨.privateRow 10 5, 780285852410369760⟩, ⟨.privateRow 10 6, 2662018690686971616⟩, ⟨.privateRow 10 7, 3109834919026836000⟩, ⟨.privateRow 11 3, 290251259109171360⟩, ⟨.privateRow 11 4, 1764124535884314240⟩, ⟨.privateRow 12 1, 52627975552761840⟩, ⟨.privateRow 12 2, 513122761639427940⟩, ⟨.privateRow 13 0, 210511902211047360⟩, ⟨.hall 4 20, 97216401316320823680⟩, ⟨.hall 3 21, 355267541149625744640⟩, ⟨.hall 2 22, 825993788127746958720⟩, ⟨.assumptionRow 14, 295030683101579040⟩]
  caps := #[0, 44796060642722170320, 0, 6729270160819686480, 811484977378355280, 0, 0, 814977249215205648, 629688528109676035, 295030683101579040, 889477556834359584, 0, 5585116132541026620, 0, 4148648648682420960, 444367933178400000] }

theorem case_40_25_14_checked :
    (Witness.linear .conditional case_40_25_14).check 40 25 14 = true := by
  change case_40_25_14.check 40 25 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_25_15 : Certificate := {
  objectiveScale := 26379059572800000
  eta := 17752325502062505594240
  rows := #[⟨.count 2, 2489679990352849694400⟩, ⟨.count 3, 331233662995558202880⟩, ⟨.count 4, 38923056840770182080⟩, ⟨.count 5, 3383387773192627200⟩, ⟨.count 6, 84584694329815680⟩, ⟨.path 5, 2720898164785600800⟩, ⟨.path 6, 67773598931198160⟩, ⟨.privateRow 2 23, 228808646886678899040⟩, ⟨.privateRow 3 19, 6357949523791145280⟩, ⟨.privateRow 3 20, 46263128648724187200⟩, ⟨.privateRow 3 21, 73736707282016819040⟩, ⟨.privateRow 4 16, 1292266163372184000⟩, ⟨.privateRow 4 17, 8738303796722708208⟩, ⟨.privateRow 4 18, 19073848571373435840⟩, ⟨.privateRow 4 19, 29760889742461397520⟩, ⟨.privateRow 4 20, 46036982070134055000⟩, ⟨.privateRow 5 13, 170931569791502520⟩, ⟨.privateRow 5 14, 1375508243506288320⟩, ⟨.privateRow 5 15, 3984878932871316480⟩, ⟨.privateRow 5 16, 7325034528962037888⟩, ⟨.privateRow 5 17, 11693833991097017760⟩, ⟨.privateRow 5 18, 19769322724751920320⟩, ⟨.privateRow 5 19, 19151384541175766880⟩, ⟨.privateRow 6 10, 16916938865963136⟩, ⟨.privateRow 6 11, 160554280903816800⟩, ⟨.privateRow 6 12, 703110271616592840⟩, ⟨.privateRow 6 13, 1659471145899240960⟩, ⟨.privateRow 6 14, 3038000271345879840⟩, ⟨.privateRow 6 15, 4838244515665456896⟩, ⟨.privateRow 6 16, 8449658527322212200⟩, ⟨.privateRow 6 17, 9703744099503854400⟩, ⟨.privateRow 6 18, 3711153463720662960⟩, ⟨.privateRow 7 8, 12388667351336640⟩, ⟨.privateRow 7 9, 92103333825799296⟩, ⟨.privateRow 7 10, 331551116663166400⟩, ⟨.privateRow 7 11, 744815225070876960⟩, ⟨.privateRow 7 12, 1374165629310576960⟩, ⟨.privateRow 7 13, 2221131417771826560⟩, ⟨.privateRow 7 14, 3945406075517402496⟩, ⟨.privateRow 7 15, 4284449725289413680⟩, ⟨.privateRow 8 6, 7880865617534910⟩, ⟨.privateRow 8 7, 50836255683071040⟩, ⟨.privateRow 8 8, 166937292559261224⟩, ⟨.privateRow 8 9, 376454102541957440⟩, ⟨.privateRow 8 10, 702596302119797085⟩, ⟨.privateRow 8 11, 1155990822507480960⟩, ⟨.privateRow 8 12, 2101107302901046440⟩, ⟨.privateRow 8 13, 653769199924200360⟩, ⟨.privateRow 9 4, 5422095790372800⟩, ⟨.privateRow 9 5, 31327664566598400⟩, ⟨.privateRow 9 6, 96973361681152320⟩, ⟨.privateRow 9 7, 221799865131516672⟩, ⟨.privateRow 9 8, 421879216163525120⟩, ⟨.privateRow 9 9, 707809421301582600⟩, ⟨.privateRow 9 10, 514892544055306560⟩, ⟨.privateRow 10 2, 4531322910525840⟩, ⟨.privateRow 10 3, 23857221477640320⟩, ⟨.privateRow 10 4, 69312457853598960⟩, ⟨.privateRow 10 5, 159557491576697760⟩, ⟨.privateRow 10 6, 309439006756575696⟩, ⟨.privateRow 10 7, 154288747990497120⟩, ⟨.privateRow 11 0, 4699149684989760⟩, ⟨.privateRow 11 1, 22153134229237440⟩, ⟨.privateRow 11 2, 65065149484473600⟩, ⟨.privateRow 11 3, 146848427655930000⟩, ⟨.privateRow 11 4, 2563172555448960⟩, ⟨.privateRow 12 0, 77535969802331040⟩, ⟨.privateRow 13 0, 23857221477640320⟩, ⟨.hall 4 20, 9607075877412636480⟩, ⟨.hall 3 21, 34151070335663080800⟩, ⟨.hall 2 22, 81338603451767101440⟩]
  caps := #[0, 0, 949133123316568080, 0, 273299980896286344, 0, 42152044696373040, 12481065760499232, 0, 41635642132094656, 839133872319600, 0, 73900935393199200, 316791402221669760, 1160678621203200000, 237411536155200000] }

theorem case_40_25_15_checked :
    (Witness.linear .negative case_40_25_15).check 40 25 15 = true := by
  change case_40_25_15.check 40 25 15 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_25_16 : Certificate := {
  objectiveScale := 6440114973600000
  eta := 2322527477291782881120
  rows := #[⟨.count 2, 436972369187431677600⟩, ⟨.count 3, 76566839910718116960⟩, ⟨.count 4, 13504796161408712160⟩, ⟨.count 5, 2082237293609272800⟩, ⟨.count 6, 292054061960781120⟩, ⟨.count 7, 25239239922536640⟩, ⟨.path 6, 38636426608940160⟩, ⟨.path 7, 25759999439974800⟩, ⟨.privateRow 7 10, 3405294275262880⟩, ⟨.privateRow 7 11, 22985736358024440⟩, ⟨.privateRow 9 7, 901401425804880⟩, ⟨.privateRow 10 5, 245836752492240⟩, ⟨.privateRow 10 6, 1081681710965856⟩, ⟨.hall 10 5, 412429423595040⟩, ⟨.hall 11 5, 326881835731440⟩, ⟨.hall 9 6, 174922304657940⟩, ⟨.hall 12 6, 277354284863040⟩, ⟨.hall 13 7, 488259105644310⟩, ⟨.hall 9 8, 101486454233976⟩, ⟨.hall 7 9, 216632050805709⟩, ⟨.hall 8 9, 247171612686768⟩, ⟨.hall 6 11, 231656302362870⟩, ⟨.hall 5 14, 1147449596212920⟩]
  caps := #[0, 0, 0, 66533395381215840, 18788136958538640, 15341485977417600, 0, 884482899780480, 0, 9237271577133600, 0, 0, 63202552337770560, 2768605427150640, 125638199428637280, 225404024076000000] }

theorem case_40_25_16_checked :
    (Witness.linear .negative case_40_25_16).check 40 25 16 = true := by
  change case_40_25_16.check 40 25 16 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_26_1_checked :
    (Witness.rising).check 40 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_26_2_checked :
    (Witness.rising).check 40 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_26_3_checked :
    (Witness.rising).check 40 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_26_4_checked :
    (Witness.rising).check 40 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_26_5_checked :
    (Witness.rising).check 40 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_26_6_checked :
    (Witness.rising).check 40 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_26_7_checked :
    (Witness.rising).check 40 26 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_26_8_checked :
    (Witness.rising).check 40 26 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_26_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_40_26_9_checked :
    (Witness.linear .positive case_40_26_9).check 40 26 9 = true := by
  change case_40_26_9.check 40 26 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_26_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_40_26_10_checked :
    (Witness.linear .positive case_40_26_10).check 40 26 10 = true := by
  change case_40_26_10.check 40 26 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_26_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_40_26_11_checked :
    (Witness.linear .positive case_40_26_11).check 40 26 11 = true := by
  change case_40_26_11.check 40 26 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_26_12 : Certificate := {
  objectiveScale := 26
  eta := 705432
  rows := #[⟨.assumptionRow 12, 81⟩]
  caps := #[0, 0, 209950, 63778, 19877, 6402, 2154, 770, 301, 136, 3016, 1206, 257, 26, 0] }

theorem case_40_26_12_checked :
    (Witness.linear .conditional case_40_26_12).check 40 26 12 = true := by
  change case_40_26_12.check 40 26 12 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_26_13 : Certificate := {
  objectiveScale := 2858941542600000
  eta := 1382844888341577460800
  rows := #[⟨.count 2, 236636558432783308800⟩, ⟨.count 3, 41809584242330704800⟩, ⟨.count 4, 7705167658759771200⟩, ⟨.count 5, 1447950969431366400⟩, ⟨.count 6, 258562673112744000⟩, ⟨.count 7, 45248467794730200⟩, ⟨.count 8, 17237511540849600⟩, ⟨.path 7, 19579531566394800⟩, ⟨.privateRow 2 24, 20478163710529324800⟩, ⟨.privateRow 3 20, 533285513295034500⟩, ⟨.privateRow 3 21, 5214347241107004000⟩, ⟨.privateRow 3 22, 7205279824075132800⟩, ⟨.privateRow 4 17, 53867223565155000⟩, ⟨.privateRow 4 18, 1254028964596808400⟩, ⟨.privateRow 4 19, 2375544559223335500⟩, ⟨.privateRow 4 20, 3059658298500804000⟩, ⟨.privateRow 4 21, 3878440096691160000⟩, ⟨.privateRow 5 15, 219408896898528480⟩, ⟨.privateRow 5 16, 673986701247219360⟩, ⟨.privateRow 5 17, 1009428675832152576⟩, ⟨.privateRow 5 18, 1291520552198156280⟩, ⟨.privateRow 5 19, 1670314868308326240⟩, ⟨.privateRow 5 20, 581766014503674000⟩, ⟨.privateRow 6 12, 21706496014403200⟩, ⟨.privateRow 6 13, 159446981752858800⟩, ⟨.privateRow 6 14, 322998132920205600⟩, ⟨.privateRow 6 15, 475946846433458400⟩, ⟨.privateRow 6 16, 584926224952829760⟩, ⟨.privateRow 6 17, 484805012086395000⟩, ⟨.privateRow 7 10, 23917047262928820⟩, ⟨.privateRow 7 11, 94088083827137400⟩, ⟨.privateRow 7 12, 172913787644147550⟩, ⟨.privateRow 7 13, 251175168166665600⟩, ⟨.privateRow 7 14, 182789445297759300⟩, ⟨.privateRow 8 8, 18804558044563200⟩, ⟨.privateRow 8 9, 59253945921670500⟩, ⟨.privateRow 8 10, 108692086660357200⟩, ⟨.privateRow 8 11, 55752576389935425⟩, ⟨.privateRow 9 6, 14125183068196200⟩, ⟨.privateRow 9 7, 44138476521266400⟩, ⟨.privateRow 9 8, 17237511540849600⟩, ⟨.privateRow 10 4, 11933661835972800⟩, ⟨.privateRow 10 5, 9480631347467280⟩, ⟨.privateRow 11 2, 5540628709558800⟩, ⟨.hall 3 22, 1465375845228094800⟩, ⟨.hall 2 23, 5735781965217704400⟩, ⟨.assumptionRow 13, 3167374552366752⟩]
  caps := #[0, 0, 121018048041290400, 109681577248691448, 9315552392391960, 11049860749434624, 15626533863454280, 6953262670786380, 0, 7568683498512960, 22573586648345040, 0, 178962629599432224, 31139923958833248, 2858941542600000] }

theorem case_40_26_13_checked :
    (Witness.linear .conditional case_40_26_13).check 40 26 13 = true := by
  change case_40_26_13.check 40 26 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_26_14 : Certificate := {
  objectiveScale := 1708660800000
  eta := 1063425510822074400
  rows := #[⟨.count 2, 166445092754740800⟩, ⟨.count 3, 25925658117559200⟩, ⟨.count 4, 4024988018251200⟩, ⟨.count 5, 581148002635200⟩, ⟨.count 6, 78921333691200⟩, ⟨.count 7, 12555666723600⟩, ⟨.count 8, 7174666699200⟩, ⟨.path 6, 40138869170400⟩, ⟨.privateRow 2 24, 15389660069784000⟩, ⟨.privateRow 3 20, 345280834899000⟩, ⟨.privateRow 3 21, 3577767127334400⟩, ⟨.privateRow 3 22, 5297594524021800⟩, ⟨.privateRow 4 17, 26905000122000⟩, ⟨.privateRow 4 18, 755492403425760⟩, ⟨.privateRow 4 19, 1590085507210200⟩, ⟨.privateRow 4 20, 2243877010174800⟩, ⟨.privateRow 4 21, 3123670514164200⟩, ⟨.privateRow 5 15, 103622686184160⟩, ⟨.privateRow 5 16, 391378068441360⟩, ⟨.privateRow 5 17, 661217282998272⟩, ⟨.privateRow 5 18, 947594104296840⟩, ⟨.privateRow 5 19, 1392602806314720⟩, ⟨.privateRow 5 20, 1030999604675040⟩, ⟨.privateRow 6 12, 4783111132800⟩, ⟨.privateRow 6 13, 71746666992000⟩, ⟨.privateRow 6 14, 179879143672800⟩, ⟨.privateRow 6 15, 303926853230000⟩, ⟨.privateRow 6 16, 427370979715680⟩, ⟨.privateRow 6 17, 646317891819600⟩, ⟨.privateRow 6 18, 194911778661600⟩, ⟨.privateRow 7 10, 3766700017080⟩, ⟨.privateRow 7 11, 39958907588600⟩, ⟨.privateRow 7 12, 91140687913275⟩, ⟨.privateRow 7 13, 155152167370200⟩, ⟨.privateRow 7 14, 221816778783600⟩, ⟨.privateRow 7 15, 198738267567840⟩, ⟨.privateRow 8 8, 1793666674800⟩, ⟨.privateRow 8 9, 22420833435000⟩, ⟨.privateRow 8 10, 53411407649600⟩, ⟨.privateRow 8 11, 92261729585025⟩, ⟨.privateRow 8 12, 91989476607600⟩, ⟨.privateRow 9 6, 697537040200⟩, ⟨.privateRow 9 7, 13588383900000⟩, ⟨.privateRow 9 8, 36710377944240⟩, ⟨.privateRow 9 9, 41453629817600⟩, ⟨.privateRow 10 4, 165569231520⟩, ⟨.privateRow 10 5, 9147700041480⟩, ⟨.privateRow 10 6, 21328327369440⟩, ⟨.privateRow 11 3, 7036692339600⟩, ⟨.privateRow 11 4, 2242083343500⟩, ⟨.privateRow 12 1, 2818619060400⟩, ⟨.hall 4 21, 8805272767200⟩, ⟨.hall 3 22, 1436025136946400⟩, ⟨.hall 2 23, 4547841853955400⟩, ⟨.assumptionRow 14, 1302411438900⟩]
  caps := #[0, 0, 5282152722000, 9750030661800, 1892464945800, 0, 7781691775000, 1531936454400, 0, 3629671893120, 749842740900, 8005075848000, 0, 95434014733200, 17492857361100] }

theorem case_40_26_14_checked :
    (Witness.linear .conditional case_40_26_14).check 40 26 14 = true := by
  change case_40_26_14.check 40 26 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_26_15 : Certificate := {
  objectiveScale := 2845557000000
  eta := 2228422778104723200
  rows := #[⟨.count 2, 345438677566382400⟩, ⟨.count 3, 52620799238607600⟩, ⟨.count 4, 7770164035233600⟩, ⟨.count 5, 1000866004538400⟩, ⟨.count 6, 93270667089600⟩, ⟨.path 6, 85969878554560⟩, ⟨.privateRow 2 24, 33857252153524800⟩, ⟨.privateRow 3 20, 478460585502900⟩, ⟨.privateRow 3 21, 7458066033818400⟩, ⟨.privateRow 3 22, 11571840552472200⟩, ⟨.privateRow 4 17, 16143000073200⟩, ⟨.privateRow 4 18, 1424888806461120⟩, ⟨.privateRow 4 19, 3266267014810800⟩, ⟨.privateRow 4 20, 4875186022106400⟩, ⟨.privateRow 4 21, 7197087532635000⟩, ⟨.privateRow 5 15, 179264172241440⟩, ⟨.privateRow 5 16, 730022336643600⟩, ⟨.privateRow 5 17, 1320712645988736⟩, ⟨.privateRow 5 18, 2028098909196360⟩, ⟨.privateRow 5 19, 3232187347989600⟩, ⟨.privateRow 5 20, 2753995812487920⟩, ⟨.privateRow 6 12, 14349333398400⟩, ⟨.privateRow 6 13, 119876722765800⟩, ⟨.privateRow 6 14, 324226604644800⟩, ⟨.privateRow 6 15, 586728298956800⟩, ⟨.privateRow 6 16, 892528537380480⟩, ⟨.privateRow 6 17, 1482465506722200⟩, ⟨.privateRow 6 18, 1123632523613600⟩, ⟨.privateRow 7 8, 74736111450⟩, ⟨.privateRow 7 10, 11927883387420⟩, ⟨.privateRow 7 11, 64273055847000⟩, ⟨.privateRow 7 12, 156385313209125⟩, ⟨.privateRow 7 13, 287242906064400⟩, ⟨.privateRow 7 14, 314639029204500⟩, ⟨.privateRow 7 15, 1016470904609160⟩, ⟨.privateRow 8 8, 7419257609400⟩, ⟨.privateRow 8 9, 35873333496000⟩, ⟨.privateRow 8 10, 86893185579200⟩, ⟨.privateRow 8 11, 162102625735050⟩, ⟨.privateRow 8 12, 258800477364000⟩, ⟨.privateRow 8 13, 184897139727300⟩, ⟨.privateRow 9 6, 4783111132800⟩, ⟨.privateRow 9 7, 22828484952000⟩, ⟨.privateRow 9 8, 57636489150240⟩, ⟨.privateRow 9 9, 110808741243200⟩, ⟨.privateRow 9 10, 81163417034700⟩, ⟨.privateRow 10 4, 3642523093440⟩, ⟨.privateRow 10 5, 17577933413040⟩, ⟨.privateRow 10 6, 47352800214720⟩, ⟨.privateRow 10 7, 31209800141520⟩, ⟨.privateRow 11 2, 3459214301400⟩, ⟨.privateRow 11 3, 17384769309600⟩, ⟨.privateRow 11 4, 12555666723600⟩, ⟨.privateRow 12 0, 5261422246080⟩, ⟨.privateRow 12 1, 5637238120800⟩, ⟨.hall 4 21, 406020910932000⟩, ⟨.hall 3 22, 3674989060142400⟩, ⟨.hall 2 23, 10407750880527000⟩, ⟨.assumptionRow 15, 812126478240⟩]
  caps := #[0, 287035699368000, 139122581188800, 112053896914960, 0, 6020675079744, 262567836960, 6448008880170, 9223477973450, 0, 0, 53422755091200, 0, 539087634914400, 144726686739360] }

theorem case_40_26_15_checked :
    (Witness.linear .conditional case_40_26_15).check 40 26 15 = true := by
  change case_40_26_15.check 40 26 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_26_16 : Certificate := {
  objectiveScale := 92744776800000
  eta := 115876907185240721520
  rows := #[⟨.count 2, 16320047888402818560⟩, ⟨.count 3, 2169409350837128400⟩, ⟨.count 4, 260190722779827840⟩, ⟨.count 5, 24911877712962240⟩, ⟨.count 6, 1383993206275680⟩, ⟨.path 5, 11022049104524640⟩, ⟨.path 6, 1219352333975776⟩, ⟨.privateRow 7 9, 5242398508620⟩, ⟨.privateRow 7 10, 74966298673266⟩, ⟨.privateRow 7 11, 275517166064140⟩, ⟨.privateRow 7 15, 1845324275034240⟩, ⟨.privateRow 8 8, 31454391051720⟩, ⟨.privateRow 8 9, 132632682268086⟩, ⟨.privateRow 9 6, 12814751909960⟩, ⟨.privateRow 9 7, 55918917425280⟩, ⟨.privateRow 9 8, 53821958021832⟩, ⟨.hall 9 5, 10332980951832⟩, ⟨.hall 11 5, 4647107835480⟩, ⟨.hall 10 6, 4147831787040⟩, ⟨.hall 12 6, 2534786092080⟩, ⟨.hall 8 7, 4341649544155⟩, ⟨.hall 7 8, 3643918499760⟩, ⟨.hall 6 10, 2884630091490⟩, ⟨.hall 5 14, 12064627002714⟩, ⟨.hall 4 17, 146366715253200⟩, ⟨.hall 3 19, 924632107143030⟩, ⟨.hall 2 22, 75512875700382120⟩]
  caps := #[0, 17665295510086224, 0, 2681206481661136, 711336975498240, 0, 75011630951296, 0, 0, 405897119320, 0, 0, 0, 1427063880621600, 14282695627200000] }

theorem case_40_26_16_checked :
    (Witness.linear .negative case_40_26_16).check 40 26 16 = true := by
  change case_40_26_16.check 40 26 16 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_27_1_checked :
    (Witness.rising).check 40 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_27_2_checked :
    (Witness.rising).check 40 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_27_3_checked :
    (Witness.rising).check 40 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_27_4_checked :
    (Witness.rising).check 40 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_27_5_checked :
    (Witness.rising).check 40 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_27_6_checked :
    (Witness.rising).check 40 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_27_7_checked :
    (Witness.rising).check 40 27 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_27_8_checked :
    (Witness.rising).check 40 27 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_27_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_40_27_9_checked :
    (Witness.linear .positive case_40_27_9).check 40 27 9 = true := by
  change case_40_27_9.check 40 27 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_27_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_40_27_10_checked :
    (Witness.linear .positive case_40_27_10).check 40 27 10 = true := by
  change case_40_27_10.check 40 27 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_27_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_40_27_11_checked :
    (Witness.linear .positive case_40_27_11).check 40 27 11 = true := by
  change case_40_27_11.check 40 27 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_27_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_40_27_12_checked :
    (Witness.linear .positive case_40_27_12).check 40 27 12 = true := by
  change case_40_27_12.check 40 27 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_27_13 : Certificate := {
  objectiveScale := 5
  eta := 261630
  rows := #[⟨.assumptionRow 13, 12⟩]
  caps := #[0, 0, 76908, 22984, 7150, 2288, 759, 264, 98, 612, 1972, 952, 282, 53] }

theorem case_40_27_13_checked :
    (Witness.linear .conditional case_40_27_13).check 40 27 13 = true := by
  change case_40_27_13.check 40 27 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_27_14 : Certificate := {
  objectiveScale := 826768488000000
  eta := 1236073000565417414400
  rows := #[⟨.count 2, 158173373096068730400⟩, ⟨.count 3, 19431618316470360000⟩, ⟨.count 4, 2198548815234932160⟩, ⟨.count 5, 222075637902518400⟩, ⟨.count 6, 9253151579271600⟩, ⟨.count 7, 9253151579271600⟩, ⟨.path 5, 144333573122138400⟩, ⟨.privateRow 2 24, 2086585681125745800⟩, ⟨.privateRow 2 25, 13435576093102363200⟩, ⟨.privateRow 3 21, 1660940708479252200⟩, ⟨.privateRow 3 22, 3645741722233010400⟩, ⟨.privateRow 3 23, 4497031667525997600⟩, ⟨.privateRow 4 18, 387707051171480040⟩, ⟨.privateRow 4 19, 1059300792795012768⟩, ⟨.privateRow 4 20, 1522606092369141780⟩, ⟨.privateRow 4 21, 1891344182803115040⟩, ⟨.privateRow 4 22, 2295706906817283960⟩, ⟨.privateRow 5 15, 57061101405508200⟩, ⟨.privateRow 5 16, 260498248269779520⟩, ⟨.privateRow 5 17, 477873872671715520⟩, ⟨.privateRow 5 18, 663759406619749440⟩, ⟨.privateRow 5 19, 817361722835658000⟩, ⟨.privateRow 5 20, 946700219354809920⟩, ⟨.privateRow 6 11, 2243188261641600⟩, ⟨.privateRow 6 12, 308438385975720⟩, ⟨.privateRow 6 13, 47636595167361200⟩, ⟨.privateRow 6 14, 142074431540066025⟩, ⟨.privateRow 6 15, 233752233943027800⟩, ⟨.privateRow 6 16, 327201721122576300⟩, ⟨.privateRow 6 17, 400661463382460280⟩, ⟨.privateRow 6 18, 97158091582351800⟩, ⟨.privateRow 7 10, 1682391196231200⟩, ⟨.privateRow 7 11, 33707909324489400⟩, ⟨.privateRow 7 12, 83278364213444400⟩, ⟨.privateRow 7 13, 119299561432751700⟩, ⟨.privateRow 7 14, 223208676871408800⟩, ⟨.privateRow 8 8, 899611959095850⟩, ⟨.privateRow 8 9, 24955469410762800⟩, ⟨.privateRow 8 10, 58603293335386800⟩, ⟨.privateRow 8 11, 80708044330313400⟩, ⟨.privateRow 9 6, 379616475047040⟩, ⟨.privateRow 9 7, 21179435836999440⟩, ⟨.privateRow 9 8, 35218055707773120⟩, ⟨.privateRow 10 4, 396563639111640⟩, ⟨.privateRow 10 5, 17936878445972640⟩, ⟨.privateRow 11 3, 5287515188155200⟩, ⟨.hall 3 23, 414078533172404100⟩, ⟨.hall 2 24, 2882541779974688832⟩, ⟨.assumptionRow 14, 697935311302320⟩]
  caps := #[0, 579417867942295200, 46162311873525120, 29803462196759160, 39879519271505004, 5758611847876160, 752836580683005, 0, 13451393937451470, 10910505488225280, 0, 0, 226554792782791200, 54588014529069840] }

theorem case_40_27_14_checked :
    (Witness.linear .conditional case_40_27_14).check 40 27 14 = true := by
  change case_40_27_14.check 40 27 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_27_15 : Certificate := {
  objectiveScale := 22812174000000
  eta := 34146543193141579200
  rows := #[⟨.count 2, 4387066677743349600⟩, ⟨.count 3, 534268925968377600⟩, ⟨.count 4, 57610926354421440⟩, ⟨.count 5, 4470121535880000⟩, ⟨.count 6, 134103646076400⟩, ⟨.path 5, 4109790467983200⟩, ⟨.privateRow 2 24, 148989150790880400⟩, ⟨.privateRow 2 25, 474995114402608800⟩, ⟨.privateRow 3 21, 55250702183476800⟩, ⟨.privateRow 3 22, 127577268634015200⟩, ⟨.privateRow 3 23, 157839991431922800⟩, ⟨.privateRow 4 18, 10822164238365480⟩, ⟨.privateRow 4 19, 32957312059736064⟩, ⟨.privateRow 4 20, 50671062669967740⟩, ⟨.privateRow 4 21, 67588237622505600⟩, ⟨.privateRow 4 22, 88226788753663560⟩, ⟨.privateRow 5 14, 35760972287040⟩, ⟨.privateRow 5 15, 1417028526873960⟩, ⟨.privateRow 5 16, 7080672512833920⟩, ⟨.privateRow 5 17, 14423592155772800⟩, ⟨.privateRow 5 18, 21613931650286976⟩, ⟨.privateRow 5 19, 29028969254004720⟩, ⟨.privateRow 5 20, 41351604287913920⟩, ⟨.privateRow 5 21, 9995191754227680⟩, ⟨.privateRow 6 12, 111753038397000⟩, ⟨.privateRow 6 13, 1117530383970000⟩, ⟨.privateRow 6 14, 3746520612259425⟩, ⟨.privateRow 6 15, 6804163566400200⟩, ⟨.privateRow 6 16, 10385582368361200⟩, ⟨.privateRow 6 17, 13987010285768520⟩, ⟨.privateRow 6 18, 14863154106801000⟩, ⟨.privateRow 7 10, 85338683866800⟩, ⟨.privateRow 7 11, 752896184400360⟩, ⟨.privateRow 7 12, 2111600268377600⟩, ⟨.privateRow 7 13, 3790822709623950⟩, ⟨.privateRow 7 14, 5796561681424800⟩, ⟨.privateRow 7 15, 7372507590247800⟩, ⟨.privateRow 8 8, 63326721758300⟩, ⟨.privateRow 8 9, 546573951432600⟩, ⟨.privateRow 8 10, 1419263587641900⟩, ⟨.privateRow 8 11, 2592670490810400⟩, ⟨.privateRow 8 12, 2997775254999525⟩, ⟨.privateRow 9 6, 57767724463680⟩, ⟨.privateRow 9 7, 467872720755440⟩, ⟨.privateRow 9 8, 1215873057759360⟩, ⟨.privateRow 9 9, 1079981363068608⟩, ⟨.privateRow 10 4, 68967589410720⟩, ⟨.privateRow 10 5, 507530722073760⟩, ⟨.privateRow 10 6, 415721302836840⟩, ⟨.privateRow 11 2, 125163403004640⟩, ⟨.privateRow 11 3, 210734300977200⟩, ⟨.privateRow 12 0, 92196256677525⟩, ⟨.hall 3 23, 21925946133491400⟩, ⟨.hall 2 24, 107744233403622816⟩, ⟨.assumptionRow 15, 10081782692800⟩]
  caps := #[0, 4469895457585600, 3491174831113200, 264414138887920, 342659446177412, 0, 13449182171600, 298274872168260, 55743479867075, 0, 662461795450280, 0, 542931938887975, 5451426234654400] }

theorem case_40_27_15_checked :
    (Witness.linear .conditional case_40_27_15).check 40 27 15 = true := by
  change case_40_27_15.check 40 27 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_27_16 : Certificate := {
  objectiveScale := 43940049153000000
  eta := 77559916537454551200000
  rows := #[⟨.count 2, 10160349066406546207200⟩, ⟨.count 3, 1245659265601542792000⟩, ⟨.count 4, 133497068464467227520⟩, ⟨.count 5, 9923491004792164800⟩, ⟨.path 5, 9490767634481733600⟩, ⟨.path 6, 44064481836447072⟩, ⟨.privateRow 4 18, 26127507237617265480⟩, ⟨.privateRow 4 19, 56454218037262373328⟩, ⟨.privateRow 4 20, 102296829311900283060⟩, ⟨.privateRow 5 15, 3525450751702479600⟩, ⟨.privateRow 5 16, 16474487322241428480⟩, ⟨.privateRow 5 17, 30136075314553047840⟩, ⟨.privateRow 5 18, 50745599264505617472⟩, ⟨.privateRow 6 11, 11870204551186800⟩, ⟨.privateRow 6 12, 39171675018916440⟩, ⟨.privateRow 6 14, 3386717736010483875⟩, ⟨.privateRow 6 16, 78343350037832880000⟩, ⟨.privateRow 7 9, 4663294645109100⟩, ⟨.privateRow 7 10, 40697844175497600⟩, ⟨.privateRow 7 11, 95131210760225640⟩, ⟨.privateRow 7 12, 1803140596108852000⟩, ⟨.privateRow 7 13, 1902624215204512800⟩, ⟨.privateRow 7 18, 62003165601370593600⟩, ⟨.privateRow 8 7, 5022009617809800⟩, ⟨.privateRow 8 8, 32643062515763700⟩, ⟨.privateRow 8 9, 77156329582714200⟩, ⟨.privateRow 8 10, 1011934937988674700⟩, ⟨.privateRow 8 11, 1828011500882767200⟩, ⟨.privateRow 9 6, 8035215388495680⟩, ⟨.hall 9 4, 2688252207180540⟩, ⟨.hall 8 6, 4619982310944000⟩, ⟨.hall 10 6, 2215592478445500⟩, ⟨.hall 9 7, 1691235591880065⟩, ⟨.hall 11 7, 1506602885342940⟩, ⟨.hall 7 8, 1923289751464620⟩, ⟨.hall 6 9, 1038544100530200⟩, ⟨.hall 5 12, 619598589210300⟩, ⟨.hall 4 17, 16078908002058720⟩, ⟨.hall 3 19, 86394445298637840⟩, ⟨.hall 2 22, 5797634984973655824⟩]
  caps := #[0, 26738945386647381888, 1111722972847206720, 2314357307013207456, 7546340156475120, 242915777527174752, 44064481836447072, 604517814761154840, 23438691528497280, 15257491581892560, 112644710008630800, 0, 0, 27989811310461000000] }

theorem case_40_27_16_checked :
    (Witness.linear .negative case_40_27_16).check 40 27 16 = true := by
  change case_40_27_16.check 40 27 16 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_27_17 : Certificate := {
  objectiveScale := 447
  eta := 283803
  rows := #[⟨.assumptionRow 17, 182⟩]
  caps := #[0, 0, 112047, 66232, 32640, 15267, 8801, 3890, 2347, 1338, 886210, 871624, 596778, 331513] }

theorem case_40_27_17_checked :
    (Witness.linear .conditional case_40_27_17).check 40 27 17 = true := by
  change case_40_27_17.check 40 27 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_28_1_checked :
    (Witness.rising).check 40 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_28_2_checked :
    (Witness.rising).check 40 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_28_3_checked :
    (Witness.rising).check 40 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_28_4_checked :
    (Witness.rising).check 40 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_28_5_checked :
    (Witness.rising).check 40 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_28_6_checked :
    (Witness.rising).check 40 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_28_7_checked :
    (Witness.rising).check 40 28 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_28_8_checked :
    (Witness.rising).check 40 28 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_28_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_40_28_9_checked :
    (Witness.linear .positive case_40_28_9).check 40 28 9 = true := by
  change case_40_28_9.check 40 28 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_28_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_40_28_10_checked :
    (Witness.linear .positive case_40_28_10).check 40 28 10 = true := by
  change case_40_28_10.check 40 28 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_28_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_40_28_11_checked :
    (Witness.linear .positive case_40_28_11).check 40 28 11 = true := by
  change case_40_28_11.check 40 28 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_28_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_40_28_12_checked :
    (Witness.linear .positive case_40_28_12).check 40 28 12 = true := by
  change case_40_28_12.check 40 28 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_28_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_40_28_13_checked :
    (Witness.linear .positive case_40_28_13).check 40 28 13 = true := by
  change case_40_28_13.check 40 28 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_28_14 : Certificate := {
  objectiveScale := 873
  eta := 61886154
  rows := #[⟨.assumptionRow 14, 1454⟩]
  caps := #[0, 0, 18756610, 5776056, 1812408, 581581, 191763, 65385, 23256, 2263584, 1545708, 693124, 232904] }

theorem case_40_28_14_checked :
    (Witness.linear .conditional case_40_28_14).check 40 28 14 = true := by
  change case_40_28_14.check 40 28 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_28_15 : Certificate := {
  objectiveScale := 11031520500000
  eta := 26715683048484830400
  rows := #[⟨.count 2, 2946380216643864000⟩, ⟨.count 3, 288304681011787440⟩, ⟨.count 4, 22396161148320960⟩, ⟨.count 5, 1147344321123000⟩, ⟨.path 4, 11230589922140160⟩, ⟨.path 5, 737489573706600⟩, ⟨.privateRow 2 25, 284311922774279400⟩, ⟨.privateRow 2 26, 378623625970590000⟩, ⟨.privateRow 3 21, 23736259315392624⟩, ⟨.privateRow 3 22, 62163115318444140⟩, ⟨.privateRow 3 23, 127492900963187760⟩, ⟨.privateRow 3 24, 122123329540332120⟩, ⟨.privateRow 4 18, 7828166396690640⟩, ⟨.privateRow 4 19, 13783429777757640⟩, ⟨.privateRow 4 20, 34328542088000160⟩, ⟨.privateRow 4 21, 46421551232636580⟩, ⟨.privateRow 4 22, 55164314959593840⟩, ⟨.privateRow 4 23, 55806827779422720⟩, ⟨.privateRow 5 15, 1570586892915040⟩, ⟨.privateRow 5 16, 3591187725114990⟩, ⟨.privateRow 5 17, 8778823119906840⟩, ⟨.privateRow 5 18, 15282626357358360⟩, ⟨.privateRow 5 19, 20615482761938064⟩, ⟨.privateRow 5 20, 24805584222679260⟩, ⟨.privateRow 5 21, 13462173367843200⟩, ⟨.privateRow 6 12, 220528518865200⟩, ⟨.privateRow 6 13, 839200417735680⟩, ⟨.privateRow 6 14, 2567865861561000⟩, ⟨.privateRow 6 15, 4954068872277525⟩, ⟨.privateRow 6 16, 7876869992362800⟩, ⟨.privateRow 6 17, 10850599151191800⟩, ⟨.privateRow 6 18, 7021747245272760⟩, ⟨.privateRow 7 9, 22694722835400⟩, ⟨.privateRow 7 10, 144783926236950⟩, ⟨.privateRow 7 11, 745028779950000⟩, ⟨.privateRow 7 12, 1878366560009940⟩, ⟨.privateRow 7 13, 2047007963400400⟩, ⟨.privateRow 7 14, 7597058469150150⟩, ⟨.privateRow 7 15, 561964565448000⟩, ⟨.privateRow 8 6, 3059584856328⟩, ⟨.privateRow 8 7, 19668759790680⟩, ⟨.privateRow 8 8, 169453930504320⟩, ⟨.privateRow 8 9, 753422770870770⟩, ⟨.privateRow 8 10, 1702241756429760⟩, ⟨.privateRow 8 11, 2124881682719796⟩, ⟨.privateRow 9 4, 5736721605615⟩, ⟨.privateRow 9 5, 30595848563280⟩, ⟨.privateRow 9 6, 255693877278840⟩, ⟨.privateRow 9 7, 981420680837520⟩, ⟨.privateRow 9 8, 435990842026740⟩, ⟨.privateRow 10 2, 16197802180560⟩, ⟨.privateRow 10 3, 68840659267380⟩, ⟨.privateRow 10 4, 477295237587168⟩, ⟨.privateRow 11 0, 76489621408200⟩, ⟨.privateRow 11 1, 80989010902800⟩, ⟨.hall 2 25, 59097058263381600⟩, ⟨.assumptionRow 15, 6288162800920⟩]
  caps := #[0, 3179398475682000, 0, 1192803635885048, 158099392325160, 143347333511096, 150733101874225, 9634497486810, 330616263786858, 2699633696760, 841716751687812, 2603049547898800, 11132924197595200] }

theorem case_40_28_15_checked :
    (Witness.linear .conditional case_40_28_15).check 40 28 15 = true := by
  change case_40_28_15.check 40 28 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_28_16 : Certificate := {
  objectiveScale := 3971347380000
  eta := 12197089665195435000
  rows := #[⟨.count 2, 1501709810018418000⟩, ⟨.count 3, 170233115988335400⟩, ⟨.count 4, 16390633158900000⟩, ⟨.count 5, 1065391155328500⟩, ⟨.path 4, 1455669503402400⟩, ⟨.path 5, 1084064028547500⟩, ⟨.privateRow 2 25, 153416326367304000⟩, ⟨.privateRow 3 21, 8811604386224640⟩, ⟨.privateRow 3 22, 33486063543632700⟩, ⟨.privateRow 3 24, 221519407142533500⟩, ⟨.privateRow 4 18, 3058023843646200⟩, ⟨.privateRow 4 19, 6709232506376400⟩, ⟨.privateRow 4 21, 55285605644969700⟩, ⟨.privateRow 4 22, 7364857832732400⟩, ⟨.privateRow 4 23, 74888802903014100⟩, ⟨.privateRow 5 15, 699333681446400⟩, ⟨.privateRow 5 16, 1577598441544125⟩, ⟨.privateRow 5 18, 12156386259517500⟩, ⟨.privateRow 5 19, 4356630293635620⟩, ⟨.privateRow 5 21, 53717568406101600⟩, ⟨.privateRow 6 11, 1951265852250⟩, ⟨.privateRow 6 12, 20222209741500⟩, ⟨.privateRow 6 14, 10406751212000⟩, ⟨.privateRow 6 18, 30903368061594600⟩, ⟨.privateRow 7 9, 2701752718500⟩, ⟨.privateRow 7 10, 11707595113500⟩, ⟨.privateRow 7 11, 6385960971000⟩, ⟨.privateRow 7 12, 43318101919950⟩, ⟨.privateRow 7 14, 2926898778375⟩, ⟨.privateRow 7 17, 11983894358178600⟩, ⟨.privateRow 8 8, 3782453805900⟩, ⟨.privateRow 8 10, 13410518039100⟩, ⟨.hall 9 4, 177607480050⟩, ⟨.hall 8 6, 523519191195⟩, ⟨.hall 10 6, 185414402250⟩, ⟨.hall 7 7, 397502455350⟩, ⟨.hall 9 7, 169800557850⟩, ⟨.hall 6 8, 79705521350⟩, ⟨.hall 3 23, 68348940272613⟩, ⟨.hall 2 24, 518952662169480⟩, ⟨.hall 1 26, 103570589749627000⟩]
  caps := #[0, 0, 0, 0, 0, 98440621258980, 478233128100, 0, 2094076764780, 3280663881495, 72013765824000, 0, 10118993124240000] }

theorem case_40_28_16_checked :
    (Witness.linear .negative case_40_28_16).check 40 28 16 = true := by
  change case_40_28_16.check 40 28 16 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_28_17 : Certificate := {
  objectiveScale := 998
  eta := 555351
  rows := #[⟨.assumptionRow 17, 399⟩]
  caps := #[0, 0, 233682, 135388, 63620, 32081, 18122, 7576, 8398, 6710002, 6619392, 4588844, 2616068] }

theorem case_40_28_17_checked :
    (Witness.linear .conditional case_40_28_17).check 40 28 17 = true := by
  change case_40_28_17.check 40 28 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_28_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4862, 4862, 3432] }

theorem case_40_28_18_checked :
    (Witness.linear .negative case_40_28_18).check 40 28 18 = true := by
  change case_40_28_18.check 40 28 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_29_1_checked :
    (Witness.rising).check 40 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_29_2_checked :
    (Witness.rising).check 40 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_29_3_checked :
    (Witness.rising).check 40 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_29_4_checked :
    (Witness.rising).check 40 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_29_5_checked :
    (Witness.rising).check 40 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_29_6_checked :
    (Witness.rising).check 40 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_29_7_checked :
    (Witness.rising).check 40 29 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_29_8_checked :
    (Witness.rising).check 40 29 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_29_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_40_29_9_checked :
    (Witness.linear .positive case_40_29_9).check 40 29 9 = true := by
  change case_40_29_9.check 40 29 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_29_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_40_29_10_checked :
    (Witness.linear .positive case_40_29_10).check 40 29 10 = true := by
  change case_40_29_10.check 40 29 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_29_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_40_29_11_checked :
    (Witness.linear .positive case_40_29_11).check 40 29 11 = true := by
  change case_40_29_11.check 40 29 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_29_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_40_29_12_checked :
    (Witness.linear .positive case_40_29_12).check 40 29 12 = true := by
  change case_40_29_12.check 40 29 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_29_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_40_29_13_checked :
    (Witness.linear .positive case_40_29_13).check 40 29 13 = true := by
  change case_40_29_13.check 40 29 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_29_14 : Certificate := {
  objectiveScale := 2
  eta := 390830
  rows := #[⟨.assumptionRow 14, 5⟩]
  caps := #[0, 0, 113050, 33592, 10166, 3146, 1001, 330, 114, 42, 969, 1173] }

theorem case_40_29_14_checked :
    (Witness.linear .conditional case_40_29_14).check 40 29 14 = true := by
  change case_40_29_14.check 40 29 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_29_15 : Certificate := {
  objectiveScale := 495
  eta := 30768980
  rows := #[⟨.assumptionRow 15, 589⟩]
  caps := #[0, 0, 10100210, 3327546, 1102348, 368368, 124553, 42735, 6641526, 5488416, 3108552, 1404744] }

theorem case_40_29_15_checked :
    (Witness.linear .conditional case_40_29_15).check 40 29 15 = true := by
  change case_40_29_15.check 40 29 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_29_16 : Certificate := {
  objectiveScale := 187
  eta := 5489385
  rows := #[⟨.assumptionRow 16, 157⟩]
  caps := #[0, 0, 2094978, 751944, 259420, 95004, 38038, 14377, 3220310, 2974830, 1914744, 1004496] }

theorem case_40_29_16_checked :
    (Witness.linear .conditional case_40_29_16).check 40 29 16 = true := by
  change case_40_29_16.check 40 29 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_29_17 : Certificate := {
  objectiveScale := 56
  eta := 58995
  rows := #[⟨.assumptionRow 17, 25⟩]
  caps := #[0, 0, 31008, 12036, 6860, 3150, 1560, 826, 1031016, 1140190, 829464, 492660] }

theorem case_40_29_17_checked :
    (Witness.linear .conditional case_40_29_17).check 40 29 17 = true := by
  change case_40_29_17.check 40 29 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_29_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 16796, 16796, 11934] }

theorem case_40_29_18_checked :
    (Witness.linear .negative case_40_29_18).check 40 29 18 = true := by
  change case_40_29_18.check 40 29 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_30_1_checked :
    (Witness.rising).check 40 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_30_2_checked :
    (Witness.rising).check 40 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_30_3_checked :
    (Witness.rising).check 40 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_30_4_checked :
    (Witness.rising).check 40 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_30_5_checked :
    (Witness.rising).check 40 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_30_6_checked :
    (Witness.rising).check 40 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_30_7_checked :
    (Witness.rising).check 40 30 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_30_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_40_30_8_checked :
    (Witness.linear .positive case_40_30_8).check 40 30 8 = true := by
  change case_40_30_8.check 40 30 8 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_30_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_40_30_9_checked :
    (Witness.linear .positive case_40_30_9).check 40 30 9 = true := by
  change case_40_30_9.check 40 30 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_30_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_40_30_10_checked :
    (Witness.linear .positive case_40_30_10).check 40 30 10 = true := by
  change case_40_30_10.check 40 30 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_40_30_11_checked :
    (Witness.linear .positive case_40_30_11).check 40 30 11 = true := by
  change case_40_30_11.check 40 30 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_30_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_40_30_12_checked :
    (Witness.linear .positive case_40_30_12).check 40 30 12 = true := by
  change case_40_30_12.check 40 30 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_30_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_40_30_13_checked :
    (Witness.linear .positive case_40_30_13).check 40 30 13 = true := by
  change case_40_30_13.check 40 30 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_30_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_40_30_14_checked :
    (Witness.linear .positive case_40_30_14).check 40 30 14 = true := by
  change case_40_30_14.check 40 30 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_30_15 : Certificate := {
  objectiveScale := 2
  eta := 326876
  rows := #[⟨.assumptionRow 15, 3⟩]
  caps := #[0, 0, 96900, 29070, 9282, 3016, 1001, 341, 10659, 22287, 14535] }

theorem case_40_30_15_checked :
    (Witness.linear .conditional case_40_30_15).check 40 30 15 = true := by
  change case_40_30_15.check 40 30 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_30_16 : Certificate := {
  objectiveScale := 1
  eta := 81719
  rows := #[⟨.assumptionRow 16, 1⟩]
  caps := #[0, 0, 28424, 9690, 3264, 1092, 364, 143, 28424, 25194, 15504] }

theorem case_40_30_16_checked :
    (Witness.linear .conditional case_40_30_16).check 40 30 16 = true := by
  change case_40_30_16.check 40 30 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_30_17 : Certificate := {
  objectiveScale := 448
  eta := 5711343
  rows := #[⟨.assumptionRow 17, 285⟩]
  caps := #[0, 0, 2480640, 945744, 381276, 161700, 59241, 29716, 16222998, 15662270, 10659000] }

theorem case_40_30_17_checked :
    (Witness.linear .conditional case_40_30_17).check 40 30 17 = true := by
  change case_40_30_17.check 40 30 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_30_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 58786, 58786, 41990] }

theorem case_40_30_18_checked :
    (Witness.linear .negative case_40_30_18).check 40 30 18 = true := by
  change case_40_30_18.check 40 30 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_30_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16796] }

theorem case_40_30_19_checked :
    (Witness.linear .negative case_40_30_19).check 40 30 19 = true := by
  change case_40_30_19.check 40 30 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_31_1_checked :
    (Witness.rising).check 40 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_31_2_checked :
    (Witness.rising).check 40 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_31_3_checked :
    (Witness.rising).check 40 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_31_4_checked :
    (Witness.rising).check 40 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_31_5_checked :
    (Witness.rising).check 40 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_31_6_checked :
    (Witness.rising).check 40 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_31_7_checked :
    (Witness.rising).check 40 31 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_31_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_40_31_8_checked :
    (Witness.linear .positive case_40_31_8).check 40 31 8 = true := by
  change case_40_31_8.check 40 31 8 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_31_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_40_31_9_checked :
    (Witness.linear .positive case_40_31_9).check 40 31 9 = true := by
  change case_40_31_9.check 40 31 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_31_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_40_31_10_checked :
    (Witness.linear .positive case_40_31_10).check 40 31 10 = true := by
  change case_40_31_10.check 40 31 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_40_31_11_checked :
    (Witness.linear .positive case_40_31_11).check 40 31 11 = true := by
  change case_40_31_11.check 40 31 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_40_31_12_checked :
    (Witness.linear .positive case_40_31_12).check 40 31 12 = true := by
  change case_40_31_12.check 40 31 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_31_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_40_31_13_checked :
    (Witness.linear .positive case_40_31_13).check 40 31 13 = true := by
  change case_40_31_13.check 40 31 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_31_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_40_31_14_checked :
    (Witness.linear .positive case_40_31_14).check 40 31 14 = true := by
  change case_40_31_14.check 40 31 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_31_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_40_31_15_checked :
    (Witness.linear .positive case_40_31_15).check 40 31 15 = true := by
  change case_40_31_15.check 40 31 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_31_16 : Certificate := {
  objectiveScale := 365
  eta := 63822539
  rows := #[⟨.assumptionRow 16, 417⟩]
  caps := #[0, 0, 19612560, 6056250, 2017458, 690404, 236964, 81939, 17079271, 14464263] }

theorem case_40_31_16_checked :
    (Witness.linear .conditional case_40_31_16).check 40 31 16 = true := by
  change case_40_31_16.check 40 31 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_31_17 : Certificate := {
  objectiveScale := 997
  eta := 11630850
  rows := #[⟨.assumptionRow 17, 623⟩]
  caps := #[0, 0, 4822713, 1930248, 736032, 331184, 148580, 125995840, 122251624, 84149252] }

theorem case_40_31_17_checked :
    (Witness.linear .conditional case_40_31_17).check 40 31 17 = true := by
  change case_40_31_17.check 40 31 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_31_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 208012, 208012, 149226] }

theorem case_40_31_18_checked :
    (Witness.linear .negative case_40_31_18).check 40 31 18 = true := by
  change case_40_31_18.check 40 31 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_31_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 58786] }

theorem case_40_31_19_checked :
    (Witness.linear .negative case_40_31_19).check 40 31 19 = true := by
  change case_40_31_19.check 40 31 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_31_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_40_31_20_checked :
    (Witness.linear .negative case_40_31_20).check 40 31 20 = true := by
  change case_40_31_20.check 40 31 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_32_1_checked :
    (Witness.rising).check 40 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_32_2_checked :
    (Witness.rising).check 40 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_32_3_checked :
    (Witness.rising).check 40 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_32_4_checked :
    (Witness.rising).check 40 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_32_5_checked :
    (Witness.rising).check 40 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_32_6_checked :
    (Witness.rising).check 40 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_32_7_checked :
    (Witness.rising).check 40 32 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_32_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0] }

theorem case_40_32_8_checked :
    (Witness.linear .positive case_40_32_8).check 40 32 8 = true := by
  change case_40_32_8.check 40 32 8 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_32_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1] }

theorem case_40_32_9_checked :
    (Witness.linear .positive case_40_32_9).check 40 32 9 = true := by
  change case_40_32_9.check 40 32 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_32_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_40_32_10_checked :
    (Witness.linear .positive case_40_32_10).check 40 32 10 = true := by
  change case_40_32_10.check 40 32 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_40_32_11_checked :
    (Witness.linear .positive case_40_32_11).check 40 32 11 = true := by
  change case_40_32_11.check 40 32 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_40_32_12_checked :
    (Witness.linear .positive case_40_32_12).check 40 32 12 = true := by
  change case_40_32_12.check 40 32 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_32_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_40_32_13_checked :
    (Witness.linear .positive case_40_32_13).check 40 32 13 = true := by
  change case_40_32_13.check 40 32 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_32_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_40_32_14_checked :
    (Witness.linear .positive case_40_32_14).check 40 32 14 = true := by
  change case_40_32_14.check 40 32 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_32_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_40_32_15_checked :
    (Witness.linear .positive case_40_32_15).check 40 32 15 = true := by
  change case_40_32_15.check 40 32 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_32_16 : Certificate := {
  objectiveScale := 7
  eta := 4494545
  rows := #[⟨.assumptionRow 16, 11⟩]
  caps := #[0, 0, 1307504, 397936, 122740, 38454, 12272, 4004, 1342] }

theorem case_40_32_16_checked :
    (Witness.linear .conditional case_40_32_16).check 40 32 16 = true := by
  change case_40_32_16.check 40 32 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_32_17 : Certificate := {
  objectiveScale := 999
  eta := 68076734
  rows := #[⟨.assumptionRow 17, 799⟩]
  caps := #[0, 0, 23396505, 7736496, 3093048, 1140020, 482885, 208049145, 196043881] }

theorem case_40_32_17_checked :
    (Witness.linear .conditional case_40_32_17).check 40 32 17 = true := by
  change case_40_32_17.check 40 32 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_32_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 742900, 742900, 534888] }

theorem case_40_32_18_checked :
    (Witness.linear .negative case_40_32_18).check 40 32 18 = true := by
  change case_40_32_18.check 40 32 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_32_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 208012] }

theorem case_40_32_19_checked :
    (Witness.linear .negative case_40_32_19).check 40 32 19 = true := by
  change case_40_32_19.check 40 32 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_32_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_40_32_20_checked :
    (Witness.linear .negative case_40_32_20).check 40 32 20 = true := by
  change case_40_32_20.check 40 32 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_33_1_checked :
    (Witness.rising).check 40 33 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_33_2_checked :
    (Witness.rising).check 40 33 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_33_3_checked :
    (Witness.rising).check 40 33 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_33_4_checked :
    (Witness.rising).check 40 33 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_33_5_checked :
    (Witness.rising).check 40 33 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_33_6_checked :
    (Witness.rising).check 40 33 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_33_7_checked :
    (Witness.rising).check 40 33 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_33_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1] }

theorem case_40_33_8_checked :
    (Witness.linear .positive case_40_33_8).check 40 33 8 = true := by
  change case_40_33_8.check 40 33 8 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_33_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_40_33_9_checked :
    (Witness.linear .positive case_40_33_9).check 40 33 9 = true := by
  change case_40_33_9.check 40 33 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_33_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_40_33_10_checked :
    (Witness.linear .positive case_40_33_10).check 40 33 10 = true := by
  change case_40_33_10.check 40 33 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_33_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_40_33_11_checked :
    (Witness.linear .positive case_40_33_11).check 40 33 11 = true := by
  change case_40_33_11.check 40 33 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_33_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_40_33_12_checked :
    (Witness.linear .positive case_40_33_12).check 40 33 12 = true := by
  change case_40_33_12.check 40 33 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_33_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42] }

theorem case_40_33_13_checked :
    (Witness.linear .positive case_40_33_13).check 40 33 13 = true := by
  change case_40_33_13.check 40 33 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_33_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_40_33_14_checked :
    (Witness.linear .positive case_40_33_14).check 40 33 14 = true := by
  change case_40_33_14.check 40 33 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_33_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_40_33_15_checked :
    (Witness.linear .positive case_40_33_15).check 40 33 15 = true := by
  change case_40_33_15.check 40 33 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_33_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_40_33_16_checked :
    (Witness.linear .positive case_40_33_16).check 40 33 16 = true := by
  change case_40_33_16.check 40 33 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_33_17 : Certificate := {
  objectiveScale := 287
  eta := 56265935
  rows := #[⟨.assumptionRow 17, 271⟩]
  caps := #[0, 0, 18223337, 5835318, 2005830, 724608, 255645, 100212840] }

theorem case_40_33_17_checked :
    (Witness.linear .conditional case_40_33_17).check 40 33 17 = true := by
  change case_40_33_17.check 40 33 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_33_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 2674440, 2674440, 1931540] }

theorem case_40_33_18_checked :
    (Witness.linear .negative case_40_33_18).check 40 33 18 = true := by
  change case_40_33_18.check 40 33 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_33_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 742900] }

theorem case_40_33_19_checked :
    (Witness.linear .negative case_40_33_19).check 40 33 19 = true := by
  change case_40_33_19.check 40 33 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_33_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_40_33_20_checked :
    (Witness.linear .negative case_40_33_20).check 40 33 20 = true := by
  change case_40_33_20.check 40 33 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_33_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_40_33_21_checked :
    (Witness.linear .negative case_40_33_21).check 40 33 21 = true := by
  change case_40_33_21.check 40 33 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_34_1_checked :
    (Witness.rising).check 40 34 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_34_2_checked :
    (Witness.rising).check 40 34 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_34_3_checked :
    (Witness.rising).check 40 34 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_34_4_checked :
    (Witness.rising).check 40 34 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_34_5_checked :
    (Witness.rising).check 40 34 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_34_6_checked :
    (Witness.rising).check 40 34 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_34_7_checked :
    (Witness.rising).check 40 34 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_34_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1] }

theorem case_40_34_8_checked :
    (Witness.linear .positive case_40_34_8).check 40 34 8 = true := by
  change case_40_34_8.check 40 34 8 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_34_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_40_34_9_checked :
    (Witness.linear .positive case_40_34_9).check 40 34 9 = true := by
  change case_40_34_9.check 40 34 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_34_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_40_34_10_checked :
    (Witness.linear .positive case_40_34_10).check 40 34 10 = true := by
  change case_40_34_10.check 40 34 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_34_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_40_34_11_checked :
    (Witness.linear .positive case_40_34_11).check 40 34 11 = true := by
  change case_40_34_11.check 40 34 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_34_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_40_34_12_checked :
    (Witness.linear .positive case_40_34_12).check 40 34 12 = true := by
  change case_40_34_12.check 40 34 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_34_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_40_34_13_checked :
    (Witness.linear .positive case_40_34_13).check 40 34 13 = true := by
  change case_40_34_13.check 40 34 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_34_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429] }

theorem case_40_34_14_checked :
    (Witness.linear .positive case_40_34_14).check 40 34 14 = true := by
  change case_40_34_14.check 40 34 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_34_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430] }

theorem case_40_34_15_checked :
    (Witness.linear .positive case_40_34_15).check 40 34 15 = true := by
  change case_40_34_15.check 40 34 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_34_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862] }

theorem case_40_34_16_checked :
    (Witness.linear .positive case_40_34_16).check 40 34 16 = true := by
  change case_40_34_16.check 40 34 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_34_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796] }

theorem case_40_34_17_checked :
    (Witness.linear .positive case_40_34_17).check 40 34 17 = true := by
  change case_40_34_17.check 40 34 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_34_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 9694845, 9694845, 7020405] }

theorem case_40_34_18_checked :
    (Witness.linear .negative case_40_34_18).check 40 34 18 = true := by
  change case_40_34_18.check 40 34 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_34_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 2674440] }

theorem case_40_34_19_checked :
    (Witness.linear .negative case_40_34_19).check 40 34 19 = true := by
  change case_40_34_19.check 40 34 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_34_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_40_34_20_checked :
    (Witness.linear .negative case_40_34_20).check 40 34 20 = true := by
  change case_40_34_20.check 40 34 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_34_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_40_34_21_checked :
    (Witness.linear .negative case_40_34_21).check 40 34 21 = true := by
  change case_40_34_21.check 40 34 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_34_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_40_34_22_checked :
    (Witness.linear .negative case_40_34_22).check 40 34 22 = true := by
  change case_40_34_22.check 40 34 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_35_1_checked :
    (Witness.rising).check 40 35 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_35_2_checked :
    (Witness.rising).check 40 35 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_35_3_checked :
    (Witness.rising).check 40 35 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_35_4_checked :
    (Witness.rising).check 40 35 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_35_5_checked :
    (Witness.rising).check 40 35 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_35_6_checked :
    (Witness.rising).check 40 35 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_35_7_checked :
    (Witness.rising).check 40 35 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_35_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2] }

theorem case_40_35_8_checked :
    (Witness.linear .positive case_40_35_8).check 40 35 8 = true := by
  change case_40_35_8.check 40 35 8 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_35_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_40_35_9_checked :
    (Witness.linear .positive case_40_35_9).check 40 35 9 = true := by
  change case_40_35_9.check 40 35 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_35_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_40_35_10_checked :
    (Witness.linear .positive case_40_35_10).check 40 35 10 = true := by
  change case_40_35_10.check 40 35 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_35_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_40_35_11_checked :
    (Witness.linear .positive case_40_35_11).check 40 35 11 = true := by
  change case_40_35_11.check 40 35 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_35_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_40_35_12_checked :
    (Witness.linear .positive case_40_35_12).check 40 35 12 = true := by
  change case_40_35_12.check 40 35 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_35_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_40_35_13_checked :
    (Witness.linear .positive case_40_35_13).check 40 35 13 = true := by
  change case_40_35_13.check 40 35 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_35_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_40_35_14_checked :
    (Witness.linear .positive case_40_35_14).check 40 35 14 = true := by
  change case_40_35_14.check 40 35 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_35_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862] }

theorem case_40_35_15_checked :
    (Witness.linear .positive case_40_35_15).check 40 35 15 = true := by
  change case_40_35_15.check 40 35 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_35_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796] }

theorem case_40_35_16_checked :
    (Witness.linear .positive case_40_35_16).check 40 35 16 = true := by
  change case_40_35_16.check 40 35 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_35_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786] }

theorem case_40_35_17_checked :
    (Witness.linear .positive case_40_35_17).check 40 35 17 = true := by
  change case_40_35_17.check 40 35 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_35_18 : Certificate := {
  objectiveScale := 398
  eta := 56001550
  rows := #[⟨.assumptionRow 18, 307⟩]
  caps := #[0, 0, 20646065, 7631844, 2643432, 969000] }

theorem case_40_35_18_checked :
    (Witness.linear .conditional case_40_35_18).check 40 35 18 = true := by
  change case_40_35_18.check 40 35 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_35_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 9694845] }

theorem case_40_35_19_checked :
    (Witness.linear .negative case_40_35_19).check 40 35 19 = true := by
  change case_40_35_19.check 40 35 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_35_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_40_35_20_checked :
    (Witness.linear .negative case_40_35_20).check 40 35 20 = true := by
  change case_40_35_20.check 40 35 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_35_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_40_35_21_checked :
    (Witness.linear .negative case_40_35_21).check 40 35 21 = true := by
  change case_40_35_21.check 40 35 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_35_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_40_35_22_checked :
    (Witness.linear .negative case_40_35_22).check 40 35 22 = true := by
  change case_40_35_22.check 40 35 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_36_1_checked :
    (Witness.rising).check 40 36 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_36_2_checked :
    (Witness.rising).check 40 36 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_36_3_checked :
    (Witness.rising).check 40 36 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_36_4_checked :
    (Witness.rising).check 40 36 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_36_5_checked :
    (Witness.rising).check 40 36 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_36_6_checked :
    (Witness.rising).check 40 36 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_36_7_checked :
    (Witness.rising).check 40 36 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_36_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5] }

theorem case_40_36_8_checked :
    (Witness.linear .positive case_40_36_8).check 40 36 8 = true := by
  change case_40_36_8.check 40 36 8 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_36_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_40_36_9_checked :
    (Witness.linear .positive case_40_36_9).check 40 36 9 = true := by
  change case_40_36_9.check 40 36 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_36_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_40_36_10_checked :
    (Witness.linear .positive case_40_36_10).check 40 36 10 = true := by
  change case_40_36_10.check 40 36 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_36_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_40_36_11_checked :
    (Witness.linear .positive case_40_36_11).check 40 36 11 = true := by
  change case_40_36_11.check 40 36 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_36_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_40_36_12_checked :
    (Witness.linear .positive case_40_36_12).check 40 36 12 = true := by
  change case_40_36_12.check 40 36 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_36_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_40_36_13_checked :
    (Witness.linear .positive case_40_36_13).check 40 36 13 = true := by
  change case_40_36_13.check 40 36 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_36_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_40_36_14_checked :
    (Witness.linear .positive case_40_36_14).check 40 36 14 = true := by
  change case_40_36_14.check 40 36 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_36_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796] }

theorem case_40_36_15_checked :
    (Witness.linear .positive case_40_36_15).check 40 36 15 = true := by
  change case_40_36_15.check 40 36 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_36_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786] }

theorem case_40_36_16_checked :
    (Witness.linear .positive case_40_36_16).check 40 36 16 = true := by
  change case_40_36_16.check 40 36 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_36_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012] }

theorem case_40_36_17_checked :
    (Witness.linear .positive case_40_36_17).check 40 36 17 = true := by
  change case_40_36_17.check 40 36 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_36_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900] }

theorem case_40_36_18_checked :
    (Witness.linear .positive case_40_36_18).check 40 36 18 = true := by
  change case_40_36_18.check 40 36 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_36_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 35357670] }

theorem case_40_36_19_checked :
    (Witness.linear .negative case_40_36_19).check 40 36 19 = true := by
  change case_40_36_19.check 40 36 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_36_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_40_36_20_checked :
    (Witness.linear .negative case_40_36_20).check 40 36 20 = true := by
  change case_40_36_20.check 40 36 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_36_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_40_36_21_checked :
    (Witness.linear .negative case_40_36_21).check 40 36 21 = true := by
  change case_40_36_21.check 40 36 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_36_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_40_36_22_checked :
    (Witness.linear .negative case_40_36_22).check 40 36 22 = true := by
  change case_40_36_22.check 40 36 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_36_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_40_36_23_checked :
    (Witness.linear .negative case_40_36_23).check 40 36 23 = true := by
  change case_40_36_23.check 40 36 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_37_1_checked :
    (Witness.rising).check 40 37 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_37_2_checked :
    (Witness.rising).check 40 37 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_37_3_checked :
    (Witness.rising).check 40 37 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_37_4_checked :
    (Witness.rising).check 40 37 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_37_5_checked :
    (Witness.rising).check 40 37 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_37_6_checked :
    (Witness.rising).check 40 37 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_37_7_checked :
    (Witness.rising).check 40 37 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_37_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14] }

theorem case_40_37_8_checked :
    (Witness.linear .positive case_40_37_8).check 40 37 8 = true := by
  change case_40_37_8.check 40 37 8 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_37_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_40_37_9_checked :
    (Witness.linear .positive case_40_37_9).check 40 37 9 = true := by
  change case_40_37_9.check 40 37 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_37_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_40_37_10_checked :
    (Witness.linear .positive case_40_37_10).check 40 37 10 = true := by
  change case_40_37_10.check 40 37 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_37_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_40_37_11_checked :
    (Witness.linear .positive case_40_37_11).check 40 37 11 = true := by
  change case_40_37_11.check 40 37 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_37_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_40_37_12_checked :
    (Witness.linear .positive case_40_37_12).check 40 37 12 = true := by
  change case_40_37_12.check 40 37 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_37_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_40_37_13_checked :
    (Witness.linear .positive case_40_37_13).check 40 37 13 = true := by
  change case_40_37_13.check 40 37 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_37_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_40_37_14_checked :
    (Witness.linear .positive case_40_37_14).check 40 37 14 = true := by
  change case_40_37_14.check 40 37 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_37_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_40_37_15_checked :
    (Witness.linear .positive case_40_37_15).check 40 37 15 = true := by
  change case_40_37_15.check 40 37 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_37_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012] }

theorem case_40_37_16_checked :
    (Witness.linear .positive case_40_37_16).check 40 37 16 = true := by
  change case_40_37_16.check 40 37 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_37_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900] }

theorem case_40_37_17_checked :
    (Witness.linear .positive case_40_37_17).check 40 37 17 = true := by
  change case_40_37_17.check 40 37 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_37_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440] }

theorem case_40_37_18_checked :
    (Witness.linear .positive case_40_37_18).check 40 37 18 = true := by
  change case_40_37_18.check 40 37 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_37_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 129644790] }

theorem case_40_37_19_checked :
    (Witness.linear .negative case_40_37_19).check 40 37 19 = true := by
  change case_40_37_19.check 40 37 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_37_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_40_37_20_checked :
    (Witness.linear .negative case_40_37_20).check 40 37 20 = true := by
  change case_40_37_20.check 40 37 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_37_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_40_37_21_checked :
    (Witness.linear .negative case_40_37_21).check 40 37 21 = true := by
  change case_40_37_21.check 40 37 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_37_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_40_37_22_checked :
    (Witness.linear .negative case_40_37_22).check 40 37 22 = true := by
  change case_40_37_22.check 40 37 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_37_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_40_37_23_checked :
    (Witness.linear .negative case_40_37_23).check 40 37 23 = true := by
  change case_40_37_23.check 40 37 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_37_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_40_37_24_checked :
    (Witness.linear .negative case_40_37_24).check 40 37 24 = true := by
  change case_40_37_24.check 40 37 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_38_1_checked :
    (Witness.rising).check 40 38 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_38_2_checked :
    (Witness.rising).check 40 38 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_38_3_checked :
    (Witness.rising).check 40 38 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_38_4_checked :
    (Witness.rising).check 40 38 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_38_5_checked :
    (Witness.rising).check 40 38 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_38_6_checked :
    (Witness.rising).check 40 38 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_38_7_checked :
    (Witness.rising).check 40 38 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_38_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_40_38_8_checked :
    (Witness.linear .positive case_40_38_8).check 40 38 8 = true := by
  change case_40_38_8.check 40 38 8 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_38_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_40_38_9_checked :
    (Witness.linear .positive case_40_38_9).check 40 38 9 = true := by
  change case_40_38_9.check 40 38 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_38_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_40_38_10_checked :
    (Witness.linear .positive case_40_38_10).check 40 38 10 = true := by
  change case_40_38_10.check 40 38 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_38_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_40_38_11_checked :
    (Witness.linear .positive case_40_38_11).check 40 38 11 = true := by
  change case_40_38_11.check 40 38 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_38_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_40_38_12_checked :
    (Witness.linear .positive case_40_38_12).check 40 38 12 = true := by
  change case_40_38_12.check 40 38 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_38_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_40_38_13_checked :
    (Witness.linear .positive case_40_38_13).check 40 38 13 = true := by
  change case_40_38_13.check 40 38 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_38_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_40_38_14_checked :
    (Witness.linear .positive case_40_38_14).check 40 38 14 = true := by
  change case_40_38_14.check 40 38 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_38_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_40_38_15_checked :
    (Witness.linear .positive case_40_38_15).check 40 38 15 = true := by
  change case_40_38_15.check 40 38 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_38_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900] }

theorem case_40_38_16_checked :
    (Witness.linear .positive case_40_38_16).check 40 38 16 = true := by
  change case_40_38_16.check 40 38 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_38_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440] }

theorem case_40_38_17_checked :
    (Witness.linear .positive case_40_38_17).check 40 38 17 = true := by
  change case_40_38_17.check 40 38 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_38_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845] }

theorem case_40_38_18_checked :
    (Witness.linear .positive case_40_38_18).check 40 38 18 = true := by
  change case_40_38_18.check 40 38 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_38_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670] }

theorem case_40_38_19_checked :
    (Witness.linear .positive case_40_38_19).check 40 38 19 = true := by
  change case_40_38_19.check 40 38 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_38_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_40_38_20_checked :
    (Witness.linear .negative case_40_38_20).check 40 38 20 = true := by
  change case_40_38_20.check 40 38 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_38_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_40_38_21_checked :
    (Witness.linear .negative case_40_38_21).check 40 38 21 = true := by
  change case_40_38_21.check 40 38 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_38_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_40_38_22_checked :
    (Witness.linear .negative case_40_38_22).check 40 38 22 = true := by
  change case_40_38_22.check 40 38 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_38_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_40_38_23_checked :
    (Witness.linear .negative case_40_38_23).check 40 38 23 = true := by
  change case_40_38_23.check 40 38 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_38_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_40_38_24_checked :
    (Witness.linear .negative case_40_38_24).check 40 38 24 = true := by
  change case_40_38_24.check 40 38 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_39_1_checked :
    (Witness.rising).check 40 39 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_39_2_checked :
    (Witness.rising).check 40 39 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_39_3_checked :
    (Witness.rising).check 40 39 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_39_4_checked :
    (Witness.rising).check 40 39 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_39_5_checked :
    (Witness.rising).check 40 39 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_39_6_checked :
    (Witness.rising).check 40 39 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_40_39_7_checked :
    (Witness.rising).check 40 39 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_39_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_40_39_8_checked :
    (Witness.linear .positive case_40_39_8).check 40 39 8 = true := by
  change case_40_39_8.check 40 39 8 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_39_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_40_39_9_checked :
    (Witness.linear .positive case_40_39_9).check 40 39 9 = true := by
  change case_40_39_9.check 40 39 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_39_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_40_39_10_checked :
    (Witness.linear .positive case_40_39_10).check 40 39 10 = true := by
  change case_40_39_10.check 40 39 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_39_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_40_39_11_checked :
    (Witness.linear .positive case_40_39_11).check 40 39 11 = true := by
  change case_40_39_11.check 40 39 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_39_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_40_39_12_checked :
    (Witness.linear .positive case_40_39_12).check 40 39 12 = true := by
  change case_40_39_12.check 40 39 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_39_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_40_39_13_checked :
    (Witness.linear .positive case_40_39_13).check 40 39 13 = true := by
  change case_40_39_13.check 40 39 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_39_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_40_39_14_checked :
    (Witness.linear .positive case_40_39_14).check 40 39 14 = true := by
  change case_40_39_14.check 40 39 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_39_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_40_39_15_checked :
    (Witness.linear .positive case_40_39_15).check 40 39 15 = true := by
  change case_40_39_15.check 40 39 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_39_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_40_39_16_checked :
    (Witness.linear .positive case_40_39_16).check 40 39 16 = true := by
  change case_40_39_16.check 40 39 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_39_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0] }

theorem case_40_39_17_checked :
    (Witness.linear .positive case_40_39_17).check 40 39 17 = true := by
  change case_40_39_17.check 40 39 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_39_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0] }

theorem case_40_39_18_checked :
    (Witness.linear .positive case_40_39_18).check 40 39 18 = true := by
  change case_40_39_18.check 40 39 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_39_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0] }

theorem case_40_39_19_checked :
    (Witness.linear .positive case_40_39_19).check 40 39 19 = true := by
  change case_40_39_19.check 40 39 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_39_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_40_39_20_checked :
    (Witness.linear .negative case_40_39_20).check 40 39 20 = true := by
  change case_40_39_20.check 40 39 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_39_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_40_39_21_checked :
    (Witness.linear .negative case_40_39_21).check 40 39 21 = true := by
  change case_40_39_21.check 40 39 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_39_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_40_39_22_checked :
    (Witness.linear .negative case_40_39_22).check 40 39 22 = true := by
  change case_40_39_22.check 40 39 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_39_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_40_39_23_checked :
    (Witness.linear .negative case_40_39_23).check 40 39 23 = true := by
  change case_40_39_23.check 40 39 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_39_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_40_39_24_checked :
    (Witness.linear .negative case_40_39_24).check 40 39 24 = true := by
  change case_40_39_24.check 40 39 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_40_39_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_40_39_25_checked :
    (Witness.linear .negative case_40_39_25).check 40 39 25 = true := by
  change case_40_39_25.check 40 39 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_40 (a k : ℕ) (h : Domain 40 a k) :
    ∃ w : Witness, w.check 40 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 20 ≤ a := by omega
  have haHi : a ≤ 39 := by omega
  interval_cases a

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_40_20_1_checked⟩

    · exact ⟨Witness.rising, case_40_20_2_checked⟩

    · exact ⟨Witness.rising, case_40_20_3_checked⟩

    · exact ⟨Witness.rising, case_40_20_4_checked⟩

    · exact ⟨Witness.rising, case_40_20_5_checked⟩

    · exact ⟨Witness.rising, case_40_20_6_checked⟩

    · exact ⟨Witness.rising, case_40_20_7_checked⟩

    · exact ⟨Witness.rising, case_40_20_8_checked⟩

    · exact ⟨Witness.linear .positive case_40_20_9, case_40_20_9_checked⟩

    · exact ⟨Witness.linear .positive case_40_20_10, case_40_20_10_checked⟩

    · exact ⟨Witness.linear .positive case_40_20_11, case_40_20_11_checked⟩

    · exact ⟨Witness.linear .conditional case_40_20_12, case_40_20_12_checked⟩

  · have hkHi : k ≤ 13 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_40_21_1_checked⟩

    · exact ⟨Witness.rising, case_40_21_2_checked⟩

    · exact ⟨Witness.rising, case_40_21_3_checked⟩

    · exact ⟨Witness.rising, case_40_21_4_checked⟩

    · exact ⟨Witness.rising, case_40_21_5_checked⟩

    · exact ⟨Witness.rising, case_40_21_6_checked⟩

    · exact ⟨Witness.rising, case_40_21_7_checked⟩

    · exact ⟨Witness.rising, case_40_21_8_checked⟩

    · exact ⟨Witness.linear .positive case_40_21_9, case_40_21_9_checked⟩

    · exact ⟨Witness.linear .positive case_40_21_10, case_40_21_10_checked⟩

    · exact ⟨Witness.linear .positive case_40_21_11, case_40_21_11_checked⟩

    · exact ⟨Witness.linear .conditional case_40_21_12, case_40_21_12_checked⟩

    · exact ⟨Witness.linear .conditional case_40_21_13, case_40_21_13_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_40_22_1_checked⟩

    · exact ⟨Witness.rising, case_40_22_2_checked⟩

    · exact ⟨Witness.rising, case_40_22_3_checked⟩

    · exact ⟨Witness.rising, case_40_22_4_checked⟩

    · exact ⟨Witness.rising, case_40_22_5_checked⟩

    · exact ⟨Witness.rising, case_40_22_6_checked⟩

    · exact ⟨Witness.rising, case_40_22_7_checked⟩

    · exact ⟨Witness.rising, case_40_22_8_checked⟩

    · exact ⟨Witness.linear .positive case_40_22_9, case_40_22_9_checked⟩

    · exact ⟨Witness.linear .positive case_40_22_10, case_40_22_10_checked⟩

    · exact ⟨Witness.linear .positive case_40_22_11, case_40_22_11_checked⟩

    · exact ⟨Witness.linear .conditional case_40_22_12, case_40_22_12_checked⟩

    · exact ⟨Witness.linear .conditional case_40_22_13, case_40_22_13_checked⟩

    · exact ⟨Witness.linear .conditional case_40_22_14, case_40_22_14_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_40_23_1_checked⟩

    · exact ⟨Witness.rising, case_40_23_2_checked⟩

    · exact ⟨Witness.rising, case_40_23_3_checked⟩

    · exact ⟨Witness.rising, case_40_23_4_checked⟩

    · exact ⟨Witness.rising, case_40_23_5_checked⟩

    · exact ⟨Witness.rising, case_40_23_6_checked⟩

    · exact ⟨Witness.rising, case_40_23_7_checked⟩

    · exact ⟨Witness.rising, case_40_23_8_checked⟩

    · exact ⟨Witness.linear .positive case_40_23_9, case_40_23_9_checked⟩

    · exact ⟨Witness.linear .positive case_40_23_10, case_40_23_10_checked⟩

    · exact ⟨Witness.linear .positive case_40_23_11, case_40_23_11_checked⟩

    · exact ⟨Witness.linear .conditional case_40_23_12, case_40_23_12_checked⟩

    · exact ⟨Witness.linear .conditional case_40_23_13, case_40_23_13_checked⟩

    · exact ⟨Witness.linear .conditional case_40_23_14, case_40_23_14_checked⟩

  · have hkHi : k ≤ 15 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_40_24_1_checked⟩

    · exact ⟨Witness.rising, case_40_24_2_checked⟩

    · exact ⟨Witness.rising, case_40_24_3_checked⟩

    · exact ⟨Witness.rising, case_40_24_4_checked⟩

    · exact ⟨Witness.rising, case_40_24_5_checked⟩

    · exact ⟨Witness.rising, case_40_24_6_checked⟩

    · exact ⟨Witness.rising, case_40_24_7_checked⟩

    · exact ⟨Witness.rising, case_40_24_8_checked⟩

    · exact ⟨Witness.linear .positive case_40_24_9, case_40_24_9_checked⟩

    · exact ⟨Witness.linear .positive case_40_24_10, case_40_24_10_checked⟩

    · exact ⟨Witness.linear .positive case_40_24_11, case_40_24_11_checked⟩

    · exact ⟨Witness.linear .conditional case_40_24_12, case_40_24_12_checked⟩

    · exact ⟨Witness.linear .conditional case_40_24_13, case_40_24_13_checked⟩

    · exact ⟨Witness.linear .conditional case_40_24_14, case_40_24_14_checked⟩

    · exact ⟨Witness.linear .negative case_40_24_15, case_40_24_15_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_40_25_1_checked⟩

    · exact ⟨Witness.rising, case_40_25_2_checked⟩

    · exact ⟨Witness.rising, case_40_25_3_checked⟩

    · exact ⟨Witness.rising, case_40_25_4_checked⟩

    · exact ⟨Witness.rising, case_40_25_5_checked⟩

    · exact ⟨Witness.rising, case_40_25_6_checked⟩

    · exact ⟨Witness.rising, case_40_25_7_checked⟩

    · exact ⟨Witness.rising, case_40_25_8_checked⟩

    · exact ⟨Witness.linear .positive case_40_25_9, case_40_25_9_checked⟩

    · exact ⟨Witness.linear .positive case_40_25_10, case_40_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_40_25_11, case_40_25_11_checked⟩

    · exact ⟨Witness.linear .positive case_40_25_12, case_40_25_12_checked⟩

    · exact ⟨Witness.linear .conditional case_40_25_13, case_40_25_13_checked⟩

    · exact ⟨Witness.linear .conditional case_40_25_14, case_40_25_14_checked⟩

    · exact ⟨Witness.linear .negative case_40_25_15, case_40_25_15_checked⟩

    · exact ⟨Witness.linear .negative case_40_25_16, case_40_25_16_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_40_26_1_checked⟩

    · exact ⟨Witness.rising, case_40_26_2_checked⟩

    · exact ⟨Witness.rising, case_40_26_3_checked⟩

    · exact ⟨Witness.rising, case_40_26_4_checked⟩

    · exact ⟨Witness.rising, case_40_26_5_checked⟩

    · exact ⟨Witness.rising, case_40_26_6_checked⟩

    · exact ⟨Witness.rising, case_40_26_7_checked⟩

    · exact ⟨Witness.rising, case_40_26_8_checked⟩

    · exact ⟨Witness.linear .positive case_40_26_9, case_40_26_9_checked⟩

    · exact ⟨Witness.linear .positive case_40_26_10, case_40_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_40_26_11, case_40_26_11_checked⟩

    · exact ⟨Witness.linear .conditional case_40_26_12, case_40_26_12_checked⟩

    · exact ⟨Witness.linear .conditional case_40_26_13, case_40_26_13_checked⟩

    · exact ⟨Witness.linear .conditional case_40_26_14, case_40_26_14_checked⟩

    · exact ⟨Witness.linear .conditional case_40_26_15, case_40_26_15_checked⟩

    · exact ⟨Witness.linear .negative case_40_26_16, case_40_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_40_27_1_checked⟩

    · exact ⟨Witness.rising, case_40_27_2_checked⟩

    · exact ⟨Witness.rising, case_40_27_3_checked⟩

    · exact ⟨Witness.rising, case_40_27_4_checked⟩

    · exact ⟨Witness.rising, case_40_27_5_checked⟩

    · exact ⟨Witness.rising, case_40_27_6_checked⟩

    · exact ⟨Witness.rising, case_40_27_7_checked⟩

    · exact ⟨Witness.rising, case_40_27_8_checked⟩

    · exact ⟨Witness.linear .positive case_40_27_9, case_40_27_9_checked⟩

    · exact ⟨Witness.linear .positive case_40_27_10, case_40_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_40_27_11, case_40_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_40_27_12, case_40_27_12_checked⟩

    · exact ⟨Witness.linear .conditional case_40_27_13, case_40_27_13_checked⟩

    · exact ⟨Witness.linear .conditional case_40_27_14, case_40_27_14_checked⟩

    · exact ⟨Witness.linear .conditional case_40_27_15, case_40_27_15_checked⟩

    · exact ⟨Witness.linear .negative case_40_27_16, case_40_27_16_checked⟩

    · exact ⟨Witness.linear .conditional case_40_27_17, case_40_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_40_28_1_checked⟩

    · exact ⟨Witness.rising, case_40_28_2_checked⟩

    · exact ⟨Witness.rising, case_40_28_3_checked⟩

    · exact ⟨Witness.rising, case_40_28_4_checked⟩

    · exact ⟨Witness.rising, case_40_28_5_checked⟩

    · exact ⟨Witness.rising, case_40_28_6_checked⟩

    · exact ⟨Witness.rising, case_40_28_7_checked⟩

    · exact ⟨Witness.rising, case_40_28_8_checked⟩

    · exact ⟨Witness.linear .positive case_40_28_9, case_40_28_9_checked⟩

    · exact ⟨Witness.linear .positive case_40_28_10, case_40_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_40_28_11, case_40_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_40_28_12, case_40_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_40_28_13, case_40_28_13_checked⟩

    · exact ⟨Witness.linear .conditional case_40_28_14, case_40_28_14_checked⟩

    · exact ⟨Witness.linear .conditional case_40_28_15, case_40_28_15_checked⟩

    · exact ⟨Witness.linear .negative case_40_28_16, case_40_28_16_checked⟩

    · exact ⟨Witness.linear .conditional case_40_28_17, case_40_28_17_checked⟩

    · exact ⟨Witness.linear .negative case_40_28_18, case_40_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_40_29_1_checked⟩

    · exact ⟨Witness.rising, case_40_29_2_checked⟩

    · exact ⟨Witness.rising, case_40_29_3_checked⟩

    · exact ⟨Witness.rising, case_40_29_4_checked⟩

    · exact ⟨Witness.rising, case_40_29_5_checked⟩

    · exact ⟨Witness.rising, case_40_29_6_checked⟩

    · exact ⟨Witness.rising, case_40_29_7_checked⟩

    · exact ⟨Witness.rising, case_40_29_8_checked⟩

    · exact ⟨Witness.linear .positive case_40_29_9, case_40_29_9_checked⟩

    · exact ⟨Witness.linear .positive case_40_29_10, case_40_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_40_29_11, case_40_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_40_29_12, case_40_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_40_29_13, case_40_29_13_checked⟩

    · exact ⟨Witness.linear .conditional case_40_29_14, case_40_29_14_checked⟩

    · exact ⟨Witness.linear .conditional case_40_29_15, case_40_29_15_checked⟩

    · exact ⟨Witness.linear .conditional case_40_29_16, case_40_29_16_checked⟩

    · exact ⟨Witness.linear .conditional case_40_29_17, case_40_29_17_checked⟩

    · exact ⟨Witness.linear .negative case_40_29_18, case_40_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_40_30_1_checked⟩

    · exact ⟨Witness.rising, case_40_30_2_checked⟩

    · exact ⟨Witness.rising, case_40_30_3_checked⟩

    · exact ⟨Witness.rising, case_40_30_4_checked⟩

    · exact ⟨Witness.rising, case_40_30_5_checked⟩

    · exact ⟨Witness.rising, case_40_30_6_checked⟩

    · exact ⟨Witness.rising, case_40_30_7_checked⟩

    · exact ⟨Witness.linear .positive case_40_30_8, case_40_30_8_checked⟩

    · exact ⟨Witness.linear .positive case_40_30_9, case_40_30_9_checked⟩

    · exact ⟨Witness.linear .positive case_40_30_10, case_40_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_40_30_11, case_40_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_40_30_12, case_40_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_40_30_13, case_40_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_40_30_14, case_40_30_14_checked⟩

    · exact ⟨Witness.linear .conditional case_40_30_15, case_40_30_15_checked⟩

    · exact ⟨Witness.linear .conditional case_40_30_16, case_40_30_16_checked⟩

    · exact ⟨Witness.linear .conditional case_40_30_17, case_40_30_17_checked⟩

    · exact ⟨Witness.linear .negative case_40_30_18, case_40_30_18_checked⟩

    · exact ⟨Witness.linear .negative case_40_30_19, case_40_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_40_31_1_checked⟩

    · exact ⟨Witness.rising, case_40_31_2_checked⟩

    · exact ⟨Witness.rising, case_40_31_3_checked⟩

    · exact ⟨Witness.rising, case_40_31_4_checked⟩

    · exact ⟨Witness.rising, case_40_31_5_checked⟩

    · exact ⟨Witness.rising, case_40_31_6_checked⟩

    · exact ⟨Witness.rising, case_40_31_7_checked⟩

    · exact ⟨Witness.linear .positive case_40_31_8, case_40_31_8_checked⟩

    · exact ⟨Witness.linear .positive case_40_31_9, case_40_31_9_checked⟩

    · exact ⟨Witness.linear .positive case_40_31_10, case_40_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_40_31_11, case_40_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_40_31_12, case_40_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_40_31_13, case_40_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_40_31_14, case_40_31_14_checked⟩

    · exact ⟨Witness.linear .positive case_40_31_15, case_40_31_15_checked⟩

    · exact ⟨Witness.linear .conditional case_40_31_16, case_40_31_16_checked⟩

    · exact ⟨Witness.linear .conditional case_40_31_17, case_40_31_17_checked⟩

    · exact ⟨Witness.linear .negative case_40_31_18, case_40_31_18_checked⟩

    · exact ⟨Witness.linear .negative case_40_31_19, case_40_31_19_checked⟩

    · exact ⟨Witness.linear .negative case_40_31_20, case_40_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_40_32_1_checked⟩

    · exact ⟨Witness.rising, case_40_32_2_checked⟩

    · exact ⟨Witness.rising, case_40_32_3_checked⟩

    · exact ⟨Witness.rising, case_40_32_4_checked⟩

    · exact ⟨Witness.rising, case_40_32_5_checked⟩

    · exact ⟨Witness.rising, case_40_32_6_checked⟩

    · exact ⟨Witness.rising, case_40_32_7_checked⟩

    · exact ⟨Witness.linear .positive case_40_32_8, case_40_32_8_checked⟩

    · exact ⟨Witness.linear .positive case_40_32_9, case_40_32_9_checked⟩

    · exact ⟨Witness.linear .positive case_40_32_10, case_40_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_40_32_11, case_40_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_40_32_12, case_40_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_40_32_13, case_40_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_40_32_14, case_40_32_14_checked⟩

    · exact ⟨Witness.linear .positive case_40_32_15, case_40_32_15_checked⟩

    · exact ⟨Witness.linear .conditional case_40_32_16, case_40_32_16_checked⟩

    · exact ⟨Witness.linear .conditional case_40_32_17, case_40_32_17_checked⟩

    · exact ⟨Witness.linear .negative case_40_32_18, case_40_32_18_checked⟩

    · exact ⟨Witness.linear .negative case_40_32_19, case_40_32_19_checked⟩

    · exact ⟨Witness.linear .negative case_40_32_20, case_40_32_20_checked⟩

  · have hkHi : k ≤ 21 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_40_33_1_checked⟩

    · exact ⟨Witness.rising, case_40_33_2_checked⟩

    · exact ⟨Witness.rising, case_40_33_3_checked⟩

    · exact ⟨Witness.rising, case_40_33_4_checked⟩

    · exact ⟨Witness.rising, case_40_33_5_checked⟩

    · exact ⟨Witness.rising, case_40_33_6_checked⟩

    · exact ⟨Witness.rising, case_40_33_7_checked⟩

    · exact ⟨Witness.linear .positive case_40_33_8, case_40_33_8_checked⟩

    · exact ⟨Witness.linear .positive case_40_33_9, case_40_33_9_checked⟩

    · exact ⟨Witness.linear .positive case_40_33_10, case_40_33_10_checked⟩

    · exact ⟨Witness.linear .positive case_40_33_11, case_40_33_11_checked⟩

    · exact ⟨Witness.linear .positive case_40_33_12, case_40_33_12_checked⟩

    · exact ⟨Witness.linear .positive case_40_33_13, case_40_33_13_checked⟩

    · exact ⟨Witness.linear .positive case_40_33_14, case_40_33_14_checked⟩

    · exact ⟨Witness.linear .positive case_40_33_15, case_40_33_15_checked⟩

    · exact ⟨Witness.linear .positive case_40_33_16, case_40_33_16_checked⟩

    · exact ⟨Witness.linear .conditional case_40_33_17, case_40_33_17_checked⟩

    · exact ⟨Witness.linear .negative case_40_33_18, case_40_33_18_checked⟩

    · exact ⟨Witness.linear .negative case_40_33_19, case_40_33_19_checked⟩

    · exact ⟨Witness.linear .negative case_40_33_20, case_40_33_20_checked⟩

    · exact ⟨Witness.linear .negative case_40_33_21, case_40_33_21_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_40_34_1_checked⟩

    · exact ⟨Witness.rising, case_40_34_2_checked⟩

    · exact ⟨Witness.rising, case_40_34_3_checked⟩

    · exact ⟨Witness.rising, case_40_34_4_checked⟩

    · exact ⟨Witness.rising, case_40_34_5_checked⟩

    · exact ⟨Witness.rising, case_40_34_6_checked⟩

    · exact ⟨Witness.rising, case_40_34_7_checked⟩

    · exact ⟨Witness.linear .positive case_40_34_8, case_40_34_8_checked⟩

    · exact ⟨Witness.linear .positive case_40_34_9, case_40_34_9_checked⟩

    · exact ⟨Witness.linear .positive case_40_34_10, case_40_34_10_checked⟩

    · exact ⟨Witness.linear .positive case_40_34_11, case_40_34_11_checked⟩

    · exact ⟨Witness.linear .positive case_40_34_12, case_40_34_12_checked⟩

    · exact ⟨Witness.linear .positive case_40_34_13, case_40_34_13_checked⟩

    · exact ⟨Witness.linear .positive case_40_34_14, case_40_34_14_checked⟩

    · exact ⟨Witness.linear .positive case_40_34_15, case_40_34_15_checked⟩

    · exact ⟨Witness.linear .positive case_40_34_16, case_40_34_16_checked⟩

    · exact ⟨Witness.linear .positive case_40_34_17, case_40_34_17_checked⟩

    · exact ⟨Witness.linear .negative case_40_34_18, case_40_34_18_checked⟩

    · exact ⟨Witness.linear .negative case_40_34_19, case_40_34_19_checked⟩

    · exact ⟨Witness.linear .negative case_40_34_20, case_40_34_20_checked⟩

    · exact ⟨Witness.linear .negative case_40_34_21, case_40_34_21_checked⟩

    · exact ⟨Witness.linear .negative case_40_34_22, case_40_34_22_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_40_35_1_checked⟩

    · exact ⟨Witness.rising, case_40_35_2_checked⟩

    · exact ⟨Witness.rising, case_40_35_3_checked⟩

    · exact ⟨Witness.rising, case_40_35_4_checked⟩

    · exact ⟨Witness.rising, case_40_35_5_checked⟩

    · exact ⟨Witness.rising, case_40_35_6_checked⟩

    · exact ⟨Witness.rising, case_40_35_7_checked⟩

    · exact ⟨Witness.linear .positive case_40_35_8, case_40_35_8_checked⟩

    · exact ⟨Witness.linear .positive case_40_35_9, case_40_35_9_checked⟩

    · exact ⟨Witness.linear .positive case_40_35_10, case_40_35_10_checked⟩

    · exact ⟨Witness.linear .positive case_40_35_11, case_40_35_11_checked⟩

    · exact ⟨Witness.linear .positive case_40_35_12, case_40_35_12_checked⟩

    · exact ⟨Witness.linear .positive case_40_35_13, case_40_35_13_checked⟩

    · exact ⟨Witness.linear .positive case_40_35_14, case_40_35_14_checked⟩

    · exact ⟨Witness.linear .positive case_40_35_15, case_40_35_15_checked⟩

    · exact ⟨Witness.linear .positive case_40_35_16, case_40_35_16_checked⟩

    · exact ⟨Witness.linear .positive case_40_35_17, case_40_35_17_checked⟩

    · exact ⟨Witness.linear .conditional case_40_35_18, case_40_35_18_checked⟩

    · exact ⟨Witness.linear .negative case_40_35_19, case_40_35_19_checked⟩

    · exact ⟨Witness.linear .negative case_40_35_20, case_40_35_20_checked⟩

    · exact ⟨Witness.linear .negative case_40_35_21, case_40_35_21_checked⟩

    · exact ⟨Witness.linear .negative case_40_35_22, case_40_35_22_checked⟩

  · have hkHi : k ≤ 23 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_40_36_1_checked⟩

    · exact ⟨Witness.rising, case_40_36_2_checked⟩

    · exact ⟨Witness.rising, case_40_36_3_checked⟩

    · exact ⟨Witness.rising, case_40_36_4_checked⟩

    · exact ⟨Witness.rising, case_40_36_5_checked⟩

    · exact ⟨Witness.rising, case_40_36_6_checked⟩

    · exact ⟨Witness.rising, case_40_36_7_checked⟩

    · exact ⟨Witness.linear .positive case_40_36_8, case_40_36_8_checked⟩

    · exact ⟨Witness.linear .positive case_40_36_9, case_40_36_9_checked⟩

    · exact ⟨Witness.linear .positive case_40_36_10, case_40_36_10_checked⟩

    · exact ⟨Witness.linear .positive case_40_36_11, case_40_36_11_checked⟩

    · exact ⟨Witness.linear .positive case_40_36_12, case_40_36_12_checked⟩

    · exact ⟨Witness.linear .positive case_40_36_13, case_40_36_13_checked⟩

    · exact ⟨Witness.linear .positive case_40_36_14, case_40_36_14_checked⟩

    · exact ⟨Witness.linear .positive case_40_36_15, case_40_36_15_checked⟩

    · exact ⟨Witness.linear .positive case_40_36_16, case_40_36_16_checked⟩

    · exact ⟨Witness.linear .positive case_40_36_17, case_40_36_17_checked⟩

    · exact ⟨Witness.linear .positive case_40_36_18, case_40_36_18_checked⟩

    · exact ⟨Witness.linear .negative case_40_36_19, case_40_36_19_checked⟩

    · exact ⟨Witness.linear .negative case_40_36_20, case_40_36_20_checked⟩

    · exact ⟨Witness.linear .negative case_40_36_21, case_40_36_21_checked⟩

    · exact ⟨Witness.linear .negative case_40_36_22, case_40_36_22_checked⟩

    · exact ⟨Witness.linear .negative case_40_36_23, case_40_36_23_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_40_37_1_checked⟩

    · exact ⟨Witness.rising, case_40_37_2_checked⟩

    · exact ⟨Witness.rising, case_40_37_3_checked⟩

    · exact ⟨Witness.rising, case_40_37_4_checked⟩

    · exact ⟨Witness.rising, case_40_37_5_checked⟩

    · exact ⟨Witness.rising, case_40_37_6_checked⟩

    · exact ⟨Witness.rising, case_40_37_7_checked⟩

    · exact ⟨Witness.linear .positive case_40_37_8, case_40_37_8_checked⟩

    · exact ⟨Witness.linear .positive case_40_37_9, case_40_37_9_checked⟩

    · exact ⟨Witness.linear .positive case_40_37_10, case_40_37_10_checked⟩

    · exact ⟨Witness.linear .positive case_40_37_11, case_40_37_11_checked⟩

    · exact ⟨Witness.linear .positive case_40_37_12, case_40_37_12_checked⟩

    · exact ⟨Witness.linear .positive case_40_37_13, case_40_37_13_checked⟩

    · exact ⟨Witness.linear .positive case_40_37_14, case_40_37_14_checked⟩

    · exact ⟨Witness.linear .positive case_40_37_15, case_40_37_15_checked⟩

    · exact ⟨Witness.linear .positive case_40_37_16, case_40_37_16_checked⟩

    · exact ⟨Witness.linear .positive case_40_37_17, case_40_37_17_checked⟩

    · exact ⟨Witness.linear .positive case_40_37_18, case_40_37_18_checked⟩

    · exact ⟨Witness.linear .negative case_40_37_19, case_40_37_19_checked⟩

    · exact ⟨Witness.linear .negative case_40_37_20, case_40_37_20_checked⟩

    · exact ⟨Witness.linear .negative case_40_37_21, case_40_37_21_checked⟩

    · exact ⟨Witness.linear .negative case_40_37_22, case_40_37_22_checked⟩

    · exact ⟨Witness.linear .negative case_40_37_23, case_40_37_23_checked⟩

    · exact ⟨Witness.linear .negative case_40_37_24, case_40_37_24_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_40_38_1_checked⟩

    · exact ⟨Witness.rising, case_40_38_2_checked⟩

    · exact ⟨Witness.rising, case_40_38_3_checked⟩

    · exact ⟨Witness.rising, case_40_38_4_checked⟩

    · exact ⟨Witness.rising, case_40_38_5_checked⟩

    · exact ⟨Witness.rising, case_40_38_6_checked⟩

    · exact ⟨Witness.rising, case_40_38_7_checked⟩

    · exact ⟨Witness.linear .positive case_40_38_8, case_40_38_8_checked⟩

    · exact ⟨Witness.linear .positive case_40_38_9, case_40_38_9_checked⟩

    · exact ⟨Witness.linear .positive case_40_38_10, case_40_38_10_checked⟩

    · exact ⟨Witness.linear .positive case_40_38_11, case_40_38_11_checked⟩

    · exact ⟨Witness.linear .positive case_40_38_12, case_40_38_12_checked⟩

    · exact ⟨Witness.linear .positive case_40_38_13, case_40_38_13_checked⟩

    · exact ⟨Witness.linear .positive case_40_38_14, case_40_38_14_checked⟩

    · exact ⟨Witness.linear .positive case_40_38_15, case_40_38_15_checked⟩

    · exact ⟨Witness.linear .positive case_40_38_16, case_40_38_16_checked⟩

    · exact ⟨Witness.linear .positive case_40_38_17, case_40_38_17_checked⟩

    · exact ⟨Witness.linear .positive case_40_38_18, case_40_38_18_checked⟩

    · exact ⟨Witness.linear .positive case_40_38_19, case_40_38_19_checked⟩

    · exact ⟨Witness.linear .negative case_40_38_20, case_40_38_20_checked⟩

    · exact ⟨Witness.linear .negative case_40_38_21, case_40_38_21_checked⟩

    · exact ⟨Witness.linear .negative case_40_38_22, case_40_38_22_checked⟩

    · exact ⟨Witness.linear .negative case_40_38_23, case_40_38_23_checked⟩

    · exact ⟨Witness.linear .negative case_40_38_24, case_40_38_24_checked⟩

  · have hkHi : k ≤ 25 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_40_39_1_checked⟩

    · exact ⟨Witness.rising, case_40_39_2_checked⟩

    · exact ⟨Witness.rising, case_40_39_3_checked⟩

    · exact ⟨Witness.rising, case_40_39_4_checked⟩

    · exact ⟨Witness.rising, case_40_39_5_checked⟩

    · exact ⟨Witness.rising, case_40_39_6_checked⟩

    · exact ⟨Witness.rising, case_40_39_7_checked⟩

    · exact ⟨Witness.linear .positive case_40_39_8, case_40_39_8_checked⟩

    · exact ⟨Witness.linear .positive case_40_39_9, case_40_39_9_checked⟩

    · exact ⟨Witness.linear .positive case_40_39_10, case_40_39_10_checked⟩

    · exact ⟨Witness.linear .positive case_40_39_11, case_40_39_11_checked⟩

    · exact ⟨Witness.linear .positive case_40_39_12, case_40_39_12_checked⟩

    · exact ⟨Witness.linear .positive case_40_39_13, case_40_39_13_checked⟩

    · exact ⟨Witness.linear .positive case_40_39_14, case_40_39_14_checked⟩

    · exact ⟨Witness.linear .positive case_40_39_15, case_40_39_15_checked⟩

    · exact ⟨Witness.linear .positive case_40_39_16, case_40_39_16_checked⟩

    · exact ⟨Witness.linear .positive case_40_39_17, case_40_39_17_checked⟩

    · exact ⟨Witness.linear .positive case_40_39_18, case_40_39_18_checked⟩

    · exact ⟨Witness.linear .positive case_40_39_19, case_40_39_19_checked⟩

    · exact ⟨Witness.linear .negative case_40_39_20, case_40_39_20_checked⟩

    · exact ⟨Witness.linear .negative case_40_39_21, case_40_39_21_checked⟩

    · exact ⟨Witness.linear .negative case_40_39_22, case_40_39_22_checked⟩

    · exact ⟨Witness.linear .negative case_40_39_23, case_40_39_23_checked⟩

    · exact ⟨Witness.linear .negative case_40_39_24, case_40_39_24_checked⟩

    · exact ⟨Witness.linear .negative case_40_39_25, case_40_39_25_checked⟩


#print axioms coverage_40
end ForestUnimodality.FiniteRows.FiniteData
