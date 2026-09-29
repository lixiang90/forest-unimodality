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

theorem case_43_22_1_checked :
    (Witness.rising).check 43 22 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_22_2_checked :
    (Witness.rising).check 43 22 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_22_3_checked :
    (Witness.rising).check 43 22 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_22_4_checked :
    (Witness.rising).check 43 22 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_22_5_checked :
    (Witness.rising).check 43 22 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_22_6_checked :
    (Witness.rising).check 43 22 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_22_7_checked :
    (Witness.rising).check 43 22 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_22_8_checked :
    (Witness.rising).check 43 22 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_22_9_checked :
    (Witness.rising).check 43 22 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_22_10 : Certificate := {
  objectiveScale := 449009847000000
  eta := 17065295264460643200
  rows := #[⟨.count 2, 4440290418325681920⟩, ⟨.count 3, 782195700164598720⟩, ⟨.count 4, 124407194229077760⟩, ⟨.count 5, 23082698214576000⟩, ⟨.count 6, 5001251279824800⟩, ⟨.count 7, 1346490729183600⟩, ⟨.count 8, 547145439160320⟩, ⟨.count 9, 449816683155840⟩, ⟨.path 10, 89622172785600⟩, ⟨.path 11, 88751977142400⟩, ⟨.privateRow 8 5, 16884566286588⟩, ⟨.privateRow 9 2, 6247453932720⟩, ⟨.privateRow 10 0, 13506641295840⟩, ⟨.privateRow 11 0, 7398300709800⟩, ⟨.privateRow 13 1, 10960445496000⟩, ⟨.hall 11 1, 7353462523680⟩, ⟨.hall 8 3, 1473254686800⟩, ⟨.hall 7 5, 686522449704⟩, ⟨.hall 6 7, 361196499300⟩, ⟨.hall 6 8, 224813683185⟩, ⟨.hall 5 12, 3702604276800⟩, ⟨.hall 9 12, 4552800436800⟩, ⟨.hall 4 15, 50819932283120⟩]
  caps := #[0, 0, 1669681163854080, 0, 0, 65301092729600, 2567056155300, 7880012337015, 0, 1870670033280, 2380144023360, 0, 5380582334400, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_22_10_checked :
    (Witness.linear .positive case_43_22_10).check 43 22 10 = true := by
  change case_43_22_10.check 43 22 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_22_11 : Certificate := {
  objectiveScale := 65637000000
  eta := 3154739591203200
  rows := #[⟨.count 2, 911849388690240⟩, ⟨.count 3, 181505565521280⟩, ⟨.count 4, 33814320059520⟩, ⟨.count 5, 7046508268800⟩, ⟨.count 6, 1672430760000⟩, ⟨.count 7, 444866582160⟩, ⟨.count 8, 151633722240⟩, ⟨.count 9, 64838854080⟩, ⟨.count 10, 66897230400⟩, ⟨.path 12, 19842363450⟩, ⟨.privateRow 4 18, 113725291680⟩, ⟨.privateRow 8 6, 1672430760⟩, ⟨.privateRow 9 4, 4116752640⟩, ⟨.privateRow 9 5, 2439557120⟩, ⟨.privateRow 10 2, 1988204400⟩, ⟨.privateRow 11 0, 2787384600⟩, ⟨.privateRow 12 0, 1801079280⟩, ⟨.privateRow 13 2, 2744501760⟩, ⟨.hall 9 3, 319552128⟩, ⟨.hall 8 5, 172768960⟩, ⟨.hall 7 6, 125616400⟩, ⟨.hall 7 7, 94753750⟩, ⟨.hall 6 9, 111732075⟩, ⟨.hall 6 10, 296559900⟩, ⟨.hall 10 11, 857656800⟩, ⟨.hall 5 13, 3921077160⟩, ⟨.hall 4 16, 117937339520⟩]
  caps := #[0, 0, 0, 0, 76300387020, 4559583600, 3935131200, 10602016425, 0, 3189909580, 0, 1252572750, 30491370, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_22_11_checked :
    (Witness.linear .positive case_43_22_11).check 43 22 11 = true := by
  change case_43_22_11.check 43 22 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_22_12 : Certificate := {
  objectiveScale := 3281850000
  eta := 200643907464000
  rows := #[⟨.count 2, 64823416257600⟩, ⟨.count 3, 14768041448160⟩, ⟨.count 4, 3173477186880⟩, ⟨.count 5, 786838852800⟩, ⟨.count 6, 199497097800⟩, ⟨.count 7, 59092553520⟩, ⟨.count 8, 18794936160⟩, ⟨.count 9, 6836749920⟩, ⟨.count 10, 3308104800⟩, ⟨.count 11, 3308104800⟩, ⟨.path 13, 315773640⟩, ⟨.path 14, 531660584⟩, ⟨.privateRow 4 18, 29785195440⟩, ⟨.privateRow 8 8, 301492620⟩, ⟨.privateRow 9 6, 634053420⟩, ⟨.privateRow 9 7, 273049920⟩, ⟨.privateRow 10 4, 259339080⟩, ⟨.privateRow 12 0, 227223360⟩, ⟨.privateRow 13 0, 78414336⟩, ⟨.privateRow 14 0, 57517460⟩, ⟨.privateRow 15 5, 79639560⟩, ⟨.hall 10 3, 48823320⟩, ⟨.hall 9 5, 29945160⟩, ⟨.hall 10 5, 1392300⟩, ⟨.hall 15 6, 1535905800⟩, ⟨.hall 8 7, 32447220⟩, ⟨.hall 14 7, 557476920⟩, ⟨.hall 7 9, 60889920⟩, ⟨.hall 11 10, 284029200⟩, ⟨.hall 6 11, 149105385⟩, ⟨.hall 10 11, 137837700⟩, ⟨.hall 5 14, 2175253080⟩, ⟨.hall 4 17, 208797228640⟩]
  caps := #[0, 359050779360, 65255483280, 12793216176, 6808044672, 0, 158165280, 288693405, 40616264, 175732128, 0, 0, 56885400, 0, 164433724, 182033280, 0, 0, 0, 0, 0, 0] }

theorem case_43_22_12_checked :
    (Witness.linear .positive case_43_22_12).check 43 22 12 = true := by
  change case_43_22_12.check 43 22 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_22_13 : Certificate := {
  objectiveScale := 60465600000
  eta := 1935441999691200
  rows := #[⟨.count 2, 510252890827680⟩, ⟨.count 3, 137055222944640⟩, ⟨.count 4, 38070895262400⟩, ⟨.count 5, 11015743939200⟩, ⟨.count 6, 3540774837600⟩, ⟨.count 7, 1207495008720⟩, ⟨.count 8, 447892885440⟩, ⟨.count 9, 188561973600⟩, ⟨.count 10, 101264763600⟩, ⟨.count 11, 76821544800⟩, ⟨.count 12, 75424789440⟩, ⟨.count 14, 63552368880⟩, ⟨.path 12, 9928640475⟩, ⟨.privateRow 3 19, 5247609887520⟩, ⟨.privateRow 10 5, 16237281060⟩, ⟨.privateRow 10 6, 10276128720⟩, ⟨.privateRow 11 3, 1763580000⟩, ⟨.privateRow 12 1, 5063238180⟩, ⟨.privateRow 13 0, 3352212864⟩, ⟨.hall 11 3, 806837850⟩, ⟨.hall 10 4, 1438199490⟩, ⟨.hall 9 6, 1193032800⟩, ⟨.hall 8 7, 1533054900⟩, ⟨.hall 7 9, 2682405180⟩, ⟨.hall 8 9, 272699856⟩, ⟨.hall 12 9, 1676106432⟩, ⟨.hall 11 10, 4761666000⟩, ⟨.hall 6 12, 19585752615⟩, ⟨.hall 5 14, 106395329040⟩, ⟨.hall 4 16, 888388140640⟩, ⟨.hall 3 18, 12672246787200⟩, ⟨.assumptionRow 13, 66552218460⟩]
  caps := #[0, 10378204478460, 2688113888460, 274189955130, 0, 33049153280, 6014459880, 8484457410, 0, 7811021790, 1159994745, 1511010150, 1056069495, 1372417956, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_22_13_checked :
    (Witness.linear .conditional case_43_22_13).check 43 22 13 = true := by
  change case_43_22_13.check 43 22 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_22_14 : Certificate := {
  objectiveScale := 5242618684800000
  eta := 84995111365711747200
  rows := #[⟨.count 2, 24554143283427838080⟩, ⟨.count 3, 7306597292841887040⟩, ⟨.count 4, 2242236206268938880⟩, ⟨.count 5, 708211377813139200⟩, ⟨.count 6, 246087210409840800⟩, ⟨.count 7, 89825892644648160⟩, ⟨.count 8, 34435966077152640⟩, ⟨.count 9, 13494500494675200⟩, ⟨.count 10, 5810132157429600⟩, ⟨.count 11, 3373625123668800⟩, ⟨.count 12, 2473991757357120⟩, ⟨.count 13, 2598940836011520⟩, ⟨.count 15, 4873014067521600⟩, ⟨.path 10, 73462983048000⟩, ⟨.path 11, 822931431894000⟩, ⟨.privateRow 3 19, 347933204421042240⟩, ⟨.privateRow 11 4, 353549097556200⟩, ⟨.privateRow 14 0, 288771204001280⟩, ⟨.hall 12 2, 183050400228696⟩, ⟨.hall 11 3, 117139761238500⟩, ⟨.hall 12 3, 50336628829344⟩, ⟨.hall 11 4, 95659067359440⟩, ⟨.hall 10 5, 183299216575800⟩, ⟨.hall 9 6, 187741919830320⟩, ⟨.hall 8 8, 274725701508960⟩, ⟨.hall 13 8, 108289201500480⟩, ⟨.hall 7 10, 482303443605984⟩, ⟨.hall 9 10, 266587160122080⟩, ⟨.hall 8 11, 215090913969360⟩, ⟨.hall 6 12, 2236198042042965⟩, ⟨.hall 7 12, 1789687303259856⟩, ⟨.hall 5 14, 11993029066178160⟩, ⟨.hall 4 15, 13098481331495560⟩, ⟨.hall 3 17, 99118815962886720⟩, ⟨.hall 2 19, 897170619971401776⟩, ⟨.assumptionRow 14, 2537602197399360⟩]
  caps := #[0, 0, 22736265711926400, 3626351366283360, 11438549154564480, 910859632974720, 1004870129936400, 548637683126715, 448457445159360, 24519808468800, 0, 0, 345139063416000, 0, 40989511272640, 369604617278400, 0, 0, 0, 0, 0, 0] }

theorem case_43_22_14_checked :
    (Witness.linear .conditional case_43_22_14).check 43 22 14 = true := by
  change case_43_22_14.check 43 22 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_23_1_checked :
    (Witness.rising).check 43 23 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_23_2_checked :
    (Witness.rising).check 43 23 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_23_3_checked :
    (Witness.rising).check 43 23 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_23_4_checked :
    (Witness.rising).check 43 23 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_23_5_checked :
    (Witness.rising).check 43 23 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_23_6_checked :
    (Witness.rising).check 43 23 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_23_7_checked :
    (Witness.rising).check 43 23 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_23_8_checked :
    (Witness.rising).check 43 23 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_23_9_checked :
    (Witness.rising).check 43 23 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_23_10 : Certificate := {
  objectiveScale := 865364500000
  eta := 44708710192866720
  rows := #[⟨.count 2, 10423605334222080⟩, ⟨.count 3, 1607620723188480⟩, ⟨.count 4, 256243151324160⟩, ⟨.count 5, 47664276660000⟩, ⟨.count 6, 10104826651920⟩, ⟨.count 7, 2669199492960⟩, ⟨.count 8, 1055947052160⟩, ⟨.count 9, 879955876800⟩, ⟨.path 10, 190367827650⟩, ⟨.path 11, 160498488150⟩, ⟨.privateRow 5 14, 190657106640⟩, ⟨.privateRow 6 11, 385853668200⟩, ⟨.privateRow 6 12, 725556211380⟩, ⟨.privateRow 6 13, 800759847888⟩, ⟨.privateRow 7 8, 166446680400⟩, ⟨.privateRow 7 9, 268962704010⟩, ⟨.privateRow 7 10, 352132003080⟩, ⟨.privateRow 7 11, 383583940740⟩, ⟨.privateRow 7 12, 245130565680⟩, ⟨.privateRow 8 5, 62663524560⟩, ⟨.privateRow 8 6, 107794594908⟩, ⟨.privateRow 8 7, 139326347160⟩, ⟨.privateRow 8 8, 79746001335⟩, ⟨.privateRow 9 2, 27075565440⟩, ⟨.privateRow 9 3, 50515985520⟩, ⟨.privateRow 9 4, 7999598880⟩, ⟨.privateRow 10 0, 23141696760⟩, ⟨.privateRow 11 0, 12307075200⟩, ⟨.hall 5 12, 1416440025⟩, ⟨.hall 4 16, 27808260480⟩, ⟨.hall 6 16, 549541072080⟩, ⟨.hall 4 17, 1048056609600⟩, ⟨.hall 3 19, 8751161194776⟩]
  caps := #[0, 37756580041180, 21226491205920, 1183032390540, 32381939590, 511763812560, 122052150220, 36971224290, 84233575881, 0, 0, 506510550, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_23_10_checked :
    (Witness.linear .positive case_43_23_10).check 43 23 10 = true := by
  change case_43_23_10.check 43 23 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_23_11 : Certificate := {
  objectiveScale := 1165593000000
  eta := 80385357720507840
  rows := #[⟨.count 2, 20631132614252160⟩, ⟨.count 3, 3596979342116160⟩, ⟨.count 4, 674841421013760⟩, ⟨.count 5, 139815211536000⟩, ⟨.count 6, 32157498653280⟩, ⟨.count 7, 8388912692160⟩, ⟨.count 8, 2868004339200⟩, ⟨.count 9, 1183051789920⟩, ⟨.count 10, 1173274502400⟩, ⟨.path 11, 40168128000⟩, ⟨.path 12, 324012438750⟩, ⟨.privateRow 4 19, 35419853589120⟩, ⟨.privateRow 6 12, 996830674840⟩, ⟨.privateRow 6 13, 2873979348240⟩, ⟨.privateRow 7 9, 220541851530⟩, ⟨.privateRow 7 10, 908323313040⟩, ⟨.privateRow 7 11, 1314928775160⟩, ⟨.privateRow 7 12, 2017333766448⟩, ⟨.privateRow 8 6, 12547518984⟩, ⟨.privateRow 8 7, 296758782320⟩, ⟨.privateRow 8 8, 454847563170⟩, ⟨.privateRow 8 9, 660665285280⟩, ⟨.privateRow 8 10, 824551247520⟩, ⟨.privateRow 8 11, 340575515280⟩, ⟨.privateRow 9 4, 69527377920⟩, ⟨.privateRow 9 5, 169690256736⟩, ⟨.privateRow 9 6, 262900397760⟩, ⟨.privateRow 9 7, 164312748600⟩, ⟨.privateRow 10 2, 87995587680⟩, ⟨.privateRow 10 3, 63107946720⟩, ⟨.privateRow 11 0, 42869645280⟩, ⟨.privateRow 12 0, 26887540680⟩, ⟨.privateRow 13 0, 37479602160⟩, ⟨.hall 6 11, 2441469030⟩, ⟨.hall 6 12, 858593736⟩, ⟨.hall 5 13, 16236710490⟩, ⟨.hall 5 14, 6377736365⟩, ⟨.hall 4 16, 448896448000⟩]
  caps := #[0, 221163252470160, 43625674932840, 13285615508880, 1862536022490, 1471739068800, 412417885880, 98855496454, 0, 22709338080, 66406419300, 0, 46174518390, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_23_11_checked :
    (Witness.linear .positive case_43_23_11).check 43 23 11 = true := by
  change case_43_23_11.check 43 23 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_23_12 : Certificate := {
  objectiveScale := 53796600000
  eta := 4580546065935840
  rows := #[⟨.count 2, 1093354954211520⟩, ⟨.count 3, 256927095865440⟩, ⟨.count 4, 58056602123520⟩, ⟨.count 5, 14813754555600⟩, ⟨.count 6, 3761694977040⟩, ⟨.count 7, 1065258754560⟩, ⟨.count 8, 338014797120⟩, ⟨.count 9, 115232317200⟩, ⟨.count 10, 55870214400⟩, ⟨.count 11, 53775081360⟩, ⟨.path 13, 10345575240⟩, ⟨.path 14, 2069115048⟩, ⟨.privateRow 11 8, 7123452336⟩, ⟨.privateRow 11 9, 872972100⟩, ⟨.privateRow 12 0, 569048480⟩, ⟨.privateRow 12 5, 2438779200⟩, ⟨.privateRow 13 0, 931170240⟩, ⟨.privateRow 14 0, 1426685832⟩, ⟨.hall 10 4, 60775680⟩, ⟨.hall 9 5, 133024320⟩, ⟨.hall 10 6, 3488400⟩, ⟨.hall 8 7, 659976856⟩, ⟨.hall 7 9, 652234869⟩, ⟨.hall 6 12, 1618201728⟩, ⟨.hall 5 14, 20017117120⟩, ⟨.hall 4 17, 779476617920⟩]
  caps := #[0, 0, 1383020598960, 63033574032, 17120229984, 2002366080, 0, 0, 0, 2706458040, 0, 21518640, 2034706960, 8921432520, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_23_12_checked :
    (Witness.linear .positive case_43_23_12).check 43 23 12 = true := by
  change case_43_23_12.check 43 23 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_23_13 : Certificate := {
  objectiveScale := 678300000
  eta := 46017502090560
  rows := #[⟨.count 2, 11302544373120⟩, ⟨.count 3, 2770231464000⟩, ⟨.count 4, 771008958720⟩, ⟨.count 5, 221152932000⟩, ⟨.count 6, 66578672160⟩, ⟨.count 7, 21416915520⟩, ⟨.count 8, 7592618880⟩, ⟨.count 9, 3008396160⟩, ⟨.count 10, 1465128000⟩, ⟨.count 11, 966984480⟩, ⟨.count 12, 1002798720⟩, ⟨.path 12, 135656675⟩, ⟨.privateRow 3 20, 184682097600⟩, ⟨.privateRow 6 13, 3879876000⟩, ⟨.privateRow 7 11, 1917767280⟩, ⟨.privateRow 7 12, 6458330736⟩, ⟨.privateRow 8 9, 877448880⟩, ⟨.privateRow 8 10, 2844247560⟩, ⟨.privateRow 8 11, 5071296384⟩, ⟨.privateRow 9 7, 395448900⟩, ⟨.privateRow 9 8, 1299545280⟩, ⟨.privateRow 9 9, 2363739840⟩, ⟨.privateRow 9 10, 3087187488⟩, ⟨.privateRow 10 5, 184497600⟩, ⟨.privateRow 10 6, 625121280⟩, ⟨.privateRow 10 7, 1162334880⟩, ⟨.privateRow 10 8, 1336522320⟩, ⟨.privateRow 11 3, 94744944⟩, ⟨.privateRow 11 4, 328839840⟩, ⟨.privateRow 11 5, 526225140⟩, ⟨.privateRow 12 1, 60775680⟩, ⟨.privateRow 12 2, 180265008⟩, ⟨.privateRow 13 0, 76512240⟩, ⟨.privateRow 14 0, 66512160⟩, ⟨.hall 7 11, 4370190⟩, ⟨.hall 7 12, 106131663⟩, ⟨.hall 6 13, 53405352⟩, ⟨.hall 6 14, 875026152⟩, ⟨.hall 8 14, 10792024320⟩, ⟨.hall 5 15, 1846269425⟩, ⟨.hall 4 16, 2248646400⟩, ⟨.hall 3 19, 315806386896⟩, ⟨.assumptionRow 13, 878536098⟩]
  caps := #[0, 104684725068, 34915575188, 2087213726, 291765045, 538308342, 290805944, 26918136, 0, 27651080, 146392986, 131988288, 11394053, 0, 13178400, 0, 0, 0, 0, 0, 0] }

theorem case_43_23_13_checked :
    (Witness.linear .conditional case_43_23_13).check 43 23 13 = true := by
  change case_43_23_13.check 43 23 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_23_14 : Certificate := {
  objectiveScale := 39070080000
  eta := 1653923163372480
  rows := #[⟨.count 2, 429686644907520⟩, ⟨.count 3, 122855807954880⟩, ⟨.count 4, 36315639360000⟩, ⟨.count 5, 11076270004800⟩, ⟨.count 6, 3522617017920⟩, ⟨.count 7, 1162100459520⟩, ⟨.count 8, 402265543680⟩, ⟨.count 9, 163420377120⟩, ⟨.count 10, 72377323200⟩, ⟨.count 11, 33522128640⟩, ⟨.count 12, 27935107200⟩, ⟨.count 13, 27236729520⟩, ⟨.count 15, 45394549200⟩, ⟨.path 11, 6614536500⟩, ⟨.privateRow 3 20, 17903610204480⟩, ⟨.privateRow 6 13, 97446965616⟩, ⟨.privateRow 7 11, 32640842520⟩, ⟨.privateRow 7 12, 325284369696⟩, ⟨.privateRow 8 9, 8380532160⟩, ⟨.privateRow 8 10, 122565282840⟩, ⟨.privateRow 8 11, 314269956000⟩, ⟨.privateRow 9 7, 349188840⟩, ⟨.privateRow 9 8, 46558512000⟩, ⟨.privateRow 9 9, 135485269920⟩, ⟨.privateRow 9 10, 232140740832⟩, ⟨.privateRow 10 6, 15523031160⟩, ⟨.privateRow 10 7, 59915363040⟩, ⟨.privateRow 10 8, 114279984000⟩, ⟨.privateRow 10 9, 154354165056⟩, ⟨.privateRow 11 4, 5290740000⟩, ⟨.privateRow 11 5, 25998696360⟩, ⟨.privateRow 11 6, 57901858560⟩, ⟨.privateRow 11 7, 55933703280⟩, ⟨.privateRow 12 2, 1117404288⟩, ⟨.privateRow 12 3, 12829456640⟩, ⟨.privateRow 12 4, 29099070000⟩, ⟨.privateRow 13 1, 6285399120⟩, ⟨.privateRow 13 2, 4655851200⟩, ⟨.privateRow 14 0, 2204878104⟩, ⟨.hall 8 10, 1347359616⟩, ⟨.hall 7 11, 1200960189⟩, ⟨.hall 8 11, 2257320384⟩, ⟨.hall 7 12, 8794570356⟩, ⟨.hall 9 13, 304093595520⟩, ⟨.hall 6 14, 93032123184⟩, ⟨.hall 5 15, 134848513800⟩, ⟨.hall 4 16, 155506391040⟩, ⟨.hall 3 18, 1220109915024⟩, ⟨.assumptionRow 14, 28842469110⟩]
  caps := #[0, 0, 0, 151860866040, 85287333456, 11102640120, 756575820, 7626206016, 0, 7178569398, 1538150130, 1934876970, 946431990, 4433843610, 3698651682, 0, 0, 0, 0, 0, 0] }

theorem case_43_23_14_checked :
    (Witness.linear .conditional case_43_23_14).check 43 23 14 = true := by
  change case_43_23_14.check 43 23 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_24_1_checked :
    (Witness.rising).check 43 24 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_24_2_checked :
    (Witness.rising).check 43 24 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_24_3_checked :
    (Witness.rising).check 43 24 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_24_4_checked :
    (Witness.rising).check 43 24 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_24_5_checked :
    (Witness.rising).check 43 24 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_24_6_checked :
    (Witness.rising).check 43 24 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_24_7_checked :
    (Witness.rising).check 43 24 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_24_8_checked :
    (Witness.rising).check 43 24 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_24_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_24_9_checked :
    (Witness.linear .positive case_43_24_9).check 43 24 9 = true := by
  change case_43_24_9.check 43 24 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_24_10 : Certificate := {
  objectiveScale := 136636500000
  eta := 9204925108579200
  rows := #[⟨.count 2, 1887081673276800⟩, ⟨.count 3, 265648901918400⟩, ⟨.count 4, 42262325305200⟩, ⟨.count 5, 7944046110000⟩, ⟨.count 6, 1679598320400⟩, ⟨.count 7, 439977938400⟩, ⟨.count 8, 162954792000⟩, ⟨.count 9, 133326648000⟩, ⟨.path 10, 31849968150⟩, ⟨.path 11, 24313489200⟩, ⟨.privateRow 5 15, 432156108384⟩, ⟨.privateRow 5 16, 513714981780⟩, ⟨.privateRow 6 11, 57688906275⟩, ⟨.privateRow 6 12, 125375421600⟩, ⟨.privateRow 6 13, 174012438600⟩, ⟨.privateRow 6 14, 229999049280⟩, ⟨.privateRow 6 15, 245887141500⟩, ⟨.privateRow 7 8, 26189163000⟩, ⟨.privateRow 7 9, 50050400400⟩, ⟨.privateRow 7 10, 66345879600⟩, ⟨.privateRow 7 11, 75325021200⟩, ⟨.privateRow 7 12, 50050400400⟩, ⟨.privateRow 8 5, 10184674500⟩, ⟨.privateRow 8 6, 20739700800⟩, ⟨.privateRow 8 7, 27498621150⟩, ⟨.privateRow 8 8, 5884478600⟩, ⟨.privateRow 9 2, 4444221600⟩, ⟨.privateRow 9 3, 8660534400⟩, ⟨.privateRow 10 0, 3199839552⟩, ⟨.privateRow 11 0, 1693036800⟩, ⟨.hall 4 16, 2115133020⟩, ⟨.hall 4 17, 3902338440⟩, ⟨.hall 5 18, 256439383200⟩, ⟨.hall 3 19, 211841229600⟩]
  caps := #[0, 0, 1880090912700, 741444303600, 80900519700, 102742996356, 0, 6376999200, 11023635350, 3309852000, 0, 610974000, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_24_10_checked :
    (Witness.linear .positive case_43_24_10).check 43 24 10 = true := by
  change case_43_24_10.check 43 24 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_24_11 : Certificate := {
  objectiveScale := 1503001500000
  eta := 136907055136051200
  rows := #[⟨.count 2, 29473046591788800⟩, ⟨.count 3, 4837606319145600⟩, ⟨.count 4, 915789635560800⟩, ⟨.count 5, 188750535573600⟩, ⟨.count 6, 42943243543200⟩, ⟨.count 7, 11292767085600⟩, ⟨.count 8, 3585005424000⟩, ⟨.count 9, 1466593128000⟩, ⟨.count 10, 1466593128000⟩, ⟨.path 11, 75321846600⟩, ⟨.path 12, 400584584400⟩, ⟨.privateRow 5 15, 3635195499936⟩, ⟨.privateRow 5 16, 15379673268960⟩, ⟨.privateRow 6 12, 1188904860000⟩, ⟨.privateRow 6 13, 4466319257400⟩, ⟨.privateRow 6 14, 6158527174800⟩, ⟨.privateRow 6 15, 9945189153900⟩, ⟨.privateRow 6 16, 1608984577200⟩, ⟨.privateRow 7 9, 247536088800⟩, ⟨.privateRow 7 10, 1363582420200⟩, ⟨.privateRow 7 11, 2118079735200⟩, ⟨.privateRow 7 12, 2970433065600⟩, ⟨.privateRow 7 13, 3641341223520⟩, ⟨.privateRow 7 14, 2727164840400⟩, ⟨.privateRow 8 7, 425719394100⟩, ⟨.privateRow 8 8, 741896955800⟩, ⟨.privateRow 8 9, 1092306340125⟩, ⟨.privateRow 8 10, 1235546512200⟩, ⟨.privateRow 8 11, 194187793800⟩, ⟨.privateRow 9 4, 86909222400⟩, ⟨.privateRow 9 5, 281467368000⟩, ⟨.privateRow 9 6, 436718842560⟩, ⟨.privateRow 9 7, 105015310400⟩, ⟨.privateRow 10 2, 130865232960⟩, ⟨.privateRow 10 3, 61108047000⟩, ⟨.privateRow 11 0, 48886437600⟩, ⟨.privateRow 12 0, 31024085400⟩, ⟨.privateRow 13 0, 51214363200⟩, ⟨.hall 5 15, 38176238100⟩, ⟨.hall 4 17, 65410625280⟩, ⟨.hall 4 18, 5243070432600⟩, ⟨.hall 3 19, 2130517509120⟩, ⟨.hall 3 20, 93210141024000⟩]
  caps := #[0, 0, 21749032905600, 8932638514800, 0, 232314218136, 852569932500, 0, 237911648975, 120972436200, 44095137240, 0, 204098710200, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_24_11_checked :
    (Witness.linear .positive case_43_24_11).check 43 24 11 = true := by
  change case_43_24_11.check 43 24 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_24_12 : Certificate := {
  objectiveScale := 174838950000
  eta := 21712603275483120
  rows := #[⟨.count 2, 4852752967062000⟩, ⟨.count 3, 1027641804789600⟩, ⟨.count 4, 241006470885180⟩, ⟨.count 5, 55052239542300⟩, ⟨.count 6, 14156290168020⟩, ⟨.count 7, 3670149302820⟩, ⟨.count 8, 1129276708560⟩, ⟨.count 9, 410646075840⟩, ⟨.count 10, 153992278440⟩, ⟨.count 11, 188212784760⟩, ⟨.path 13, 42914932060⟩, ⟨.privateRow 13 0, 3360942585⟩, ⟨.privateRow 14 0, 7944046110⟩, ⟨.hall 11 1, 2412984420⟩, ⟨.hall 11 2, 402164070⟩, ⟨.hall 10 4, 752099040⟩, ⟨.hall 9 6, 358956360⟩, ⟨.hall 8 7, 226674294⟩, ⟨.hall 7 10, 1016163225⟩, ⟨.hall 10 10, 499974930⟩]
  caps := #[0, 0, 5947694712960, 162817391880, 0, 179278018920, 5637411780, 0, 2407633800, 15951185250, 20846671560, 0, 0, 83246243080, 0, 0, 0, 0, 0, 0] }

theorem case_43_24_12_checked :
    (Witness.linear .positive case_43_24_12).check 43 24 12 = true := by
  change case_43_24_12.check 43 24 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_24_13 : Certificate := {
  objectiveScale := 54313875000
  eta := 6417518209502400
  rows := #[⟨.count 2, 1505343777537600⟩, ⟨.count 3, 371508990652800⟩, ⟨.count 4, 91379227539600⟩, ⟨.count 5, 25632788781600⟩, ⟨.count 6, 7490100618000⟩, ⟨.count 7, 2304646344000⟩, ⟨.count 8, 768215448000⟩, ⟨.count 9, 293318625600⟩, ⟨.count 10, 125707982400⟩, ⟨.count 11, 76821544800⟩, ⟨.count 12, 76821544800⟩, ⟨.path 11, 15520791000⟩, ⟨.privateRow 5 16, 3578603628600⟩, ⟨.privateRow 6 13, 237780972000⟩, ⟨.privateRow 6 14, 1355351540400⟩, ⟨.privateRow 6 15, 3260571578550⟩, ⟨.privateRow 7 11, 175592102400⟩, ⟨.privateRow 7 12, 588050634600⟩, ⟨.privateRow 7 13, 1309258613520⟩, ⟨.privateRow 7 14, 1941115819500⟩, ⟨.privateRow 7 15, 214002874800⟩, ⟨.privateRow 8 9, 96026931000⟩, ⟨.privateRow 8 10, 272076304500⟩, ⟨.privateRow 8 11, 571893722400⟩, ⟨.privateRow 8 12, 841195915560⟩, ⟨.privateRow 8 13, 933061679550⟩, ⟨.privateRow 9 7, 48110462400⟩, ⟨.privateRow 9 8, 131818787100⟩, ⟨.privateRow 9 9, 103093848000⟩, ⟨.privateRow 9 10, 733684551600⟩, ⟨.privateRow 9 11, 34453298880⟩, ⟨.privateRow 10 5, 24303543264⟩, ⟨.privateRow 10 6, 67277049840⟩, ⟨.privateRow 10 7, 139850130420⟩, ⟨.privateRow 10 8, 92784463200⟩, ⟨.privateRow 11 3, 13121035200⟩, ⟨.privateRow 11 4, 37014017040⟩, ⟨.privateRow 11 5, 37764126400⟩, ⟨.privateRow 12 1, 8535727200⟩, ⟨.privateRow 12 2, 11930618700⟩, ⟨.privateRow 13 0, 5487253200⟩, ⟨.privateRow 14 0, 5404113000⟩, ⟨.hall 6 15, 61339331625⟩, ⟨.hall 7 16, 1034831397600⟩, ⟨.hall 5 17, 1361747987600⟩, ⟨.hall 4 18, 2601824425200⟩, ⟨.hall 3 19, 3538180863360⟩, ⟨.hall 2 21, 49903741087200⟩, ⟨.assumptionRow 13, 70113108780⟩]
  caps := #[0, 41353300203600, 0, 1472296545720, 353927831400, 30545709480, 90816447150, 3272532120, 0, 24885157440, 7445547696, 29113571500, 0, 39532638420, 0, 0, 0, 0, 0, 0] }

theorem case_43_24_13_checked :
    (Witness.linear .conditional case_43_24_13).check 43 24 13 = true := by
  change case_43_24_13.check 43 24 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_24_14 : Certificate := {
  objectiveScale := 94962000000
  eta := 6611988458275200
  rows := #[⟨.count 2, 1699814026310400⟩, ⟨.count 3, 447408676915200⟩, ⟨.count 4, 120113977183200⟩, ⟨.count 5, 35165644113600⟩, ⟨.count 6, 10622324512800⟩, ⟨.count 7, 3324277756800⟩, ⟨.count 8, 1075501627200⟩, ⟨.count 9, 426645273600⟩, ⟨.count 10, 186657307200⟩, ⟨.count 11, 97772875200⟩, ⟨.count 12, 48886437600⟩, ⟨.count 13, 90789098400⟩, ⟨.path 10, 16134037920⟩, ⟨.path 11, 5434228800⟩, ⟨.privateRow 2 22, 86431221676800⟩, ⟨.privateRow 5 16, 6492933687240⟩, ⟨.privateRow 6 13, 103398695400⟩, ⟨.privateRow 6 14, 2303016796080⟩, ⟨.privateRow 6 15, 6408197195400⟩, ⟨.privateRow 7 11, 57865579200⟩, ⟨.privateRow 7 12, 859004546400⟩, ⟨.privateRow 7 13, 2489018051520⟩, ⟨.privateRow 7 14, 4378828053600⟩, ⟨.privateRow 8 9, 18332414100⟩, ⟨.privateRow 8 10, 328237509600⟩, ⟨.privateRow 8 11, 1008282775500⟩, ⟨.privateRow 8 12, 1877239203840⟩, ⟨.privateRow 8 13, 2556353299500⟩, ⟨.privateRow 8 14, 833785352400⟩, ⟨.privateRow 9 8, 125919612000⟩, ⟨.privateRow 9 9, 426222014400⟩, ⟨.privateRow 9 10, 849340128000⟩, ⟨.privateRow 9 11, 1230753101760⟩, ⟨.privateRow 9 12, 1054021222800⟩, ⟨.privateRow 10 6, 40590557280⟩, ⟨.privateRow 10 7, 187657257060⟩, ⟨.privateRow 10 8, 409884209280⟩, ⟨.privateRow 10 9, 643078865520⟩, ⟨.privateRow 10 10, 5866372512⟩, ⟨.privateRow 11 4, 13332664800⟩, ⟨.privateRow 11 5, 55305868800⟩, ⟨.privateRow 11 6, 259616611800⟩, ⟨.privateRow 11 7, 99465912000⟩, ⟨.privateRow 12 1, 1697445750⟩, ⟨.privateRow 12 3, 38294376120⟩, ⟨.privateRow 12 4, 81930048200⟩, ⟨.privateRow 13 1, 16507108800⟩, ⟨.privateRow 13 2, 12570798240⟩, ⟨.privateRow 14 0, 5502369600⟩, ⟨.hall 6 15, 81368987700⟩, ⟨.hall 6 16, 1000460260800⟩, ⟨.hall 7 16, 6754955407200⟩, ⟨.hall 5 17, 3485469587600⟩, ⟨.hall 4 18, 6030785320560⟩, ⟨.hall 3 19, 8358649659360⟩, ⟨.hall 2 21, 154528547846400⟩, ⟨.assumptionRow 14, 80028038475⟩]
  caps := #[0, 0, 9387057799350, 0, 274521961350, 0, 77171244150, 6405141600, 4131715770, 28461372030, 0, 1268958075, 57688781920, 4629465330, 0, 94962000000, 0, 0, 0, 0] }

theorem case_43_24_14_checked :
    (Witness.linear .conditional case_43_24_14).check 43 24 14 = true := by
  change case_43_24_14.check 43 24 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_24_15 : Certificate := {
  objectiveScale := 63063000000
  eta := 4148698640486400
  rows := #[⟨.count 2, 1073187669153600⟩, ⟨.count 3, 282172517827200⟩, ⟨.count 4, 75945080811600⟩, ⟨.count 5, 21290043574800⟩, ⟨.count 6, 6037475043600⟩, ⟨.count 7, 1808798191200⟩, ⟨.count 8, 554046292800⟩, ⟨.count 9, 159991977600⟩, ⟨.count 10, 53330659200⟩, ⟨.count 11, 16295479200⟩, ⟨.count 12, 24443218800⟩, ⟨.count 13, 45394549200⟩, ⟨.path 10, 19101782700⟩, ⟨.privateRow 2 22, 93633823483200⟩, ⟨.privateRow 5 16, 4491034067520⟩, ⟨.privateRow 6 13, 18914395500⟩, ⟨.privateRow 6 14, 1482888607200⟩, ⟨.privateRow 6 15, 4592415227400⟩, ⟨.privateRow 7 11, 1496523600⟩, ⟨.privateRow 7 12, 492356264400⟩, ⟨.privateRow 7 13, 1680995075760⟩, ⟨.privateRow 7 14, 3379274999100⟩, ⟨.privateRow 7 15, 2865676413600⟩, ⟨.privateRow 8 10, 151315164000⟩, ⟨.privateRow 8 11, 622962590250⟩, ⟨.privateRow 8 12, 1376560605420⟩, ⟨.privateRow 8 13, 2189705017500⟩, ⟨.privateRow 8 14, 1975826853000⟩, ⟨.privateRow 9 8, 42405281100⟩, ⟨.privateRow 9 9, 225808783200⟩, ⟨.privateRow 9 10, 578983314000⟩, ⟨.privateRow 9 11, 1009134584640⟩, ⟨.privateRow 9 12, 1319933815200⟩, ⟨.privateRow 9 13, 905633601600⟩, ⟨.privateRow 10 6, 9036583920⟩, ⟨.privateRow 10 7, 79162697250⟩, ⟨.privateRow 10 8, 246273365520⟩, ⟨.privateRow 10 9, 432644972760⟩, ⟨.privateRow 10 10, 832224936816⟩, ⟨.privateRow 11 5, 24196317600⟩, ⟨.privateRow 11 6, 105365087100⟩, ⟨.privateRow 11 7, 248241520800⟩, ⟨.privateRow 11 8, 226655301600⟩, ⟨.privateRow 12 3, 2240628390⟩, ⟨.privateRow 12 4, 43001959000⟩, ⟨.privateRow 12 5, 129854599875⟩, ⟨.privateRow 12 6, 34045911900⟩, ⟨.privateRow 13 2, 8729721000⟩, ⟨.privateRow 13 3, 55870214400⟩, ⟨.privateRow 14 1, 16644668040⟩, ⟨.privateRow 15 0, 4236824592⟩, ⟨.hall 7 14, 15924038130⟩, ⟨.hall 7 15, 307966583925⟩, ⟨.hall 8 15, 340168128300⟩, ⟨.hall 6 16, 1247014969200⟩, ⟨.hall 5 17, 3020905487600⟩, ⟨.hall 4 18, 4901058342180⟩, ⟨.hall 3 19, 6672998732400⟩, ⟨.hall 2 21, 128992050532800⟩, ⟨.assumptionRow 15, 22938071100⟩]
  caps := #[0, 30619727707800, 91562360400, 0, 0, 17279262000, 14715356700, 38474367360, 13835811990, 8663993520, 0, 11136953100, 0, 0, 98730748620, 0, 63063000000, 0, 0, 0] }

theorem case_43_24_15_checked :
    (Witness.linear .conditional case_43_24_15).check 43 24 15 = true := by
  change case_43_24_15.check 43 24 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_25_1_checked :
    (Witness.rising).check 43 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_25_2_checked :
    (Witness.rising).check 43 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_25_3_checked :
    (Witness.rising).check 43 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_25_4_checked :
    (Witness.rising).check 43 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_25_5_checked :
    (Witness.rising).check 43 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_25_6_checked :
    (Witness.rising).check 43 25 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_25_7_checked :
    (Witness.rising).check 43 25 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_25_8_checked :
    (Witness.rising).check 43 25 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_25_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_25_9_checked :
    (Witness.linear .positive case_43_25_9).check 43 25 9 = true := by
  change case_43_25_9.check 43 25 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_25_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_25_10_checked :
    (Witness.linear .positive case_43_25_10).check 43 25 10 = true := by
  change case_43_25_10.check 43 25 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_25_11 : Certificate := {
  objectiveScale := 10224500000
  eta := 1584572397408000
  rows := #[⟨.count 2, 303598745049600⟩, ⟨.count 3, 59171794882200⟩, ⟨.count 4, 12317054349600⟩, ⟨.count 5, 2639368789200⟩, ⟨.count 6, 581648839200⟩, ⟨.count 7, 134437703400⟩, ⟨.count 8, 37246809600⟩, ⟨.count 9, 12570798240⟩, ⟨.count 10, 9311702400⟩, ⟨.path 11, 3635259628⟩, ⟨.path 12, 454274535⟩, ⟨.privateRow 3 21, 1165126762800⟩, ⟨.privateRow 3 22, 7406877277800⟩, ⟨.privateRow 6 15, 425079214560⟩, ⟨.privateRow 6 18, 1253837356200⟩, ⟨.privateRow 8 14, 6983776800⟩, ⟨.privateRow 8 17, 224062839000⟩, ⟨.privateRow 9 10, 26538351840⟩, ⟨.privateRow 11 0, 271591320⟩, ⟨.privateRow 11 4, 687796200⟩, ⟨.privateRow 12 1, 1336638600⟩, ⟨.hall 9 3, 9976824⟩, ⟨.hall 12 3, 108721800⟩, ⟨.hall 13 3, 281013876⟩, ⟨.hall 8 11, 7900200⟩, ⟨.hall 5 14, 17381650⟩, ⟨.hall 10 14, 310390080⟩]
  caps := #[0, 0, 666513274570, 0, 26345060170, 0, 405239406, 2336148815, 1377159355, 1288961388, 2151344195, 2745813383, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_25_11_checked :
    (Witness.linear .positive case_43_25_11).check 43 25 11 = true := by
  change case_43_25_11.check 43 25 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_25_12 : Certificate := {
  objectiveScale := 2862860000
  eta := 459525995248320
  rows := #[⟨.count 2, 106880961707520⟩, ⟨.count 3, 24001611313680⟩, ⟨.count 4, 5965449025536⟩, ⟨.count 5, 1453634342160⟩, ⟨.count 6, 358500542400⟩, ⟨.count 7, 98587649160⟩, ⟨.count 8, 28245497280⟩, ⟨.count 9, 9777287520⟩, ⟨.count 10, 4345461120⟩, ⟨.count 11, 2987504520⟩, ⟨.path 12, 780845065⟩, ⟨.privateRow 12 4, 85357272⟩, ⟨.privateRow 13 0, 65659440⟩, ⟨.privateRow 13 6, 365816880⟩, ⟨.privateRow 13 9, 213393180⟩, ⟨.hall 12 1, 65659440⟩, ⟨.hall 13 2, 168127960⟩, ⟨.hall 11 4, 2558160⟩, ⟨.hall 9 5, 29695974⟩, ⟨.hall 8 9, 3262224⟩, ⟨.hall 10 10, 71339072⟩, ⟨.hall 7 11, 41198080⟩]
  caps := #[0, 728204226750, 239498279020, 46697540890, 0, 0, 2249877630, 673873200, 0, 0, 0, 0, 2923366193, 0, 0, 0, 0, 0, 0] }

theorem case_43_25_12_checked :
    (Witness.linear .positive case_43_25_12).check 43 25 12 = true := by
  change case_43_25_12.check 43 25 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_25_13 : Certificate := {
  objectiveScale := 701316000000
  eta := 138491627533459200
  rows := #[⟨.count 2, 31728732004569600⟩, ⟨.count 3, 7235437196988000⟩, ⟨.count 4, 1822258257019200⟩, ⟨.count 5, 459392837904000⟩, ⟨.count 6, 127216478188800⟩, ⟨.count 7, 38135495197800⟩, ⟨.count 8, 12743064734400⟩, ⟨.count 9, 4722429872160⟩, ⟨.count 10, 2248776129600⟩, ⟨.count 11, 2061378118800⟩, ⟨.path 11, 248067391572⟩, ⟨.privateRow 4 18, 16748697215250⟩, ⟨.privateRow 4 19, 241181239899600⟩, ⟨.privateRow 5 16, 30473058247632⟩, ⟨.privateRow 5 17, 92261394945720⟩, ⟨.privateRow 5 18, 190648027730160⟩, ⟨.privateRow 6 14, 19435850834400⟩, ⟨.privateRow 6 15, 39814045951680⟩, ⟨.privateRow 6 16, 75313921983300⟩, ⟨.privateRow 6 17, 96197645544000⟩, ⟨.privateRow 7 11, 883447765200⟩, ⟨.privateRow 7 12, 8939650005000⟩, ⟨.privateRow 7 13, 18331541127900⟩, ⟨.privateRow 7 14, 32069153876760⟩, ⟨.privateRow 7 15, 40380924934350⟩, ⟨.privateRow 7 16, 36957564844200⟩, ⟨.privateRow 8 9, 947401054600⟩, ⟨.privateRow 8 10, 4040769607875⟩, ⟨.privateRow 8 11, 8339211480600⟩, ⟨.privateRow 8 12, 10478672103900⟩, ⟨.privateRow 8 13, 27491288184360⟩, ⟨.privateRow 9 7, 652145077584⟩, ⟨.privateRow 9 8, 2065542519040⟩, ⟨.privateRow 9 9, 1152497766420⟩, ⟨.privateRow 9 10, 13000067720640⟩, ⟨.privateRow 10 5, 395239440960⟩, ⟨.privateRow 10 6, 1176859507824⟩, ⟨.privateRow 10 7, 2165488124800⟩, ⟨.privateRow 10 8, 1227456970740⟩, ⟨.privateRow 11 3, 242055763950⟩, ⟨.privateRow 11 4, 741073951800⟩, ⟨.privateRow 11 5, 281097016200⟩, ⟨.privateRow 12 0, 52586176500⟩, ⟨.privateRow 12 1, 113262534000⟩, ⟨.privateRow 12 2, 98160862800⟩, ⟨.privateRow 13 0, 67957520400⟩, ⟨.privateRow 14 0, 63804560820⟩, ⟨.hall 5 18, 5309211087180⟩, ⟨.hall 6 18, 15995054275200⟩, ⟨.hall 5 19, 87667466566680⟩, ⟨.hall 4 20, 543104421699840⟩, ⟨.hall 3 21, 1109068277417100⟩, ⟨.hall 2 22, 1379510087155200⟩, ⟨.assumptionRow 13, 974618845200⟩]
  caps := #[0, 0, 0, 0, 2421139200480, 1647707577516, 2303835449916, 437088782185, 291138152305, 0, 0, 0, 1456308555900, 0, 0, 0, 0, 0, 0] }

theorem case_43_25_13_checked :
    (Witness.linear .conditional case_43_25_13).check 43 25 13 = true := by
  change case_43_25_13.check 43 25 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_25_14 : Certificate := {
  objectiveScale := 94999320531500000
  eta := 17238014611666269220800
  rows := #[⟨.count 2, 3796607869327317844800⟩, ⟨.count 3, 932939744287341690900⟩, ⟨.count 4, 229918799540008378800⟩, ⟨.count 5, 57269151533774980800⟩, ⟨.count 6, 14770776639932913600⟩, ⟨.count 7, 4081398808402515600⟩, ⟨.count 8, 1154335016517883200⟩, ⟨.count 9, 445243506371183520⟩, ⟨.count 10, 164905002359697600⟩, ⟨.count 11, 113372189122292100⟩, ⟨.path 9, 43991458157687040⟩, ⟨.path 10, 10560010185384660⟩, ⟨.privateRow 2 23, 224023445705649189600⟩, ⟨.privateRow 4 18, 9137798443256743260⟩, ⟨.privateRow 4 19, 44018641963215279360⟩, ⟨.privateRow 5 16, 6013260911046372984⟩, ⟨.privateRow 5 17, 16780703592800977830⟩, ⟨.privateRow 5 18, 35793219708609363000⟩, ⟨.privateRow 6 14, 2855899430747262900⟩, ⟨.privateRow 6 15, 6795852936530537880⟩, ⟨.privateRow 6 16, 14033857410638014950⟩, ⟨.privateRow 6 17, 19975099988213370000⟩, ⟨.privateRow 7 12, 1193878563002096400⟩, ⟨.privateRow 7 13, 2853200092911017850⟩, ⟨.privateRow 7 14, 5833808931692802060⟩, ⟨.privateRow 7 15, 8421934049084556000⟩, ⟨.privateRow 7 16, 9242532751303051200⟩, ⟨.privateRow 8 9, 11451736274979000⟩, ⟨.privateRow 8 10, 458642037812908950⟩, ⟨.privateRow 8 11, 1225008588957753600⟩, ⟨.privateRow 8 12, 2588664984959002950⟩, ⟨.privateRow 8 13, 3147624232540727940⟩, ⟨.privateRow 8 14, 5812901333179340400⟩, ⟨.privateRow 9 7, 1649050023596976⟩, ⟨.privateRow 9 8, 183227780399664000⟩, ⟨.privateRow 9 9, 528726663815780430⟩, ⟨.privateRow 9 10, 792721904200546320⟩, ⟨.privateRow 9 11, 2797888206702869280⟩, ⟨.privateRow 9 12, 534292207645420224⟩, ⟨.privateRow 10 6, 66786525955677528⟩, ⟨.privateRow 10 7, 243692947931553120⟩, ⟨.privateRow 10 8, 606025883671888680⟩, ⟨.privateRow 10 9, 739716724870643520⟩, ⟨.privateRow 11 4, 22487045776322400⟩, ⟨.privateRow 11 5, 60808719620138490⟩, ⟨.privateRow 11 6, 431730457566708300⟩, ⟨.privateRow 12 2, 4049006754367575⟩, ⟨.privateRow 12 3, 54477545422400100⟩, ⟨.privateRow 12 4, 82599737789098530⟩, ⟨.privateRow 13 1, 24294040526205450⟩, ⟨.privateRow 13 2, 8834196554983800⟩, ⟨.privateRow 14 0, 7018278374237130⟩, ⟨.hall 6 18, 10975791782997241200⟩, ⟨.hall 5 19, 47373379026100627500⟩, ⟨.hall 4 20, 117008737055281431360⟩, ⟨.hall 3 21, 229717821568382497350⟩, ⟨.hall 2 22, 340392604001261011200⟩, ⟨.assumptionRow 14, 87209376247917000⟩]
  caps := #[0, 58681457081935490880, 9934656198434071720, 1157070306439407360, 305503805520113200, 487563351844264696, 0, 167064398605472940, 28740085932071360, 0, 54899593312856292, 0, 289804791500078855, 87209376247917000, 0, 94999320531500000, 0, 0, 0] }

theorem case_43_25_14_checked :
    (Witness.linear .conditional case_43_25_14).check 43 25 14 = true := by
  change case_43_25_14.check 43 25 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_25_15 : Certificate := {
  objectiveScale := 136007622267048000000
  eta := 32793919704482499705542400
  rows := #[⟨.count 2, 6732777055822243307481600⟩, ⟨.count 3, 1514165626493731333722600⟩, ⟨.count 4, 333802008526018523531040⟩, ⟨.count 5, 72271984848814208858400⟩, ⟨.count 6, 15742926965629550887200⟩, ⟨.count 7, 3364206340014895775400⟩, ⟨.count 8, 859649777301103588800⟩, ⟨.count 9, 238056861406459455360⟩, ⟨.count 10, 132253811892477475200⟩, ⟨.count 11, 90924495676078264200⟩, ⟨.path 8, 158568611779231505280⟩, ⟨.path 9, 33255437512754096640⟩, ⟨.privateRow 2 23, 368789754462173439595200⟩, ⟨.privateRow 4 18, 15011634236120521419420⟩, ⟨.privateRow 4 19, 70842305397755111580360⟩, ⟨.privateRow 5 16, 9172463123802775292496⟩, ⟨.privateRow 5 17, 25886203918979481817740⟩, ⟨.privateRow 5 18, 59258524648622740721280⟩, ⟨.privateRow 6 14, 3922742527739376541200⟩, ⟨.privateRow 6 15, 9949737669696564339600⟩, ⟨.privateRow 6 16, 22471339645659342438000⟩, ⟨.privateRow 6 17, 35581785974571960723600⟩, ⟨.privateRow 7 11, 17860168793515373325⟩, ⟨.privateRow 7 12, 1408401882002926582200⟩, ⟨.privateRow 7 13, 3883774886735342999400⟩, ⟨.privateRow 7 14, 8959959588194112377880⟩, ⟨.privateRow 7 15, 14723273692690673210100⟩, ⟨.privateRow 7 16, 18708797419825437124200⟩, ⟨.privateRow 8 10, 465988040339901104025⟩, ⟨.privateRow 8 11, 1491397896608920099800⟩, ⟨.privateRow 8 12, 3747191336953528464000⟩, ⟨.privateRow 8 13, 6513500235704515653600⟩, ⟨.privateRow 8 14, 8805210819903851903550⟩, ⟨.privateRow 8 15, 8632316513731915204200⟩, ⟨.privateRow 9 8, 125641121297853601440⟩, ⟨.privateRow 9 9, 566211632164669190700⟩, ⟨.privateRow 9 10, 1615385845258117732800⟩, ⟨.privateRow 9 11, 3103556119076804751360⟩, ⟨.privateRow 9 12, 4525725442960579201344⟩, ⟨.privateRow 9 13, 1848247021197372715920⟩, ⟨.privateRow 10 6, 21821878962258783408⟩, ⟨.privateRow 10 7, 196176487640508254880⟩, ⟨.privateRow 10 8, 714997170543706350300⟩, ⟨.privateRow 10 9, 1572875691435535687200⟩, ⟨.privateRow 10 10, 1994828329378201917600⟩, ⟨.privateRow 11 5, 50421765784007037420⟩, ⟨.privateRow 11 6, 305836940001354161400⟩, ⟨.privateRow 11 7, 842084817909133924125⟩, ⟨.privateRow 11 8, 448718290349477148000⟩, ⟨.privateRow 12 4, 110408316178095035100⟩, ⟨.privateRow 12 5, 432973788933706020000⟩, ⟨.privateRow 13 2, 11808376061828346000⟩, ⟨.privateRow 13 3, 150674878548929694960⟩, ⟨.privateRow 14 1, 36842133312904439520⟩, ⟨.hall 6 17, 460775263802080827600⟩, ⟨.hall 7 17, 394006147929672478200⟩, ⟨.hall 6 18, 24996716239850568813600⟩, ⟨.hall 5 19, 99357093189351122645520⟩, ⟨.hall 4 20, 217131159464786364557760⟩, ⟨.hall 3 21, 401026621110964824175200⟩, ⟨.hall 2 22, 578880684819108364492800⟩, ⟨.assumptionRow 15, 67717187662894554400⟩]
  caps := #[0, 121002817859536198829760, 1850082071948872267520, 2362715818199310537040, 374156884308488969012, 0, 215545006451556015520, 776423634734459550, 96662140141422011585, 6847072092319370912, 0, 0, 70277009429711184800, 67717187662894554400, 112422706001640483680, 1156351412740537445600, 136007622267048000000, 0, 0] }

theorem case_43_25_15_checked :
    (Witness.linear .conditional case_43_25_15).check 43 25 15 = true := by
  change case_43_25_15.check 43 25 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_25_16 : Certificate := {
  objectiveScale := 277200000
  eta := 31026592396800
  rows := #[⟨.count 2, 8147739600000⟩, ⟨.count 3, 2260997739000⟩, ⟨.count 4, 638782784640⟩, ⟨.count 5, 182742159600⟩, ⟨.count 6, 52646932800⟩, ⟨.count 7, 15355355400⟩, ⟨.count 8, 4786084800⟩, ⟨.count 9, 1435825440⟩, ⟨.count 10, 455817600⟩, ⟨.path 10, 11771760⟩, ⟨.path 11, 78029952⟩, ⟨.privateRow 4 18, 4481256780⟩, ⟨.privateRow 5 16, 2467601136⟩, ⟨.privateRow 6 14, 850588200⟩, ⟨.privateRow 6 15, 15471751680⟩, ⟨.privateRow 6 16, 32680494000⟩, ⟨.privateRow 7 12, 191862000⟩, ⟨.privateRow 7 14, 27603825480⟩, ⟨.privateRow 7 15, 24174612000⟩, ⟨.privateRow 8 11, 1648269000⟩, ⟨.privateRow 8 13, 27064170000⟩, ⟨.privateRow 8 15, 25535281800⟩, ⟨.privateRow 9 10, 3327468480⟩, ⟨.privateRow 9 13, 42983599680⟩, ⟨.privateRow 10 8, 669482100⟩, ⟨.privateRow 10 9, 690238080⟩, ⟨.privateRow 10 12, 22306573800⟩, ⟨.privateRow 11 10, 9594960480⟩, ⟨.privateRow 12 4, 40291020⟩, ⟨.privateRow 12 9, 4333523040⟩, ⟨.privateRow 13 3, 116396280⟩, ⟨.privateRow 13 6, 25581600⟩, ⟨.privateRow 13 9, 1477337400⟩, ⟨.privateRow 13 11, 1208730600⟩, ⟨.privateRow 14 3, 155195040⟩, ⟨.privateRow 14 9, 543182640⟩, ⟨.privateRow 15 2, 90530440⟩, ⟨.hall 6 14, 64079400⟩, ⟨.hall 7 14, 109220265⟩, ⟨.hall 5 16, 304143840⟩]
  caps := #[0, 0, 0, 1243790856, 0, 0, 381421656, 0, 1199520, 20137572, 0, 275686152, 18267480, 0, 708935920, 0, 2217600000, 277200000, 0] }

theorem case_43_25_16_checked :
    (Witness.linear .negative case_43_25_16).check 43 25 16 = true := by
  change case_43_25_16.check 43 25 16 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_26_1_checked :
    (Witness.rising).check 43 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_26_2_checked :
    (Witness.rising).check 43 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_26_3_checked :
    (Witness.rising).check 43 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_26_4_checked :
    (Witness.rising).check 43 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_26_5_checked :
    (Witness.rising).check 43 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_26_6_checked :
    (Witness.rising).check 43 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_26_7_checked :
    (Witness.rising).check 43 26 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_26_8_checked :
    (Witness.rising).check 43 26 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_26_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_26_9_checked :
    (Witness.linear .positive case_43_26_9).check 43 26 9 = true := by
  change case_43_26_9.check 43 26 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_26_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_26_10_checked :
    (Witness.linear .positive case_43_26_10).check 43 26 10 = true := by
  change case_43_26_10.check 43 26 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_26_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_26_11_checked :
    (Witness.linear .positive case_43_26_11).check 43 26 11 = true := by
  change case_43_26_11.check 43 26 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_26_12 : Certificate := {
  objectiveScale := 240625
  eta := 116241084960
  rows := #[⟨.count 2, 23967933990⟩, ⟨.count 3, 5391087702⟩, ⟨.count 4, 1156203048⟩, ⟨.count 5, 271591320⟩, ⟨.count 6, 61928790⟩, ⟨.count 7, 15668730⟩, ⟨.count 8, 4178328⟩, ⟨.count 9, 1139544⟩, ⟨.count 10, 474810⟩, ⟨.path 10, 187148⟩]
  caps := #[0, 0, 0, 0, 0, 0, 0, 51702, 0, 90298, 0, 240625, 0, 0, 0, 0, 0, 0] }

theorem case_43_26_12_checked :
    (Witness.linear .positive case_43_26_12).check 43 26 12 = true := by
  change case_43_26_12.check 43 26 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_26_13 : Certificate := {
  objectiveScale := 91171080000
  eta := 38588998383936000
  rows := #[⟨.count 2, 7717799676787200⟩, ⟨.count 3, 1704347428623840⟩, ⟨.count 4, 383593019649840⟩, ⟨.count 5, 91878567580800⟩, ⟨.count 6, 22969641895200⟩, ⟨.count 7, 6465231372600⟩, ⟨.count 8, 1799020903680⟩, ⟨.count 9, 674632838880⟩, ⟨.count 10, 281097016200⟩, ⟨.path 10, 64217593440⟩, ⟨.privateRow 2 24, 100492183291500⟩, ⟨.privateRow 3 22, 163467284820840⟩, ⟨.privateRow 4 19, 27994251059775⟩, ⟨.privateRow 4 20, 65846306766240⟩, ⟨.privateRow 4 21, 111115642668030⟩, ⟨.privateRow 5 16, 2414757224880⟩, ⟨.privateRow 5 17, 16679493806976⟩, ⟨.privateRow 5 18, 27563570274240⟩, ⟨.privateRow 5 19, 45939283790400⟩, ⟨.privateRow 5 20, 45762594237360⟩, ⟨.privateRow 6 14, 2850170766300⟩, ⟨.privateRow 6 15, 7178013092250⟩, ⟨.privateRow 6 16, 12059061994980⟩, ⟨.privateRow 6 17, 16435809465075⟩, ⟨.privateRow 6 18, 24049411386000⟩, ⟨.privateRow 6 19, 9717925417200⟩, ⟨.privateRow 7 11, 129393864600⟩, ⟨.privateRow 7 12, 1721719224225⟩, ⟨.privateRow 7 13, 3378900868200⟩, ⟨.privateRow 7 14, 5206987585800⟩, ⟨.privateRow 7 15, 8216064216360⟩, ⟨.privateRow 7 16, 7679972049750⟩, ⟨.privateRow 8 9, 191145971016⟩, ⟨.privateRow 8 10, 858907549500⟩, ⟨.privateRow 8 11, 1721719224225⟩, ⟨.privateRow 8 12, 2513810459160⟩, ⟨.privateRow 8 13, 3612096658170⟩, ⟨.privateRow 9 7, 154461390720⟩, ⟨.privateRow 9 8, 467245706928⟩, ⟨.privateRow 9 9, 916168052800⟩, ⟨.privateRow 9 10, 1224333670560⟩, ⟨.privateRow 10 5, 107753856210⟩, ⟨.privateRow 10 6, 293874153300⟩, ⟨.privateRow 10 7, 371048061384⟩, ⟨.privateRow 11 3, 71046498600⟩, ⟨.privateRow 11 4, 117123756750⟩, ⟨.privateRow 12 1, 42068941200⟩, ⟨.hall 5 20, 2944825884000⟩, ⟨.hall 4 21, 35394130011240⟩, ⟨.hall 3 22, 100317414277080⟩, ⟨.hall 2 23, 194284887696900⟩, ⟨.assumptionRow 13, 127031704800⟩]
  caps := #[0, 0, 0, 875862607620, 0, 558446072184, 0, 0, 193866529857, 0, 0, 272532991500, 824881200, 967021255200, 91171080000, 0, 0, 0] }

theorem case_43_26_13_checked :
    (Witness.linear .conditional case_43_26_13).check 43 26 13 = true := by
  change case_43_26_13.check 43 26 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_26_14 : Certificate := {
  objectiveScale := 164670644892600000
  eta := 59398495864107569769600
  rows := #[⟨.count 2, 12521504954404032186600⟩, ⟨.count 3, 2592391980509779528080⟩, ⟨.count 4, 596861399118756451680⟩, ⟨.count 5, 135524599429189370400⟩, ⟨.count 6, 31115341705681233000⟩, ⟨.count 7, 7920268797809768400⟩, ⟨.count 8, 2112071679415938240⟩, ⟨.count 9, 704023893138646080⟩, ⟨.count 10, 440014933211653800⟩, ⟨.path 8, 150584795966404800⟩, ⟨.path 9, 83275355345101920⟩, ⟨.privateRow 2 24, 1195520573536063374600⟩, ⟨.privateRow 3 21, 139826967665036652000⟩, ⟨.privateRow 3 22, 425773116540036605340⟩, ⟨.privateRow 4 19, 96630422297087829150⟩, ⟨.privateRow 4 20, 171387911795144924880⟩, ⟨.privateRow 4 21, 288992379241988251830⟩, ⟨.privateRow 5 16, 7421585206836560760⟩, ⟨.privateRow 5 17, 38444733307463923440⟩, ⟨.privateRow 5 18, 69698365420725961920⟩, ⟨.privateRow 5 19, 120128267385193026960⟩, ⟨.privateRow 5 20, 129716402310795540240⟩, ⟨.privateRow 6 14, 5498690015712979800⟩, ⟨.privateRow 6 15, 15327186840205940700⟩, ⟨.privateRow 6 16, 28049904337640044860⟩, ⟨.privateRow 6 17, 49064284189606610925⟩, ⟨.privateRow 6 18, 57966729177620963700⟩, ⟨.privateRow 6 19, 44252930425857753600⟩, ⟨.privateRow 7 12, 2828667427789203000⟩, ⟨.privateRow 7 13, 6716962653924837600⟩, ⟨.privateRow 7 14, 11807067374512710300⟩, ⟨.privateRow 7 15, 21007570097047814280⟩, ⟨.privateRow 7 16, 25882306964271207450⟩, ⟨.privateRow 7 17, 16448177265292773000⟩, ⟨.privateRow 8 9, 17600597328466152⟩, ⟨.privateRow 8 10, 1251598032246481920⟩, ⟨.privateRow 8 11, 3168107519123907360⟩, ⟨.privateRow 8 12, 5493900737528363160⟩, ⟨.privateRow 8 13, 9724330023977548980⟩, ⟨.privateRow 8 14, 11325984380867968812⟩, ⟨.privateRow 9 8, 539751651406295328⟩, ⟨.privateRow 9 9, 1555805887306390720⟩, ⟨.privateRow 9 10, 2102293569789012600⟩, ⟨.privateRow 9 11, 6671464511170979520⟩, ⟨.privateRow 10 6, 220007466605826900⟩, ⟨.privateRow 10 7, 805227327777326454⟩, ⟨.privateRow 10 8, 1647611472136970340⟩, ⟨.privateRow 10 9, 902030613083890290⟩, ⟨.privateRow 11 4, 89050641245215650⟩, ⟨.privateRow 11 5, 428585973907455000⟩, ⟨.privateRow 11 6, 540589775088603240⟩, ⟨.privateRow 12 2, 26594309150154900⟩, ⟨.privateRow 12 3, 240087513161120625⟩, ⟨.privateRow 13 1, 63826341960371760⟩, ⟨.hall 5 20, 23245958988583016400⟩, ⟨.hall 4 21, 113586712044779773800⟩, ⟨.hall 3 22, 286706078047092543840⟩, ⟨.hall 2 23, 566299219043398440600⟩, ⟨.assumptionRow 14, 162523339683200496⟩]
  caps := #[0, 0, 0, 0, 0, 2321528311813150440, 468812118944470158, 0, 0, 298351289134074176, 0, 162523339683200496, 801687050296022583, 98696997722828736, 1648853754135399504, 164670644892600000, 0, 0] }

theorem case_43_26_14_checked :
    (Witness.linear .conditional case_43_26_14).check 43 26 14 = true := by
  change case_43_26_14.check 43 26 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_26_15 : Certificate := {
  objectiveScale := 57382704775431189000000
  eta := 21169672250167962902552371200
  rows := #[⟨.count 2, 4410348385451658938031744000⟩, ⟨.count 3, 871043806126702640261269440⟩, ⟨.count 4, 185864681958319912388480640⟩, ⟨.count 5, 38772293498476122532147200⟩, ⟨.count 6, 8027076388356384742983600⟩, ⟨.count 7, 1734839836934656050799200⟩, ⟨.count 8, 385519963763256900177600⟩, ⟨.count 9, 154207985505302760071040⟩, ⟨.count 10, 96379990940814225044400⟩, ⟨.path 7, 38702833495430644940400⟩, ⟨.path 8, 99604522023378804432000⟩, ⟨.privateRow 2 24, 516837701420116281800595000⟩, ⟨.privateRow 3 21, 56048177398448165670820080⟩, ⟨.privateRow 3 22, 165847475744588424648902040⟩, ⟨.privateRow 4 19, 34308178846649623658572830⟩, ⟨.privateRow 4 20, 65498923938701720538030960⟩, ⟨.privateRow 4 21, 117543660094403588660935320⟩, ⟨.privateRow 5 16, 2029487237810859538792080⟩, ⟨.privateRow 5 17, 12916020271679858318521536⟩, ⟨.privateRow 5 18, 25656353588444746706819280⟩, ⟨.privateRow 5 19, 48647111998869259989553440⟩, ⟨.privateRow 5 20, 58309894519192606151862000⟩, ⟨.privateRow 6 14, 1355876335140162023073600⟩, ⟨.privateRow 6 15, 4808673119439909728108100⟩, ⟨.privateRow 6 16, 9935400208984506398862720⟩, ⟨.privateRow 6 17, 19493426858201943766569450⟩, ⟨.privateRow 6 18, 26428770372984700710389400⟩, ⟨.privateRow 6 19, 24295789382996919229942500⟩, ⟨.privateRow 7 12, 609259228447289922602100⟩, ⟨.privateRow 7 13, 1919732064453769053945600⟩, ⟨.privateRow 7 14, 3976822007153120285760600⟩, ⟨.privateRow 7 15, 8134471235404720593747360⟩, ⟨.privateRow 7 16, 8388501354384438086900100⟩, ⟨.privateRow 7 17, 19243871524515906933865200⟩, ⟨.privateRow 7 18, 1769261262270661131172200⟩, ⟨.privateRow 8 10, 221673979163872717602120⟩, ⟨.privateRow 8 11, 802363424582278423494630⟩, ⟨.privateRow 8 12, 1718317552773373612220160⟩, ⟨.privateRow 8 13, 3614249660280533439165000⟩, ⟨.privateRow 8 14, 5591967074386041337076088⟩, ⟨.privateRow 8 15, 5267166504915497398676460⟩, ⟨.privateRow 9 8, 65966749355046180697056⟩, ⟨.privateRow 9 9, 336021104218344903117760⟩, ⟨.privateRow 9 10, 803166591173451875370000⟩, ⟨.privateRow 9 11, 987665430974439106169280⟩, ⟨.privateRow 9 12, 4496305058853688809849120⟩, ⟨.privateRow 10 6, 12266544301558174096560⟩, ⟨.privateRow 10 7, 133968187407731772811716⟩, ⟨.privateRow 10 8, 394087074069107053514880⟩, ⟨.privateRow 10 9, 965004659294902428257055⟩, ⟨.privateRow 10 10, 980322193569424689023040⟩, ⟨.privateRow 11 5, 42557398597242644824800⟩, ⟨.privateRow 11 6, 194136838895068653303720⟩, ⟨.privateRow 11 7, 573690422266751339550000⟩, ⟨.privateRow 11 8, 46468924203606858503550⟩, ⟨.privateRow 12 3, 4207063096622843156700⟩, ⟨.privateRow 12 4, 82611420806412192895200⟩, ⟨.privateRow 12 5, 189317839348027942051500⟩, ⟨.privateRow 13 2, 15145427147842235364120⟩, ⟨.privateRow 13 3, 66089136645129754316160⟩, ⟨.privateRow 14 1, 16407546076829088311130⟩, ⟨.hall 5 20, 17395604895521653189646400⟩, ⟨.hall 4 21, 56704479241521329203265280⟩, ⟨.hall 3 22, 126557823234699778221780480⟩, ⟨.hall 2 23, 236022550315186435355605050⟩, ⟨.assumptionRow 15, 35571374739704721400560⟩]
  caps := #[0, 52492611090965151180412800, 0, 0, 1264885559244763334088210, 59873538612709699637760, 181066175315000274434850, 0, 109564995523239642952566, 0, 85993681879274775967179, 35571374739704721400560, 194259984001189896109320, 35571374739704721400560, 164211293828023582368690, 538255673014607168599440, 57382704775431189000000, 0] }

theorem case_43_26_15_checked :
    (Witness.linear .conditional case_43_26_15).check 43 26 15 = true := by
  change case_43_26_15.check 43 26 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_26_16 : Certificate := {
  objectiveScale := 78414592806000000
  eta := 33558472239608796480000
  rows := #[⟨.count 2, 7529682208762223710200⟩, ⟨.count 3, 1635975521680928828400⟩, ⟨.count 4, 358356542844393933840⟩, ⟨.count 5, 81591340472675233200⟩, ⟨.count 6, 17977752985504712400⟩, ⟨.count 7, 3666791110097115000⟩, ⟨.count 8, 704023893138646080⟩, ⟨.count 9, 117337315523107680⟩, ⟨.path 8, 35484338059410240⟩, ⟨.path 9, 89924086310778720⟩, ⟨.privateRow 2 24, 964806076888752898800⟩, ⟨.privateRow 3 21, 82497910922371624680⟩, ⟨.privateRow 3 22, 306221059186430267880⟩, ⟨.privateRow 4 19, 51611132529219778515⟩, ⟨.privateRow 4 20, 119651933759081363640⟩, ⟨.privateRow 4 21, 226519687617359376240⟩, ⟨.privateRow 5 16, 1244613668227249320⟩, ⟨.privateRow 5 17, 21720813350691847392⟩, ⟨.privateRow 5 18, 45520592495348470500⟩, ⟨.privateRow 5 19, 93545777927993751360⟩, ⟨.privateRow 5 20, 119529008952342869880⟩, ⟨.privateRow 6 14, 1371928646634975000⟩, ⟨.privateRow 6 15, 7836456429578977200⟩, ⟨.privateRow 6 16, 17685806569500789720⟩, ⟨.privateRow 6 17, 36656561509439897025⟩, ⟨.privateRow 6 18, 54086914964937254400⟩, ⟨.privateRow 6 19, 54605503993365274950⟩, ⟨.privateRow 7 12, 770026133120394150⟩, ⟨.privateRow 7 13, 2945406083539233600⟩, ⟨.privateRow 7 14, 6816739282771017600⟩, ⟨.privateRow 7 15, 15056891952661639080⟩, ⟨.privateRow 7 16, 23399365555434018150⟩, ⟨.privateRow 7 17, 28140002633488145400⟩, ⟨.privateRow 7 18, 19392086699399313900⟩, ⟨.privateRow 8 10, 334085412253292700⟩, ⟨.privateRow 8 11, 1180706737451271030⟩, ⟨.privateRow 8 12, 2757426914793030480⟩, ⟨.privateRow 8 13, 6409550860449757020⟩, ⟨.privateRow 8 14, 10883036014768237320⟩, ⟨.privateRow 8 15, 14219815924956611970⟩, ⟨.privateRow 8 16, 4312146345474207240⟩, ⟨.privateRow 9 8, 125159803224648192⟩, ⟨.privateRow 9 9, 491078394596709920⟩, ⟨.privateRow 9 10, 1205966853987495600⟩, ⟨.privateRow 9 11, 2929707893934101280⟩, ⟨.privateRow 9 12, 5423591473068088320⟩, ⟨.privateRow 9 13, 6164120308813923456⟩, ⟨.privateRow 10 6, 41334736150185660⟩, ⟨.privateRow 10 7, 203873585721399594⟩, ⟨.privateRow 10 8, 567130358361687120⟩, ⟨.privateRow 10 9, 946032106405055670⟩, ⟨.privateRow 10 10, 4041851457929905620⟩, ⟨.privateRow 10 11, 686912201291526210⟩, ⟨.privateRow 11 4, 12222637033657050⟩, ⟨.privateRow 11 5, 81907541680091400⟩, ⟨.privateRow 11 6, 278676124367380740⟩, ⟨.privateRow 11 7, 831139318288679400⟩, ⟨.privateRow 11 8, 1238851567911382425⟩, ⟨.privateRow 12 2, 2954923238906100⟩, ⟨.privateRow 12 3, 28810501579334475⟩, ⟨.privateRow 12 4, 87304550240407500⟩, ⟨.privateRow 12 5, 603099833060735010⟩, ⟨.privateRow 12 6, 140851341054524100⟩, ⟨.privateRow 13 1, 14183631546749280⟩, ⟨.privateRow 13 2, 61462403369246880⟩, ⟨.privateRow 13 3, 201149683753898880⟩, ⟨.privateRow 14 0, 46096802526935160⟩, ⟨.privateRow 14 1, 24969101368756545⟩, ⟨.hall 6 19, 2535324138981433800⟩, ⟨.hall 5 20, 44121225275780796000⟩, ⟨.hall 4 21, 123065890891682258520⟩, ⟨.hall 3 22, 256795265833528181760⟩, ⟨.hall 2 23, 456185482007182077150⟩]
  caps := #[0, 75958304647536352800, 0, 716824193717673360, 210974493654151920, 147760522240035276, 0, 28904819228029800, 40726302276351120, 0, 278653857863296266, 0, 32504155627967100, 0, 415276952914693485, 3450242083464000000, 705731335254000000, 78414592806000000] }

theorem case_43_26_16_checked :
    (Witness.linear .negative case_43_26_16).check 43 26 16 = true := by
  change case_43_26_16.check 43 26 16 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_27_1_checked :
    (Witness.rising).check 43 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_27_2_checked :
    (Witness.rising).check 43 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_27_3_checked :
    (Witness.rising).check 43 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_27_4_checked :
    (Witness.rising).check 43 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_27_5_checked :
    (Witness.rising).check 43 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_27_6_checked :
    (Witness.rising).check 43 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_27_7_checked :
    (Witness.rising).check 43 27 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_27_8_checked :
    (Witness.rising).check 43 27 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_27_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_27_9_checked :
    (Witness.linear .positive case_43_27_9).check 43 27 9 = true := by
  change case_43_27_9.check 43 27 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_27_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_27_10_checked :
    (Witness.linear .positive case_43_27_10).check 43 27 10 = true := by
  change case_43_27_10.check 43 27 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_27_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_43_27_11_checked :
    (Witness.linear .positive case_43_27_11).check 43 27 11 = true := by
  change case_43_27_11.check 43 27 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_27_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_43_27_12_checked :
    (Witness.linear .positive case_43_27_12).check 43 27 12 = true := by
  change case_43_27_12.check 43 27 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_27_13 : Certificate := {
  objectiveScale := 3563425000
  eta := 6140661175143495
  rows := #[⟨.count 2, 1000700339653014⟩, ⟨.count 3, 168811151522013⟩, ⟨.count 4, 28842426946872⟩, ⟨.count 5, 5370732156405⟩, ⟨.count 6, 986165040420⟩, ⟨.count 7, 182730581019⟩, ⟨.count 8, 54142394376⟩, ⟨.count 9, 20303397891⟩, ⟨.path 3, 4203997680960⟩, ⟨.path 7, 42467006400⟩]
  caps := #[0, 0, 634253815706, 0, 35137405128, 22474750995, 0, 9400275381, 0, 0, 7126850000, 3563425000, 3563425000, 0, 0, 0, 0] }

theorem case_43_27_13_checked :
    (Witness.linear .positive case_43_27_13).check 43 27 13 = true := by
  change case_43_27_13.check 43 27 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_27_14 : Certificate := {
  objectiveScale := 2515211770500000
  eta := 1969632924592105773000
  rows := #[⟨.count 2, 376469337417219446400⟩, ⟨.count 3, 74166194352931480800⟩, ⟨.count 4, 14512953011032476000⟩, ⟨.count 5, 3044383821279801000⟩, ⟨.count 6, 614184531814854000⟩, ⟨.count 7, 127386421413451200⟩, ⟨.count 8, 28308093647433600⟩, ⟨.count 9, 15923302676681400⟩, ⟨.path 8, 7984154716137600⟩, ⟨.privateRow 2 25, 37191527285168856600⟩, ⟨.privateRow 3 22, 6686523370025499000⟩, ⟨.privateRow 3 23, 12577892609561479200⟩, ⟨.privateRow 4 19, 870777180661948560⟩, ⟨.privateRow 4 20, 3346737009009644250⟩, ⟨.privateRow 4 21, 5129578219416651000⟩, ⟨.privateRow 4 22, 7756923161069082000⟩, ⟨.privateRow 5 16, 30980031058033200⟩, ⟨.privateRow 5 17, 681163503391371000⟩, ⟨.privateRow 5 18, 1334524414807584000⟩, ⟨.privateRow 5 19, 2074768426146165750⟩, ⟨.privateRow 5 20, 3216759891525780600⟩, ⟨.privateRow 5 21, 2944294490169232200⟩, ⟨.privateRow 6 14, 67768817939447625⟩, ⟨.privateRow 6 15, 317924444599047000⟩, ⟨.privateRow 6 16, 578799414755562000⟩, ⟨.privateRow 6 17, 853034071965075000⟩, ⟨.privateRow 6 18, 1335472230443100750⟩, ⟨.privateRow 6 19, 1333260660626895000⟩, ⟨.privateRow 6 20, 407560723272202500⟩, ⟨.privateRow 7 12, 50297416391422200⟩, ⟨.privateRow 7 13, 144447102852752700⟩, ⟨.privateRow 7 14, 266146630453103400⟩, ⟨.privateRow 7 15, 235816530116567400⟩, ⟨.privateRow 7 16, 902623786015311360⟩, ⟨.privateRow 7 17, 207002934796858200⟩, ⟨.privateRow 8 9, 160841441178600⟩, ⟨.privateRow 8 10, 28485019232730060⟩, ⟨.privateRow 8 11, 73129241922536800⟩, ⟨.privateRow 8 12, 132694188972345000⟩, ⟨.privateRow 8 13, 198662157204310800⟩, ⟨.privateRow 8 14, 205823430894881800⟩, ⟨.privateRow 9 8, 14958254029609800⟩, ⟨.privateRow 9 9, 41577512544668100⟩, ⟨.privateRow 9 10, 76078001677477800⟩, ⟨.privateRow 9 11, 79616513383407000⟩, ⟨.privateRow 10 6, 7772088211237350⟩, ⟨.privateRow 10 7, 26263109609591400⟩, ⟨.privateRow 10 8, 32074081105886820⟩, ⟨.privateRow 11 4, 4374533702385000⟩, ⟨.privateRow 11 5, 14217234532751250⟩, ⟨.privateRow 12 2, 2383079312156400⟩, ⟨.privateRow 12 3, 1924794829049400⟩, ⟨.privateRow 13 0, 1668155518509480⟩, ⟨.hall 4 22, 1544857067141388000⟩, ⟨.hall 3 23, 5638365652562042400⟩, ⟨.hall 2 24, 13480031113971405984⟩, ⟨.assumptionRow 14, 2652475260855420⟩]
  caps := #[0, 1142261366798838000, 18217998279424944, 0, 0, 0, 8871595036787340, 18409819826643960, 2997767197941360, 16892221193014440, 6132466802875050, 2652475260855420, 88451975087863200, 0, 27530065985144580, 2515211770500000, 0] }

theorem case_43_27_14_checked :
    (Witness.linear .conditional case_43_27_14).check 43 27 14 = true := by
  change case_43_27_14.check 43 27 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_27_15 : Certificate := {
  objectiveScale := 28625905261800000
  eta := 27243970935318658521000
  rows := #[⟨.count 2, 4824274138283556356400⟩, ⟨.count 3, 859431259789232130000⟩, ⟨.count 4, 147331073106725508000⟩, ⟨.count 5, 26129228777474823000⟩, ⟨.count 6, 4292863435510650000⟩, ⟨.count 7, 841401233360087400⟩, ⟨.count 8, 213689202123196800⟩, ⟨.count 9, 120200176194298200⟩, ⟨.path 7, 259598716401024000⟩, ⟨.privateRow 2 25, 498470130677754635400⟩, ⟨.privateRow 3 22, 83214772773243111000⟩, ⟨.privateRow 3 23, 164519698302510150600⟩, ⟨.privateRow 4 19, 9557631152820911160⟩, ⟨.privateRow 4 20, 39949387130862108900⟩, ⟨.privateRow 4 21, 66173058903918166200⟩, ⟨.privateRow 4 22, 107476128971444633400⟩, ⟨.privateRow 5 16, 206875133177941800⟩, ⟨.privateRow 5 17, 6978288006835645500⟩, ⟨.privateRow 5 18, 15362727281214112800⟩, ⟨.privateRow 5 19, 26207931273792518250⟩, ⟨.privateRow 5 20, 44912891231964756000⟩, ⟨.privateRow 5 21, 46906687805346369000⟩, ⟨.privateRow 6 14, 457905433121136000⟩, ⟨.privateRow 6 15, 3066331025364750000⟩, ⟨.privateRow 6 16, 6362977581079119000⟩, ⟨.privateRow 6 17, 10560444051356199000⟩, ⟨.privateRow 6 18, 18595253448153632250⟩, ⟨.privateRow 6 19, 21884063824580958000⟩, ⟨.privateRow 6 20, 15812046987464227500⟩, ⟨.privateRow 7 12, 288098835005381400⟩, ⟨.privateRow 7 13, 1283566167217684350⟩, ⟨.privateRow 7 14, 2784228571031193000⟩, ⟨.privateRow 7 15, 4656325873050551700⟩, ⟨.privateRow 7 16, 8221692051689996880⟩, ⟨.privateRow 7 17, 10401608104242304950⟩, ⟨.privateRow 7 18, 3325538208042250200⟩, ⟨.privateRow 8 10, 129549078787188060⟩, ⟨.privateRow 8 11, 571321825121047000⟩, ⟨.privateRow 8 12, 1300499128546643025⟩, ⟨.privateRow 8 13, 2268539833254294600⟩, ⟨.privateRow 8 14, 4084580061417355500⟩, ⟨.privateRow 8 15, 3667440931439365080⟩, ⟨.privateRow 9 8, 48565727755272000⟩, ⟨.privateRow 9 9, 271118175193805940⟩, ⟨.privateRow 9 10, 670746662220034400⟩, ⟨.privateRow 9 11, 1233721252883144025⟩, ⟨.privateRow 9 12, 2220841350637509600⟩, ⟨.privateRow 10 6, 14309544785035500⟩, ⟨.privateRow 10 7, 134249547437787600⟩, ⟨.privateRow 10 8, 386357709195958500⟩, ⟨.privateRow 10 9, 768899539782574200⟩, ⟨.privateRow 10 10, 281182555025947575⟩, ⟨.privateRow 11 4, 2201468428467000⟩, ⟨.privateRow 11 5, 66777875663499000⟩, ⟨.privateRow 11 6, 244563129053334000⟩, ⟨.privateRow 11 7, 208919353861518300⟩, ⟨.privateRow 12 3, 29059383255764400⟩, ⟨.privateRow 12 4, 125923994108312400⟩, ⟨.privateRow 13 1, 13491856511604900⟩, ⟨.privateRow 13 2, 29059383255764400⟩, ⟨.hall 5 21, 1803002642914473000⟩, ⟨.hall 4 22, 29630463309312465600⟩, ⟨.hall 3 23, 85840812733710209175⟩, ⟨.hall 2 24, 187470605468691168624⟩, ⟨.assumptionRow 15, 20564353768251150⟩]
  caps := #[0, 0, 0, 0, 369895890134087460, 0, 213257542756722750, 72593408267445780, 7247622734694520, 0, 31874821587346500, 16189231424706450, 157180074808333500, 0, 1613911596797986200, 294320604111548850, 28625905261800000] }

theorem case_43_27_15_checked :
    (Witness.linear .conditional case_43_27_15).check 43 27 15 = true := by
  change case_43_27_15.check 43 27 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_27_16 : Certificate := {
  objectiveScale := 36322133562000000
  eta := 70903078932611650725000
  rows := #[⟨.count 2, 9018298686055009150800⟩, ⟨.count 3, 1271958264488063552400⟩, ⟨.count 4, 195685886844317469600⟩, ⟨.count 5, 30851378556536538000⟩, ⟨.count 6, 4292863435510650000⟩, ⟨.count 7, 360600528582894600⟩, ⟨.path 3, 120709259293474051200⟩, ⟨.path 7, 397875960610128000⟩, ⟨.privateRow 2 25, 905267593644657843600⟩, ⟨.privateRow 3 22, 165883874905350201600⟩, ⟨.privateRow 3 23, 288523351500670786500⟩, ⟨.privateRow 4 19, 21041899415499002040⟩, ⟨.privateRow 4 20, 68423950298604250350⟩, ⟨.privateRow 4 21, 114779720629726752600⟩, ⟨.privateRow 4 22, 190019307109443411600⟩, ⟨.privateRow 5 16, 1502093358292012200⟩, ⟨.privateRow 5 17, 11889323777059829100⟩, ⟨.privateRow 5 18, 25323315215181623640⟩, ⟨.privateRow 5 19, 43947473943801027600⟩, ⟨.privateRow 5 20, 78891382308857718600⟩, ⟨.privateRow 5 21, 87170884921479258900⟩, ⟨.privateRow 6 14, 1337942437400819250⟩, ⟨.privateRow 6 15, 4897952757849294000⟩, ⟨.privateRow 6 16, 10083459225188349000⟩, ⟨.privateRow 6 17, 17245863374924784600⟩, ⟨.privateRow 6 18, 31996142139339378000⟩, ⟨.privateRow 6 19, 40791742333874532000⟩, ⟨.privateRow 6 20, 33441406162627963500⟩, ⟨.privateRow 7 11, 39494343606697980⟩, ⟨.privateRow 7 12, 679226392463018400⟩, ⟨.privateRow 7 13, 2028377973278782125⟩, ⟨.privateRow 7 14, 4238896009464230400⟩, ⟨.privateRow 7 15, 7352244110551239900⟩, ⟨.privateRow 7 16, 13816151680847475960⟩, ⟨.privateRow 7 17, 19047435063360754050⟩, ⟨.privateRow 7 18, 13874534623570420800⟩, ⟨.privateRow 8 9, 27925293459281400⟩, ⟨.privateRow 8 10, 304507113025555440⟩, ⟨.privateRow 8 11, 906695156231064200⟩, ⟨.privateRow 8 12, 1929880606675121100⟩, ⟨.privateRow 8 13, 3445738384236548400⟩, ⟨.privateRow 8 14, 6633268982574234000⟩, ⟨.privateRow 8 15, 9757583191950473880⟩, ⟨.privateRow 8 16, 1646074635105250350⟩, ⟨.privateRow 9 7, 13355575132699800⟩, ⟨.privateRow 9 8, 139626467296407000⟩, ⟨.privateRow 9 9, 443405094405633360⟩, ⟨.privateRow 9 10, 986828607027263000⟩, ⟨.privateRow 9 11, 1818027664938760275⟩, ⟨.privateRow 9 12, 3615544982352303000⟩, ⟨.privateRow 9 13, 2789089273545474900⟩, ⟨.privateRow 10 5, 6604405285401000⟩, ⟨.privateRow 10 6, 67254860489666850⟩, ⟨.privateRow 10 7, 241961393637873000⟩, ⟨.privateRow 10 8, 578677991106835620⟩, ⟨.privateRow 10 9, 1118052432537440400⟩, ⟨.privateRow 10 10, 1678509603284664150⟩, ⟨.privateRow 11 3, 4088441367153000⟩, ⟨.privateRow 11 4, 37424963283939000⟩, ⟨.privateRow 11 5, 150250220242872750⟩, ⟨.privateRow 11 6, 398065518565533000⟩, ⟨.privateRow 11 7, 724062966122796300⟩, ⟨.privateRow 12 1, 4197466470277080⟩, ⟨.privateRow 12 2, 26983713023209800⟩, ⟨.privateRow 12 3, 111394302480430200⟩, ⟨.privateRow 12 4, 293822652919395600⟩, ⟨.privateRow 13 0, 37777198232493720⟩, ⟨.privateRow 13 1, 94442995581234300⟩, ⟨.privateRow 14 0, 58464711550287900⟩, ⟨.hall 5 21, 8499869602311087000⟩, ⟨.hall 4 22, 59425175306592295200⟩, ⟨.hall 3 23, 158483216834942924925⟩, ⟨.hall 2 24, 337355417175933252096⟩, ⟨.assumptionRow 16, 7356857652282600⟩]
  caps := #[0, 22424157965136213000, 4445720040170257200, 0, 214183135407538440, 329793738488917560, 58755080987395650, 61216514505865080, 125121825273419390, 165394119290400, 43938288529576380, 52599884632913700, 179952481414819080, 615758299676760240, 0, 1880469778172891400, 355864477967717400] }

theorem case_43_27_16_checked :
    (Witness.linear .conditional case_43_27_16).check 43 27 16 = true := by
  change case_43_27_16.check 43 27 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_27_17 : Certificate := {
  objectiveScale := 2812825158000000
  eta := 6944204579096995610400
  rows := #[⟨.count 2, 832693398373567130400⟩, ⟨.count 3, 107387982175568814720⟩, ⟨.count 4, 15312357683570787840⟩, ⟨.count 5, 2476505217463477200⟩, ⟨.count 6, 320533803184795200⟩, ⟨.count 7, 32053380318479520⟩, ⟨.path 3, 14743477521952058880⟩, ⟨.path 7, 29526430581648000⟩, ⟨.privateRow 6 14, 32434968179413800⟩, ⟨.privateRow 8 10, 1780743351026640⟩, ⟨.privateRow 8 11, 7122973404106560⟩, ⟨.privateRow 8 12, 18697805185779720⟩, ⟨.privateRow 9 8, 971314555105440⟩, ⟨.privateRow 9 9, 4451858377566600⟩, ⟨.privateRow 10 6, 190793930467140⟩, ⟨.privateRow 10 7, 1040694166184400⟩, ⟨.privateRow 10 8, 4808007047771928⟩, ⟨.hall 10 5, 133198089789600⟩, ⟨.hall 11 5, 197957438845485⟩, ⟨.hall 12 5, 125798195912400⟩, ⟨.hall 13 5, 54512551562040⟩, ⟨.hall 10 6, 86023766322450⟩, ⟨.hall 9 7, 125685141978165⟩, ⟨.hall 8 9, 95226917167200⟩, ⟨.hall 7 10, 93569120633520⟩, ⟨.hall 6 13, 203493836055510⟩, ⟨.hall 5 16, 1350062315001400⟩, ⟨.hall 4 18, 5245180247324160⟩]
  caps := #[0, 3913374234280848480, 0, 0, 9265241173119360, 2459928293222400, 2842287056980800, 0, 8013345079619880, 0, 2052097616864412, 0, 8769629379851340, 0, 224494838737163280, 433175074332000000, 123764306952000000] }

theorem case_43_27_17_checked :
    (Witness.linear .negative case_43_27_17).check 43 27 17 = true := by
  change case_43_27_17.check 43 27 17 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_28_1_checked :
    (Witness.rising).check 43 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_28_2_checked :
    (Witness.rising).check 43 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_28_3_checked :
    (Witness.rising).check 43 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_28_4_checked :
    (Witness.rising).check 43 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_28_5_checked :
    (Witness.rising).check 43 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_28_6_checked :
    (Witness.rising).check 43 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_28_7_checked :
    (Witness.rising).check 43 28 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_28_8_checked :
    (Witness.rising).check 43 28 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_28_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_28_9_checked :
    (Witness.linear .positive case_43_28_9).check 43 28 9 = true := by
  change case_43_28_9.check 43 28 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_28_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_43_28_10_checked :
    (Witness.linear .positive case_43_28_10).check 43 28 10 = true := by
  change case_43_28_10.check 43 28 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_28_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_43_28_11_checked :
    (Witness.linear .positive case_43_28_11).check 43 28 11 = true := by
  change case_43_28_11.check 43 28 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_28_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_43_28_12_checked :
    (Witness.linear .positive case_43_28_12).check 43 28 12 = true := by
  change case_43_28_12.check 43 28 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_28_13 : Certificate := {
  objectiveScale := 133
  eta := 14366394
  rows := #[⟨.assumptionRow 13, 449⟩]
  caps := #[0, 0, 4190602, 1242462, 375804, 116545, 37323, 12474, 4424, 1713, 765, 18921, 7097, 1413, 133, 0] }

theorem case_43_28_13_checked :
    (Witness.linear .conditional case_43_28_13).check 43 28 13 = true := by
  change case_43_28_13.check 43 28 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_28_14 : Certificate := {
  objectiveScale := 141330735000000
  eta := 284861949428634177600
  rows := #[⟨.count 2, 46111697750739020400⟩, ⟨.count 3, 7622608180086900000⟩, ⟨.count 4, 1260271219107700800⟩, ⟨.count 5, 217128839069142000⟩, ⟨.count 6, 33262290240379200⟩, ⟨.count 7, 6467667546740400⟩, ⟨.count 8, 2155889182246800⟩, ⟨.path 7, 2200169770548750⟩, ⟨.privateRow 2 26, 3897693649417768200⟩, ⟨.privateRow 3 22, 111798253307941200⟩, ⟨.privateRow 3 23, 907937329894795200⟩, ⟨.privateRow 3 24, 1311088606974946800⟩, ⟨.privateRow 4 19, 20326955146898400⟩, ⟨.privateRow 4 20, 207843116377036140⟩, ⟨.privateRow 4 21, 393199538622815925⟩, ⟨.privateRow 4 22, 531041703212720700⟩, ⟨.privateRow 4 23, 719066038321530900⟩, ⟨.privateRow 5 17, 40785903509036400⟩, ⟨.privateRow 5 18, 103944657001185000⟩, ⟨.privateRow 5 19, 159289412151149280⟩, ⟨.privateRow 5 20, 212278088409086700⟩, ⟨.privateRow 5 21, 294432865461134400⟩, ⟨.privateRow 5 22, 210199195269063000⟩, ⟨.privateRow 6 14, 4311778364493600⟩, ⟨.privateRow 6 15, 24831223616949750⟩, ⟨.privateRow 6 16, 47121577840537200⟩, ⟨.privateRow 6 17, 70297386549690300⟩, ⟨.privateRow 6 18, 62828770454049600⟩, ⟨.privateRow 6 19, 179246786295376800⟩, ⟨.privateRow 7 11, 27998560808400⟩, ⟨.privateRow 7 12, 4003794195601200⟩, ⟨.privateRow 7 13, 13140657872742400⟩, ⟨.privateRow 7 14, 23483792878045500⟩, ⟨.privateRow 7 15, 34274238223882800⟩, ⟨.privateRow 7 16, 43785082677536200⟩, ⟨.privateRow 7 17, 19895777310449040⟩, ⟨.privateRow 8 9, 44914357963475⟩, ⟨.privateRow 8 10, 2743858959223200⟩, ⟨.privateRow 8 11, 7491714908307630⟩, ⟨.privateRow 8 12, 13384478673115550⟩, ⟨.privateRow 8 13, 19537745714111625⟩, ⟨.privateRow 8 14, 3349327836704850⟩, ⟨.privateRow 9 8, 1873570360762100⟩, ⟨.privateRow 9 9, 4983743823895200⟩, ⟨.privateRow 9 10, 8038386808091640⟩, ⟨.privateRow 10 6, 1314855490271400⟩, ⟨.privateRow 10 7, 3156837731147100⟩, ⟨.privateRow 11 4, 1055945721916800⟩, ⟨.privateRow 11 5, 142146539488800⟩, ⟨.privateRow 12 2, 338782585781640⟩, ⟨.hall 4 23, 19903476914671350⟩, ⟨.hall 3 24, 348810550320776544⟩, ⟨.hall 2 25, 1112900794292687400⟩, ⟨.assumptionRow 14, 157357640349000⟩]
  caps := #[0, 134447788370504700, 16591969200970800, 9011771786717700, 1426114322287200, 0, 1375832630376750, 792955148154390, 0, 1180890024124720, 330742186047000, 4024974589012800, 0, 10516759185114000, 1679941914651000, 141330735000000] }

theorem case_43_28_14_checked :
    (Witness.linear .conditional case_43_28_14).check 43 28 14 = true := by
  change case_43_28_14.check 43 28 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_28_15 : Certificate := {
  objectiveScale := 5500802183292000000
  eta := 12352642991968390057346400
  rows := #[⟨.count 2, 1897697767217190110172000⟩, ⟨.count 3, 290749570679112711566400⟩, ⟨.count 4, 45147448863216259560000⟩, ⟨.count 5, 6566901652831455936000⟩, ⟨.count 6, 985035247924718390400⟩, ⟨.count 7, 191534631540917464800⟩, ⟨.count 8, 63844877180305821600⟩, ⟨.path 6, 178196694185614104000⟩, ⟨.path 7, 34494464235839107500⟩, ⟨.privateRow 2 26, 176075050566543412284000⟩, ⟨.privateRow 3 22, 2483109687476894275800⟩, ⟨.privateRow 3 23, 37723201716820696876800⟩, ⟨.privateRow 3 24, 58842175018391858293200⟩, ⟨.privateRow 4 20, 7343985015083178221760⟩, ⟨.privateRow 4 21, 16234270153731513333450⟩, ⟨.privateRow 4 22, 24028475561645098143600⟩, ⟨.privateRow 4 23, 35515993105730124187200⟩, ⟨.privateRow 5 17, 867769146981299534400⟩, ⟨.privateRow 5 18, 3698442528087715808400⟩, ⟨.privateRow 5 19, 6468398128038984096960⟩, ⟨.privateRow 5 20, 9665658370261299205800⟩, ⟨.privateRow 5 21, 15049149621072086520000⟩, ⟨.privateRow 5 22, 13202208531213239538000⟩, ⟨.privateRow 6 14, 39523019206855984800⟩, ⟨.privateRow 6 15, 617357160591707185650⟩, ⟨.privateRow 6 16, 1610454452956285622400⟩, ⟨.privateRow 6 17, 2804614247563434306000⟩, ⟨.privateRow 6 18, 4098841114975633746720⟩, ⟨.privateRow 6 19, 6495076166003611886700⟩, ⟨.privateRow 6 20, 6060702983759031207600⟩, ⟨.privateRow 7 12, 34658647612166017440⟩, ⟨.privateRow 7 13, 326318261143785310400⟩, ⟨.privateRow 7 14, 757017829423626170400⟩, ⟨.privateRow 7 15, 1322501027306334876000⟩, ⟨.privateRow 7 16, 1953349218492690018000⟩, ⟨.privateRow 7 17, 3099212752266845454240⟩, ⟨.privateRow 7 18, 1016957686514871301200⟩, ⟨.privateRow 8 10, 18863259166908538200⟩, ⟨.privateRow 8 11, 169986985492564250010⟩, ⟨.privateRow 8 12, 402577419998039486200⟩, ⟨.privateRow 8 13, 708279106219017708375⟩, ⟨.privateRow 8 14, 1064841344400100667400⟩, ⟨.privateRow 8 15, 822002793696437453100⟩, ⟨.privateRow 9 8, 9120696740043688800⟩, ⟨.privateRow 9 9, 93694430147721530400⟩, ⟨.privateRow 9 10, 245346742307175228720⟩, ⟨.privateRow 9 11, 447927551011034494400⟩, ⟨.privateRow 9 12, 337465779381616485600⟩, ⟨.privateRow 10 6, 4209552341558625600⟩, ⟨.privateRow 10 7, 57004354625273055000⟩, ⟨.privateRow 10 8, 172878660936282646800⟩, ⟨.privateRow 10 9, 150491496210720865200⟩, ⟨.privateRow 11 4, 1954435015723647600⟩, ⟨.privateRow 11 5, 39990747244806943200⟩, ⟨.privateRow 11 6, 79806096475382277000⟩, ⟨.privateRow 12 3, 32248177759440185400⟩, ⟨.hall 4 23, 3799910279320701846300⟩, ⟨.hall 3 24, 19900995458905727214048⟩, ⟨.hall 2 25, 53875955643438069741600⟩, ⟨.assumptionRow 15, 4447398565191582000⟩]
  caps := #[0, 0, 638262364619333025000, 669677573803984619328, 125558074846628917038, 47729398384374762900, 0, 31951724538614806380, 0, 18033293902107146400, 22012031173592741400, 0, 0, 1525014893284957620000, 365745586765993434000, 61562227634312418000] }

theorem case_43_28_15_checked :
    (Witness.linear .conditional case_43_28_15).check 43 28 15 = true := by
  change case_43_28_15.check 43 28 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_28_16 : Certificate := {
  objectiveScale := 629360424000000
  eta := 1898286730401879417600
  rows := #[⟨.count 2, 277079119033814697600⟩, ⟨.count 3, 39296188794107044800⟩, ⟨.count 4, 5197631717995516800⟩, ⟨.count 5, 610460101106856000⟩, ⟨.count 6, 52325151523444800⟩, ⟨.count 7, 3699758188526400⟩, ⟨.path 6, 44760841293168000⟩, ⟨.privateRow 2 26, 26075367175849992000⟩, ⟨.privateRow 3 22, 488368080885484800⟩, ⟨.privateRow 3 23, 5319723738216888000⟩, ⟨.privateRow 3 24, 8572603991257706400⟩, ⟨.privateRow 4 19, 68313392266719600⟩, ⟨.privateRow 4 20, 988945363793106720⟩, ⟨.privateRow 4 21, 2228179369040024400⟩, ⟨.privateRow 4 22, 3447646094822529600⟩, ⟨.privateRow 4 23, 5358967601859471600⟩, ⟨.privateRow 5 17, 146102695812216000⟩, ⟨.privateRow 5 18, 472247705921191200⟩, ⟨.privateRow 5 19, 863206439071616640⟩, ⟨.privateRow 5 20, 1362039550261790400⟩, ⟨.privateRow 5 21, 2271122990871134400⟩, ⟨.privateRow 5 22, 2204791611919696800⟩, ⟨.privateRow 6 14, 11099274565579200⟩, ⟨.privateRow 6 15, 82352653249967100⟩, ⟨.privateRow 6 16, 200013457987886400⟩, ⟨.privateRow 6 17, 361783497149474400⟩, ⟨.privateRow 6 18, 564953075387981280⟩, ⟨.privateRow 6 19, 690929841707305200⟩, ⟨.privateRow 6 20, 1650092152082774400⟩, ⟨.privateRow 6 21, 38847460979527200⟩, ⟨.privateRow 7 10, 88089480679200⟩, ⟨.privateRow 7 12, 8139468014758080⟩, ⟨.privateRow 7 13, 39816445266998400⟩, ⟨.privateRow 7 14, 91106545392462600⟩, ⟨.privateRow 7 15, 165205528908076800⟩, ⟨.privateRow 7 16, 260744862810432000⟩, ⟨.privateRow 7 17, 452744694898816320⟩, ⟨.privateRow 7 18, 439346284887510000⟩, ⟨.privateRow 8 10, 4582655028970200⟩, ⟨.privateRow 8 11, 20117435150112300⟩, ⟨.privateRow 8 12, 46658061599749600⟩, ⟨.privateRow 8 13, 85499099387977275⟩, ⟨.privateRow 8 14, 137023187196495600⟩, ⟨.privateRow 8 15, 242488317939667800⟩, ⟨.privateRow 8 16, 40512352164364080⟩, ⟨.privateRow 9 8, 2554594939696800⟩, ⟨.privateRow 9 9, 11387567411438400⟩, ⟨.privateRow 9 10, 27695332725540480⟩, ⟨.privateRow 9 11, 52148972562086400⟩, ⟨.privateRow 9 12, 85160505446616600⟩, ⟨.privateRow 9 13, 42509466533476800⟩, ⟨.privateRow 10 6, 1585610652225600⟩, ⟨.privateRow 10 7, 7597717708581000⟩, ⟨.privateRow 10 8, 19603913518425600⟩, ⟨.privateRow 10 9, 38768180446915920⟩, ⟨.privateRow 10 10, 13125332621200800⟩, ⟨.privateRow 11 4, 1245836941034400⟩, ⟨.privateRow 11 5, 6098502508560000⟩, ⟨.privateRow 11 6, 17177448732444000⟩, ⟨.privateRow 11 7, 3459514150310400⟩, ⟨.privateRow 12 2, 1162781144965440⟩, ⟨.privateRow 12 3, 6540643940430600⟩, ⟨.privateRow 12 4, 1341670551883200⟩, ⟨.privateRow 13 0, 2180214646810200⟩, ⟨.privateRow 13 1, 1162781144965440⟩, ⟨.hall 4 23, 807406157535377400⟩, ⟨.hall 3 24, 3231601358087950848⟩, ⟨.hall 2 25, 8145281920482907200⟩, ⟨.assumptionRow 16, 244749278030400⟩]
  caps := #[0, 0, 0, 15023473637990400, 22583096141881968, 281571350860800, 0, 0, 1124891576817600, 5734281986447040, 139176314620200, 0, 34268382434202840, 0, 152969701343659200, 37971436223635200] }

theorem case_43_28_16_checked :
    (Witness.linear .conditional case_43_28_16).check 43 28 16 = true := by
  change case_43_28_16.check 43 28 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_28_17 : Certificate := {
  objectiveScale := 397493554458000000
  eta := 1768400111425535437449600
  rows := #[⟨.count 2, 250970193994121003001600⟩, ⟨.count 3, 34060848083580298780800⟩, ⟨.count 4, 4294813553610000220800⟩, ⟨.count 5, 454221955489806504000⟩, ⟨.count 6, 34791468931134115200⟩, ⟨.path 5, 35071064942809896000⟩, ⟨.path 6, 32151296849968296000⟩, ⟨.privateRow 5 17, 84493567404182851200⟩, ⟨.privateRow 6 15, 65596415380575779700⟩, ⟨.privateRow 6 17, 257553513059645602800⟩, ⟨.privateRow 7 10, 53690538473972400⟩, ⟨.privateRow 7 11, 351428979102364800⟩, ⟨.privateRow 7 12, 386571877012601280⟩, ⟨.privateRow 7 15, 98207664945820372800⟩, ⟨.privateRow 7 17, 549189779942568885120⟩, ⟨.privateRow 7 20, 282841756680886603200⟩, ⟨.privateRow 8 8, 43365434921285400⟩, ⟨.privateRow 8 9, 187916884658903400⟩, ⟨.privateRow 8 10, 563750653976710200⟩, ⟨.privateRow 8 11, 1296626504146433460⟩, ⟨.privateRow 8 12, 4196810424048842600⟩, ⟨.privateRow 8 13, 23325183308286384525⟩, ⟨.privateRow 8 18, 904068132093984257400⟩, ⟨.privateRow 9 10, 708715107856435680⟩, ⟨.privateRow 9 11, 5082704308869387200⟩, ⟨.hall 9 5, 83112288659400⟩, ⟨.hall 12 5, 9735097635390600⟩, ⟨.hall 9 6, 6482758515433200⟩, ⟨.hall 10 6, 27174978426063600⟩, ⟨.hall 11 6, 18038563265576700⟩, ⟨.hall 8 7, 18683642490633120⟩, ⟨.hall 9 7, 19007141091107400⟩, ⟨.hall 12 7, 5575555918450980⟩, ⟨.hall 8 8, 6735931333195680⟩, ⟨.hall 7 9, 4465047876901920⟩, ⟨.hall 6 11, 4740140419146000⟩, ⟨.hall 5 15, 31263196565191500⟩, ⟨.hall 4 18, 346733111328318000⟩, ⟨.hall 3 22, 71854467826540102704⟩, ⟨.hall 2 24, 983129597618447575296⟩]
  caps := #[0, 1432676353166288630400, 192325993945025740800, 11022562042190899200, 0, 12674481469487494800, 0, 157797835259208480, 0, 228638070150225120, 6656643877619736000, 4562590015490707200, 32364561193657492800, 0, 253203394189746000000, 82678659327264000000] }

theorem case_43_28_17_checked :
    (Witness.linear .negative case_43_28_17).check 43 28 17 = true := by
  change case_43_28_17.check 43 28 17 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_28_18 : Certificate := {
  objectiveScale := 10752036394554000000
  eta := 51223495685613007663146240
  rows := #[⟨.count 2, 6423040373451081612392160⟩, ⟨.count 3, 730681732624445903901600⟩, ⟨.count 4, 69588736440423419419200⟩, ⟨.count 5, 4568957443058103295200⟩, ⟨.path 4, 2678943107697326870400⟩, ⟨.path 5, 3837305331953975481600⟩, ⟨.path 6, 55783291338858283200⟩, ⟨.hall 12 7, 270352511423556408⟩, ⟨.hall 11 8, 326013322598994492⟩, ⟨.hall 13 8, 781018366334718512⟩, ⟨.hall 10 9, 219751773991339968⟩, ⟨.hall 8 10, 223328066712113160⟩, ⟨.hall 9 10, 335182328404381080⟩, ⟨.hall 12 10, 193108936731111720⟩, ⟨.hall 7 11, 80619825710455955⟩, ⟨.hall 10 14, 3359527531660370070⟩]
  caps := #[0, 0, 0, 972138797503331858400, 62875154166893140800, 0, 55783291338858283200, 0, 0, 105437479455186999120, 149590931950150891200, 84848620003983435600, 469238652005302539360, 1422164112441453501120, 0, 4612623613263666000000] }

theorem case_43_28_18_checked :
    (Witness.linear .negative case_43_28_18).check 43 28 18 = true := by
  change case_43_28_18.check 43 28 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_29_1_checked :
    (Witness.rising).check 43 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_29_2_checked :
    (Witness.rising).check 43 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_29_3_checked :
    (Witness.rising).check 43 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_29_4_checked :
    (Witness.rising).check 43 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_29_5_checked :
    (Witness.rising).check 43 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_29_6_checked :
    (Witness.rising).check 43 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_29_7_checked :
    (Witness.rising).check 43 29 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_29_8_checked :
    (Witness.rising).check 43 29 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_29_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_43_29_9_checked :
    (Witness.linear .positive case_43_29_9).check 43 29 9 = true := by
  change case_43_29_9.check 43 29 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_29_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_43_29_10_checked :
    (Witness.linear .positive case_43_29_10).check 43 29 10 = true := by
  change case_43_29_10.check 43 29 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_29_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_43_29_11_checked :
    (Witness.linear .positive case_43_29_11).check 43 29 11 = true := by
  change case_43_29_11.check 43 29 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_29_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_43_29_12_checked :
    (Witness.linear .positive case_43_29_12).check 43 29 12 = true := by
  change case_43_29_12.check 43 29 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_29_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_43_29_13_checked :
    (Witness.linear .positive case_43_29_13).check 43 29 13 = true := by
  change case_43_29_13.check 43 29 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_29_14 : Certificate := {
  objectiveScale := 294
  eta := 43424766
  rows := #[⟨.assumptionRow 14, 641⟩]
  caps := #[0, 0, 12671290, 3751254, 1129752, 347347, 109527, 36102, 12810, 4858, 415701, 234753, 83657, 20961, 3475] }

theorem case_43_29_14_checked :
    (Witness.linear .conditional case_43_29_14).check 43 29 14 = true := by
  change case_43_29_14.check 43 29 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_29_15 : Certificate := {
  objectiveScale := 196109713800000
  eta := 1311020343319508902080
  rows := #[⟨.count 2, 157617830397328741440⟩, ⟨.count 3, 17769506501602215360⟩, ⟨.count 4, 1825203147153946560⟩, ⟨.count 5, 178324445411592480⟩, ⟨.count 7, 6118976068044840⟩, ⟨.path 5, 101600694282927840⟩, ⟨.path 6, 652337829823680⟩, ⟨.privateRow 2 27, 11769413397165103680⟩, ⟨.privateRow 3 23, 1163479592366811720⟩, ⟨.privateRow 3 24, 2782094452271053920⟩, ⟨.privateRow 3 25, 3846213528485328000⟩, ⟨.privateRow 4 20, 289340154074691720⟩, ⟨.privateRow 4 21, 763648213291996032⟩, ⟨.privateRow 4 22, 1164353731805103840⟩, ⟨.privateRow 4 23, 1536737132517546960⟩, ⟨.privateRow 4 24, 2048108703918437160⟩, ⟨.privateRow 5 16, 932415400844928⟩, ⟨.privateRow 5 17, 42483176700997032⟩, ⟨.privateRow 5 18, 181920904814851488⟩, ⟨.privateRow 5 19, 331823330775688752⟩, ⟨.privateRow 5 20, 482524969937250240⟩, ⟨.privateRow 5 21, 497210512500557856⟩, ⟨.privateRow 5 22, 1131486088925320128⟩, ⟨.privateRow 5 23, 269584602769289808⟩, ⟨.privateRow 6 12, 1262645855310840⟩, ⟨.privateRow 6 14, 1631726951478624⟩, ⟨.privateRow 6 15, 32505036890566240⟩, ⟨.privateRow 6 16, 91784641020672600⟩, ⟨.privateRow 6 17, 152516519138206080⟩, ⟨.privateRow 6 18, 220671644866632960⟩, ⟨.privateRow 6 19, 283920489557280576⟩, ⟨.privateRow 6 20, 338000582806286400⟩, ⟨.privateRow 7 12, 2225082206561760⟩, ⟨.privateRow 7 13, 20717104687523244⟩, ⟨.privateRow 7 14, 49048935148613400⟩, ⟨.privateRow 7 15, 80857898042021100⟩, ⟨.privateRow 7 16, 115636159979786160⟩, ⟨.privateRow 7 17, 146126976101166060⟩, ⟨.privateRow 8 10, 1456899063820200⟩, ⟨.privateRow 8 11, 13588894904359320⟩, ⟨.privateRow 8 12, 30594880340224200⟩, ⟨.privateRow 8 13, 51088593837961680⟩, ⟨.privateRow 8 14, 52557633727313715⟩, ⟨.privateRow 9 8, 1075863924051840⟩, ⟨.privateRow 9 9, 10101166842486720⟩, ⟨.privateRow 9 10, 23522297612224320⟩, ⟨.privateRow 9 11, 17133132990525552⟩, ⟨.privateRow 10 6, 899114850814752⟩, ⟨.privateRow 10 7, 8875877373427680⟩, ⟨.privateRow 10 8, 7167943393995384⟩, ⟨.privateRow 11 4, 1048967325950544⟩, ⟨.privateRow 11 5, 4120943066234280⟩, ⟨.privateRow 12 2, 1201941727651665⟩, ⟨.hall 3 25, 667909772350432920⟩, ⟨.hall 2 26, 2743632316986200640⟩, ⟨.assumptionRow 15, 172599724746540⟩]
  caps := #[0, 276737375247802560, 25326002979426240, 27275209177834800, 7263948266746080, 5300352997244448, 17043608566899200, 0, 10110140496140685, 666888909932700, 8795863411204824, 0, 21940810492930875, 68337902698359840, 15233478095548440] }

theorem case_43_29_15_checked :
    (Witness.linear .conditional case_43_29_15).check 43 29 15 = true := by
  change case_43_29_15.check 43 29 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_29_16 : Certificate := {
  objectiveScale := 478764000000
  eta := 3118817976530256000
  rows := #[⟨.count 2, 374323885697361600⟩, ⟨.count 3, 41737606219108800⟩, ⟨.count 4, 4093093809604800⟩, ⟨.count 5, 283827672928800⟩, ⟨.count 6, 9958865716800⟩, ⟨.count 7, 8714007502200⟩, ⟨.path 5, 253451347749600⟩, ⟨.privateRow 2 26, 6079887520106400⟩, ⟨.privateRow 2 27, 35329076130348000⟩, ⟨.privateRow 3 23, 3348046168166700⟩, ⟨.privateRow 3 24, 8325611739244800⟩, ⟨.privateRow 3 25, 11420329260740400⟩, ⟨.privateRow 4 20, 690896309103000⟩, ⟨.privateRow 4 21, 2030114776369680⟩, ⟨.privateRow 4 22, 3292027548509700⟩, ⟨.privateRow 4 23, 4633362274741200⟩, ⟨.privateRow 4 24, 6569116798444200⟩, ⟨.privateRow 5 16, 5311395048960⟩, ⟨.privateRow 5 17, 88135961593680⟩, ⟨.privateRow 5 18, 423820871004960⟩, ⟨.privateRow 5 19, 855466565073120⟩, ⟨.privateRow 5 20, 1336678956508896⟩, ⟨.privateRow 5 21, 1883719450332720⟩, ⟨.privateRow 5 22, 2864169780151680⟩, ⟨.privateRow 5 23, 2189954571124320⟩, ⟨.privateRow 6 14, 8299054764000⟩, ⟨.privateRow 6 15, 64548203720000⟩, ⟨.privateRow 6 16, 207891321838200⟩, ⟨.privateRow 6 17, 379859592340800⟩, ⟨.privateRow 6 18, 597255307849200⟩, ⟨.privateRow 6 19, 839532379926240⟩, ⟨.privateRow 6 20, 1305441314377200⟩, ⟨.privateRow 6 21, 529479693943200⟩, ⟨.privateRow 7 12, 5884784287200⟩, ⟨.privateRow 7 13, 39462005402820⟩, ⟨.privateRow 7 14, 106781171296800⟩, ⟨.privateRow 7 15, 193419845093475⟩, ⟨.privateRow 7 16, 302678383035600⟩, ⟨.privateRow 7 17, 429061131298800⟩, ⟨.privateRow 7 18, 473046121548000⟩, ⟨.privateRow 8 10, 3838312828350⟩, ⟨.privateRow 8 11, 25236671077800⟩, ⟨.privateRow 8 12, 63612254766060⟩, ⟨.privateRow 8 13, 116601719434200⟩, ⟨.privateRow 8 14, 183149764823025⟩, ⟨.privateRow 8 15, 197221108570200⟩, ⟨.privateRow 9 8, 2936588608800⟩, ⟨.privateRow 9 9, 18534555639600⟩, ⟨.privateRow 9 10, 46474706678400⟩, ⟨.privateRow 9 11, 86642131736160⟩, ⟨.privateRow 9 12, 63994933402400⟩, ⟨.privateRow 10 6, 2774255449680⟩, ⟨.privateRow 10 7, 16547038421760⟩, ⟨.privateRow 10 8, 43321065868080⟩, ⟨.privateRow 10 9, 15209904003840⟩, ⟨.privateRow 11 4, 3485603000880⟩, ⟨.privateRow 11 5, 19206383882400⟩, ⟨.privateRow 11 6, 3447299671200⟩, ⟨.privateRow 12 2, 5135040135225⟩, ⟨.privateRow 12 3, 1825792048080⟩, ⟨.hall 3 25, 2505899585989800⟩, ⟨.hall 2 26, 8617738466937600⟩, ⟨.assumptionRow 16, 250792542000⟩]
  caps := #[0, 0, 222055169450400, 32346617666220, 0, 0, 9172421614200, 0, 1492659541800, 1933952474080, 457828264080, 0, 158784869998755, 492893921520000, 144996071220000] }

theorem case_43_29_16_checked :
    (Witness.linear .conditional case_43_29_16).check 43 29 16 = true := by
  change case_43_29_16.check 43 29 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_29_17 : Certificate := {
  objectiveScale := 1411989939360000
  eta := 7980123828901358534400
  rows := #[⟨.count 2, 1060401069803404929600⟩, ⟨.count 3, 135002094849835012800⟩, ⟨.count 4, 15629613156663105600⟩, ⟨.count 5, 1468554256330761600⟩, ⟨.count 6, 104896732595054400⟩, ⟨.path 5, 346251122307490400⟩, ⟨.path 6, 89581603391280000⟩, ⟨.privateRow 2 26, 83078212215283084800⟩, ⟨.privateRow 3 24, 77116581246130826400⟩, ⟨.privateRow 4 22, 38588885503405637400⟩, ⟨.privateRow 4 23, 12762435799064952000⟩, ⟨.privateRow 4 24, 18540497486175865200⟩, ⟨.privateRow 5 17, 351404054193432240⟩, ⟨.privateRow 5 18, 864648781533519840⟩, ⟨.privateRow 5 19, 1863665282438799840⟩, ⟨.privateRow 5 21, 25796728963438753320⟩, ⟨.privateRow 5 23, 31316919516253491120⟩, ⟨.privateRow 6 14, 33217298655100560⟩, ⟨.privateRow 6 15, 255766724537324000⟩, ⟨.privateRow 6 16, 544880249868754800⟩, ⟨.privateRow 6 17, 1081435362229965600⟩, ⟨.privateRow 6 19, 4919656758708051360⟩, ⟨.privateRow 6 20, 12575952718895966400⟩, ⟨.privateRow 6 21, 2636016039472015200⟩, ⟨.privateRow 6 22, 5827596255280800000⟩, ⟨.privateRow 7 10, 336207476266200⟩, ⟨.privateRow 7 11, 1456899063820200⟩, ⟨.privateRow 7 12, 6357377733033600⟩, ⟨.privateRow 7 13, 25787113429617540⟩, ⟨.privateRow 7 14, 636664890889427400⟩, ⟨.privateRow 7 15, 410299198848363825⟩, ⟨.privateRow 7 16, 758628155374947000⟩, ⟨.privateRow 7 17, 606070010549203200⟩, ⟨.privateRow 7 20, 15346974738281986800⟩, ⟨.privateRow 8 9, 1008622428798600⟩, ⟨.privateRow 8 10, 3642247659550500⟩, ⟨.privateRow 8 11, 13906763791011000⟩, ⟨.privateRow 8 13, 12626458553108400⟩, ⟨.privateRow 9 8, 448276635021600⟩, ⟨.privateRow 9 9, 5341963234007400⟩, ⟨.hall 9 6, 179157990139128⟩, ⟨.hall 11 6, 72515338018200⟩, ⟨.hall 8 7, 133361142374460⟩, ⟨.hall 10 7, 64535181202800⟩, ⟨.hall 12 7, 29665365552900⟩, ⟨.hall 8 8, 315020683120⟩, ⟨.hall 7 9, 74221541506710⟩, ⟨.hall 3 21, 2377717743020004⟩, ⟨.hall 2 24, 258518146906056576⟩, ⟨.hall 1 27, 91608564362388044400⟩]
  caps := #[0, 4635319714679253600, 323644243016952000, 249033183831832400, 85532855219445216, 26180125965833840, 0, 11240255026466190, 800166854246760, 26667355184421600, 0, 170067128246215200, 0, 145883270559826800, 1284910844817600000] }

theorem case_43_29_17_checked :
    (Witness.linear .negative case_43_29_17).check 43 29 17 = true := by
  change case_43_29_17.check 43 29 17 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_29_18 : Certificate := {
  objectiveScale := 9972178946730000
  eta := 55512111390614102624400
  rows := #[⟨.count 2, 6401983956028543602720⟩, ⟨.count 3, 681270186766784935320⟩, ⟨.count 4, 62822653151178080160⟩, ⟨.count 5, 4148665774134401520⟩, ⟨.path 3, 41323221864429785280⟩, ⟨.path 5, 3658199398834220240⟩, ⟨.path 6, 45682023801173760⟩, ⟨.hall 11 6, 175590711344070⟩, ⟨.hall 12 9, 536349809196432⟩, ⟨.hall 9 10, 332331580339416⟩, ⟨.hall 10 10, 375316553086020⟩, ⟨.hall 11 11, 546282213070440⟩, ⟨.hall 7 12, 313680318177510⟩, ⟨.hall 8 12, 418281158633976⟩, ⟨.hall 6 13, 239461803539010⟩, ⟨.hall 5 15, 39838351246785⟩]
  caps := #[0, 33694389535769362400, 0, 894972616289711960, 154626518942175280, 93427755168347600, 193848658591688100, 0, 71838368383279680, 276086897125182000, 0, 287517863392119360, 988708301971790400, 0, 16334429114743740000] }

theorem case_43_29_18_checked :
    (Witness.linear .negative case_43_29_18).check 43 29 18 = true := by
  change case_43_29_18.check 43 29 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_30_1_checked :
    (Witness.rising).check 43 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_30_2_checked :
    (Witness.rising).check 43 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_30_3_checked :
    (Witness.rising).check 43 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_30_4_checked :
    (Witness.rising).check 43 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_30_5_checked :
    (Witness.rising).check 43 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_30_6_checked :
    (Witness.rising).check 43 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_30_7_checked :
    (Witness.rising).check 43 30 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_30_8_checked :
    (Witness.rising).check 43 30 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_30_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_43_30_9_checked :
    (Witness.linear .positive case_43_30_9).check 43 30 9 = true := by
  change case_43_30_9.check 43 30 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_30_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_43_30_10_checked :
    (Witness.linear .positive case_43_30_10).check 43 30 10 = true := by
  change case_43_30_10.check 43 30 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_43_30_11_checked :
    (Witness.linear .positive case_43_30_11).check 43 30 11 = true := by
  change case_43_30_11.check 43 30 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_30_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_43_30_12_checked :
    (Witness.linear .positive case_43_30_12).check 43 30 12 = true := by
  change case_43_30_12.check 43 30 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_30_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_43_30_13_checked :
    (Witness.linear .positive case_43_30_13).check 43 30 13 = true := by
  change case_43_30_13.check 43 30 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_30_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_43_30_14_checked :
    (Witness.linear .positive case_43_30_14).check 43 30 14 = true := by
  change case_43_30_14.check 43 30 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_30_15 : Certificate := {
  objectiveScale := 72522450000
  eta := 514606556333469600
  rows := #[⟨.count 2, 62156734416176400⟩, ⟨.count 3, 7060032658879200⟩, ⟨.count 4, 729278098829280⟩, ⟨.count 5, 60342159477600⟩, ⟨.count 6, 6465231372600⟩, ⟨.path 5, 40408132564800⟩, ⟨.privateRow 2 27, 5511609745141500⟩, ⟨.privateRow 2 28, 7609577325550200⟩, ⟨.privateRow 3 23, 442221825885840⟩, ⟨.privateRow 3 24, 1218696113735100⟩, ⟨.privateRow 3 25, 2387825453613600⟩, ⟨.privateRow 3 26, 2450322690215400⟩, ⟨.privateRow 3 27, 2974006431396000⟩, ⟨.privateRow 4 20, 152394739497000⟩, ⟨.privateRow 4 21, 277358425884540⟩, ⟨.privateRow 4 22, 643937044710960⟩, ⟨.privateRow 4 23, 835954416477180⟩, ⟨.privateRow 4 24, 977542983537120⟩, ⟨.privateRow 4 25, 1103614995302820⟩, ⟨.privateRow 5 17, 32182485054720⟩, ⟨.privateRow 5 18, 73057114510380⟩, ⟨.privateRow 5 19, 168958046537280⟩, ⟨.privateRow 5 20, 271827061265760⟩, ⟨.privateRow 5 21, 350329337309952⟩, ⟨.privateRow 5 22, 403861453075080⟩, ⟨.privateRow 5 23, 308032356952320⟩, ⟨.privateRow 6 13, 89794880175⟩, ⟨.privateRow 6 14, 4408112299500⟩, ⟨.privateRow 6 15, 17456124706020⟩, ⟨.privateRow 6 16, 49447047349700⟩, ⟨.privateRow 6 17, 88627546732725⟩, ⟨.privateRow 6 18, 130843968255000⟩, ⟨.privateRow 6 19, 170430682572150⟩, ⟨.privateRow 6 20, 128873612027160⟩, ⟨.privateRow 7 11, 213139495800⟩, ⟨.privateRow 7 12, 2924747525700⟩, ⟨.privateRow 7 13, 14273887446000⟩, ⟨.privateRow 7 14, 32695598655720⟩, ⟨.privateRow 7 15, 34583856707400⟩, ⟨.privateRow 7 16, 114988757984100⟩, ⟨.privateRow 7 17, 10687423289400⟩, ⟨.privateRow 8 10, 2983952941200⟩, ⟨.privateRow 8 11, 12481488344325⟩, ⟨.privateRow 8 12, 25762967439300⟩, ⟨.privateRow 8 13, 31356372157110⟩, ⟨.privateRow 9 8, 3571270662960⟩, ⟨.privateRow 9 9, 13262013072000⟩, ⟨.privateRow 9 10, 7470934030560⟩, ⟨.privateRow 10 6, 5172185098080⟩, ⟨.privateRow 10 7, 2493732100860⟩, ⟨.privateRow 11 4, 2424461764725⟩, ⟨.hall 3 26, 45974978649600⟩, ⟨.assumptionRow 15, 68861070432⟩]
  caps := #[0, 1123157630770560, 39579798438180, 0, 3479996580060, 3836895100584, 0, 4740173176896, 1582254621255, 271782902160, 13009108130172, 0, 117085488103584, 31257745418592] }

theorem case_43_30_15_checked :
    (Witness.linear .conditional case_43_30_15).check 43 30 15 = true := by
  change case_43_30_15.check 43 30 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_30_16 : Certificate := {
  objectiveScale := 2969823336480000
  eta := 26734839814636412659200
  rows := #[⟨.count 2, 2828563526140045293600⟩, ⟨.count 3, 266077579854521635200⟩, ⟨.count 4, 20650797242440485120⟩, ⟨.count 5, 1103140878335496000⟩, ⟨.path 4, 7282322830024482240⟩, ⟨.path 5, 758941858397923200⟩, ⟨.privateRow 2 27, 263926455141767418000⟩, ⟨.privateRow 2 28, 380418131893995795600⟩, ⟨.privateRow 3 23, 19988912715439187520⟩, ⟨.privateRow 3 24, 53943588950605754400⟩, ⟨.privateRow 3 25, 113402882292888988800⟩, ⟨.privateRow 3 26, 124599762207994273200⟩, ⟨.privateRow 3 27, 161830766851817263200⟩, ⟨.privateRow 4 20, 6254808780162262320⟩, ⟨.privateRow 4 21, 11235489845847026760⟩, ⟨.privateRow 4 22, 28156567778635199904⟩, ⟨.privateRow 4 23, 39762712959602953320⟩, ⟨.privateRow 4 24, 50369412504798747360⟩, ⟨.privateRow 4 25, 62895577178298304440⟩, ⟨.privateRow 5 17, 1176683603557862400⟩, ⟨.privateRow 5 18, 2708210856313642680⟩, ⟨.privateRow 5 19, 6669274567308312960⟩, ⟨.privateRow 5 20, 11803607398189807200⟩, ⟨.privateRow 5 21, 16600063937192543808⟩, ⟨.privateRow 5 22, 21114116411341393440⟩, ⟨.privateRow 5 23, 27784441589010025920⟩, ⟨.privateRow 6 14, 147921163231350600⟩, ⟨.privateRow 6 15, 576391108930296660⟩, ⟨.privateRow 6 16, 1761961125119195000⟩, ⟨.privateRow 6 17, 3436973299064029725⟩, ⟨.privateRow 6 18, 5590560379850245800⟩, ⟨.privateRow 6 19, 7974789266300356500⟩, ⟨.privateRow 6 20, 10170958898253273120⟩, ⟨.privateRow 6 21, 5364022520906349300⟩, ⟨.privateRow 7 11, 10910184511010400⟩, ⟨.privateRow 7 12, 86675354726360400⟩, ⟨.privateRow 7 13, 449135929036594800⟩, ⟨.privateRow 7 14, 1134659189145081600⟩, ⟨.privateRow 7 15, 2035557573119070000⟩, ⟨.privateRow 7 16, 3185319286193744700⟩, ⟨.privateRow 7 17, 4525128909090504000⟩, ⟨.privateRow 7 18, 1792603927295181000⟩, ⟨.privateRow 8 9, 5909683276797300⟩, ⟨.privateRow 8 10, 84856990641192000⟩, ⟨.privateRow 8 11, 383801097254224650⟩, ⟨.privateRow 8 12, 869977010869129800⟩, ⟨.privateRow 8 13, 1500271594536274560⟩, ⟨.privateRow 8 14, 2000974982091885800⟩, ⟨.privateRow 9 7, 5883418017789312⟩, ⟨.privateRow 9 8, 100858594590673920⟩, ⟨.privateRow 9 9, 400524995826426240⟩, ⟨.privateRow 9 10, 864127021362805200⟩, ⟨.privateRow 9 11, 377073609321951360⟩, ⟨.privateRow 10 5, 12410334881274330⟩, ⟨.privateRow 10 6, 152233441210298448⟩, ⟨.privateRow 10 7, 446772055725875880⟩, ⟨.privateRow 11 3, 19467191970626400⟩, ⟨.privateRow 11 4, 186155023219114950⟩, ⟨.privateRow 12 1, 101121247180753800⟩, ⟨.hall 3 26, 7574900697903739200⟩, ⟨.assumptionRow 16, 1880083785950370⟩]
  caps := #[0, 7671466656041348160, 4001362675837647120, 0, 346748128235981472, 61966945361953632, 225933956965947685, 1880083785950370, 92604569911333550, 318386750973848256, 0, 762669565431834060, 0, 4025934092458998720] }

theorem case_43_30_16_checked :
    (Witness.linear .conditional case_43_30_16).check 43 30 16 = true := by
  change case_43_30_16.check 43 30 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_30_17 : Certificate := {
  objectiveScale := 25225200000
  eta := 248602201127280000
  rows := #[⟨.count 2, 16548743537726400⟩, ⟨.count 3, 883769018932800⟩, ⟨.path 3, 885500576552592⟩, ⟨.privateRow 2 23, 298899827226000⟩, ⟨.privateRow 2 25, 432889404948000⟩, ⟨.privateRow 2 26, 2424180667708800⟩, ⟨.privateRow 2 27, 3988766659878000⟩, ⟨.privateRow 2 28, 5553352652047200⟩, ⟨.privateRow 3 21, 128180239387200⟩, ⟨.privateRow 3 22, 200141075534400⟩, ⟨.privateRow 3 23, 627858295384320⟩, ⟨.privateRow 3 24, 749404645189200⟩, ⟨.privateRow 3 25, 1589135131584000⟩, ⟨.privateRow 3 26, 1703447918172000⟩, ⟨.privateRow 3 27, 2208298159267200⟩, ⟨.privateRow 4 14, 51894833760⟩, ⟨.privateRow 4 15, 168658209720⟩, ⟨.privateRow 4 16, 858623613120⟩, ⟨.privateRow 4 17, 15988798281456⟩, ⟨.privateRow 4 18, 22412802091680⟩, ⟨.privateRow 4 19, 65186398056780⟩, ⟨.privateRow 4 20, 121433910998400⟩, ⟨.privateRow 4 21, 184961836659600⟩, ⟨.privateRow 4 22, 378064242908352⟩, ⟨.privateRow 4 23, 535321157651280⟩, ⟨.privateRow 4 24, 683627943398400⟩, ⟨.privateRow 4 25, 856446388958160⟩, ⟨.privateRow 5 11, 59967363456⟩, ⟨.privateRow 5 12, 192752239680⟩, ⟨.privateRow 5 13, 1914342756480⟩, ⟨.privateRow 5 14, 3747960216000⟩, ⟨.privateRow 5 15, 8231883528960⟩, ⟨.privateRow 5 16, 17030731221504⟩, ⟨.privateRow 5 17, 27884824007040⟩, ⟨.privateRow 5 18, 44338369355280⟩, ⟨.privateRow 5 19, 98817648209280⟩, ⟨.privateRow 5 20, 154615852110720⟩, ⟨.privateRow 5 21, 219180713431680⟩, ⟨.privateRow 5 22, 283720588351200⟩, ⟨.privateRow 5 23, 369998632523520⟩, ⟨.privateRow 6 7, 20822001200⟩, ⟨.privateRow 6 8, 55117062000⟩, ⟨.privateRow 6 9, 292809391875⟩, ⟨.privateRow 6 10, 712112441040⟩, ⟨.privateRow 6 11, 1873980108000⟩, ⟨.privateRow 6 12, 3128105257200⟩, ⟨.privateRow 6 13, 5465775315000⟩, ⟨.privateRow 6 14, 8398838120400⟩, ⟨.privateRow 6 15, 12461967718200⟩, ⟨.privateRow 6 16, 27339287575600⟩, ⟨.privateRow 6 17, 48536084797200⟩, ⟨.privateRow 6 18, 73299393367200⟩, ⟨.privateRow 6 19, 103693565976000⟩, ⟨.privateRow 6 20, 135151445388960⟩, ⟨.privateRow 6 21, 65355056266500⟩, ⟨.privateRow 7 3, 7648898400⟩, ⟨.privateRow 7 4, 24094029960⟩, ⟨.privateRow 7 5, 67632364800⟩, ⟨.privateRow 7 6, 160626866400⟩, ⟨.privateRow 7 7, 510226516800⟩, ⟨.privateRow 7 8, 491919778350⟩, ⟨.privateRow 7 9, 2773490559840⟩, ⟨.privateRow 7 10, 1870155658800⟩, ⟨.privateRow 7 11, 3570858799200⟩, ⟨.privateRow 7 12, 4966047286200⟩, ⟨.privateRow 7 13, 9462382675200⟩, ⟨.privateRow 7 14, 17171012018160⟩, ⟨.privateRow 7 15, 28306023345600⟩, ⟨.privateRow 7 16, 42024003921900⟩, ⟨.privateRow 7 17, 58605859540800⟩, ⟨.privateRow 7 18, 10895855770800⟩, ⟨.privateRow 8 0, 32590958400⟩, ⟨.privateRow 8 1, 17036182800⟩, ⟨.privateRow 8 2, 53542288800⟩, ⟨.privateRow 8 3, 168658209720⟩, ⟨.privateRow 8 4, 424111287600⟩, ⟨.privateRow 8 5, 406029023400⟩, ⟨.privateRow 8 6, 1543277736000⟩, ⟨.privateRow 8 7, 2014528616100⟩, ⟨.privateRow 8 8, 1848993706560⟩, ⟨.privateRow 8 9, 2984982600600⟩, ⟨.privateRow 8 10, 4987670133600⟩, ⟨.privateRow 8 11, 8026881462600⟩, ⟨.privateRow 8 12, 5758229786400⟩, ⟨.privateRow 8 13, 36467652901680⟩, ⟨.privateRow 9 0, 626931527040⟩, ⟨.privateRow 9 1, 171335324160⟩, ⟨.privateRow 9 3, 2177762146560⟩, ⟨.privateRow 9 4, 1549156889280⟩, ⟨.privateRow 9 5, 2381057078400⟩, ⟨.privateRow 9 6, 2211296527440⟩, ⟨.privateRow 9 7, 4177726320768⟩, ⟨.privateRow 9 8, 5996736345600⟩, ⟨.privateRow 9 9, 2214179573760⟩, ⟨.privateRow 10 0, 6971206001760⟩, ⟨.privateRow 11 0, 3035847774960⟩, ⟨.privateRow 12 0, 1301923022400⟩, ⟨.hall 3 26, 88201997083200⟩]
  caps := #[0, 56158554003552, 0, 1897353157392, 944402977644, 1613257867200, 993176007075, 411396849540, 1689338503020, 0, 3099400143840, 0, 0, 96057561600000] }

theorem case_43_30_17_checked :
    (Witness.linear .negative case_43_30_17).check 43 30 17 = true := by
  change case_43_30_17.check 43 30 17 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_30_18 : Certificate := {
  objectiveScale := 401662800000
  eta := 4424933656034892000
  rows := #[⟨.count 2, 540493342749360000⟩, ⟨.count 3, 59932694824002000⟩, ⟨.count 4, 5508377129455200⟩, ⟨.count 5, 344812339872000⟩, ⟨.path 5, 337886761212000⟩, ⟨.privateRow 4 20, 257685650422200⟩, ⟨.privateRow 5 17, 67046843864000⟩, ⟨.privateRow 6 13, 448974400875⟩, ⟨.privateRow 6 14, 10775385621000⟩, ⟨.hall 10 7, 5838057225⟩, ⟨.hall 11 7, 14113984500⟩, ⟨.hall 6 11, 4643656875⟩, ⟨.hall 7 11, 13878884250⟩, ⟨.hall 9 11, 15012147150⟩, ⟨.hall 8 12, 16916785200⟩, ⟨.hall 10 12, 18476488800⟩, ⟨.hall 11 12, 7056992250⟩, ⟨.hall 5 13, 10790304525⟩, ⟨.hall 6 14, 11999169000⟩, ⟨.hall 4 19, 168001099812⟩]
  caps := #[0, 0, 0, 0, 17989193514600, 0, 29763549128775, 2693846405250, 0, 41091272913600, 17514171675, 137116165586400, 0, 2485489406400000] }

theorem case_43_30_18_checked :
    (Witness.linear .negative case_43_30_18).check 43 30 18 = true := by
  change case_43_30_18.check 43 30 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_30_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16796, 16796, 11934, 7072] }

theorem case_43_30_19_checked :
    (Witness.linear .negative case_43_30_19).check 43 30 19 = true := by
  change case_43_30_19.check 43 30 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_31_1_checked :
    (Witness.rising).check 43 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_31_2_checked :
    (Witness.rising).check 43 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_31_3_checked :
    (Witness.rising).check 43 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_31_4_checked :
    (Witness.rising).check 43 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_31_5_checked :
    (Witness.rising).check 43 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_31_6_checked :
    (Witness.rising).check 43 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_31_7_checked :
    (Witness.rising).check 43 31 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_31_8_checked :
    (Witness.rising).check 43 31 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_31_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_43_31_9_checked :
    (Witness.linear .positive case_43_31_9).check 43 31 9 = true := by
  change case_43_31_9.check 43 31 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_31_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_43_31_10_checked :
    (Witness.linear .positive case_43_31_10).check 43 31 10 = true := by
  change case_43_31_10.check 43 31 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_43_31_11_checked :
    (Witness.linear .positive case_43_31_11).check 43 31 11 = true := by
  change case_43_31_11.check 43 31 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_43_31_12_checked :
    (Witness.linear .positive case_43_31_12).check 43 31 12 = true := by
  change case_43_31_12.check 43 31 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_31_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_43_31_13_checked :
    (Witness.linear .positive case_43_31_13).check 43 31 13 = true := by
  change case_43_31_13.check 43 31 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_31_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_43_31_14_checked :
    (Witness.linear .positive case_43_31_14).check 43 31 14 = true := by
  change case_43_31_14.check 43 31 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_31_15 : Certificate := {
  objectiveScale := 189
  eta := 115000920
  rows := #[⟨.assumptionRow 15, 446⟩]
  caps := #[0, 0, 32978946, 9570490, 2816424, 842712, 259402, 83226, 27687, 9660, 3598, 362121, 193515] }

theorem case_43_31_15_checked :
    (Witness.linear .conditional case_43_31_15).check 43 31 15 = true := by
  change case_43_31_15.check 43 31 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_31_16 : Certificate := {
  objectiveScale := 679
  eta := 243411185
  rows := #[⟨.assumptionRow 16, 905⟩]
  caps := #[0, 0, 73873976, 22632610, 7009746, 2198508, 699608, 226369, 82060, 14506899, 11415789, 6144429, 2632773] }

theorem case_43_31_16_checked :
    (Witness.linear .conditional case_43_31_16).check 43 31 16 = true := by
  change case_43_31_16.check 43 31 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_31_17 : Certificate := {
  objectiveScale := 13922148240000
  eta := 372154365915553821600
  rows := #[⟨.count 2, 33839455017981412800⟩, ⟨.count 3, 2641128196525378560⟩, ⟨.count 4, 139006747185546240⟩, ⟨.path 3, 38753908633440000⟩, ⟨.path 4, 138458723088381696⟩, ⟨.privateRow 2 28, 3040772594683824000⟩, ⟨.privateRow 2 29, 4018163785832196000⟩, ⟨.privateRow 3 24, 356783984442902016⟩, ⟨.privateRow 3 25, 646526173107774960⟩, ⟨.privateRow 3 26, 1324425396795621120⟩, ⟨.privateRow 3 27, 1322012085212538720⟩, ⟨.privateRow 3 28, 1474050714946729920⟩, ⟨.privateRow 4 20, 22685128880974560⟩, ⟨.privateRow 4 21, 95636090449579680⟩, ⟨.privateRow 4 22, 153003954367424160⟩, ⟨.privateRow 4 23, 347902997817158784⟩, ⟨.privateRow 4 24, 468906440592910320⟩, ⟨.privateRow 4 25, 562784261174815680⟩, ⟨.privateRow 4 26, 572196176348837040⟩, ⟨.privateRow 5 15, 140776509013140⟩, ⟨.privateRow 5 16, 745932671134560⟩, ⟨.privateRow 5 17, 8253525614141808⟩, ⟨.privateRow 5 18, 21961135406049840⟩, ⟨.privateRow 5 19, 40935797728035210⟩, ⟨.privateRow 5 20, 92705640670122480⟩, ⟨.privateRow 5 21, 151515745557856680⟩, ⟨.privateRow 5 22, 204407491087079280⟩, ⟨.privateRow 5 23, 249415752111566040⟩, ⟨.privateRow 5 24, 145764019618176960⟩, ⟨.privateRow 6 12, 73876885196400⟩, ⟨.privateRow 6 13, 344758797583200⟩, ⟨.privateRow 6 14, 2628785831571900⟩, ⟨.privateRow 6 15, 6189987502062000⟩, ⟨.privateRow 6 16, 11514943839278880⟩, ⟨.privateRow 6 17, 28634133465938000⟩, ⟨.privateRow 6 18, 50981207192615700⟩, ⟨.privateRow 6 19, 77447601314226000⟩, ⟨.privateRow 6 20, 105898410657639600⟩, ⟨.privateRow 6 21, 73157816847155040⟩, ⟨.privateRow 7 9, 53868562122375⟩, ⟨.privateRow 7 10, 183871358711040⟩, ⟨.privateRow 7 11, 985025135952000⟩, ⟨.privateRow 7 12, 2373531721822800⟩, ⟨.privateRow 7 13, 4295120019890700⟩, ⟨.privateRow 7 14, 10201726237575600⟩, ⟨.privateRow 7 15, 20737241674629480⟩, ⟨.privateRow 7 16, 33939588295412800⟩, ⟨.privateRow 7 17, 49796098825923450⟩, ⟨.privateRow 7 18, 12756075510578400⟩, ⟨.privateRow 8 6, 40221859718040⟩, ⟨.privateRow 8 8, 754159869713250⟩, ⟨.privateRow 8 9, 1142300815992336⟩, ⟨.privateRow 8 10, 2378835703324080⟩, ⟨.privateRow 8 11, 5197901871254400⟩, ⟨.privateRow 8 12, 925102773514920⟩, ⟨.privateRow 8 13, 38064505424072400⟩, ⟨.privateRow 8 14, 1665184992326856⟩, ⟨.privateRow 9 5, 563106036052560⟩, ⟨.privateRow 9 6, 1135676039097600⟩, ⟨.privateRow 9 7, 1689318108157680⟩, ⟨.privateRow 9 8, 1673229364270464⟩, ⟨.privateRow 9 9, 12790551390336720⟩, ⟨.privateRow 10 2, 217198042477416⟩, ⟨.privateRow 10 3, 1752826307712480⟩, ⟨.privateRow 10 4, 2493755302518480⟩, ⟨.privateRow 10 5, 1618338355714080⟩, ⟨.privateRow 11 0, 2068552785499200⟩, ⟨.assumptionRow 17, 4061875993560⟩]
  caps := #[0, 40403065627746360, 1511344223395776, 465007916640960, 0, 1700078761536792, 148686736677360, 1967172976744350, 178365336495654, 0, 3397443574977144, 0, 184361323610882880] }

theorem case_43_31_17_checked :
    (Witness.linear .conditional case_43_31_17).check 43 31 17 = true := by
  change case_43_31_17.check 43 31 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_31_18 : Certificate := {
  objectiveScale := 459
  eta := 16612992
  rows := #[⟨.assumptionRow 18, 292⟩]
  caps := #[0, 0, 5851791, 2541687, 969000, 390660, 165676, 60697, 29796, 16620934, 16046640, 10920630, 6147336] }

theorem case_43_31_18_checked :
    (Witness.linear .conditional case_43_31_18).check 43 31 18 = true := by
  change case_43_31_18.check 43 31 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_31_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 58786, 58786, 41990, 25194] }

theorem case_43_31_19_checked :
    (Witness.linear .negative case_43_31_19).check 43 31 19 = true := by
  change case_43_31_19.check 43 31 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_31_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16796, 16796] }

theorem case_43_31_20_checked :
    (Witness.linear .negative case_43_31_20).check 43 31 20 = true := by
  change case_43_31_20.check 43 31 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_32_1_checked :
    (Witness.rising).check 43 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_32_2_checked :
    (Witness.rising).check 43 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_32_3_checked :
    (Witness.rising).check 43 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_32_4_checked :
    (Witness.rising).check 43 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_32_5_checked :
    (Witness.rising).check 43 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_32_6_checked :
    (Witness.rising).check 43 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_32_7_checked :
    (Witness.rising).check 43 32 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_32_8_checked :
    (Witness.rising).check 43 32 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_32_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_43_32_9_checked :
    (Witness.linear .positive case_43_32_9).check 43 32 9 = true := by
  change case_43_32_9.check 43 32 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_32_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_43_32_10_checked :
    (Witness.linear .positive case_43_32_10).check 43 32 10 = true := by
  change case_43_32_10.check 43 32 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_43_32_11_checked :
    (Witness.linear .positive case_43_32_11).check 43 32 11 = true := by
  change case_43_32_11.check 43 32 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_43_32_12_checked :
    (Witness.linear .positive case_43_32_12).check 43 32 12 = true := by
  change case_43_32_12.check 43 32 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_32_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_43_32_13_checked :
    (Witness.linear .positive case_43_32_13).check 43 32 13 = true := by
  change case_43_32_13.check 43 32 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_32_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_43_32_14_checked :
    (Witness.linear .positive case_43_32_14).check 43 32 14 = true := by
  change case_43_32_14.check 43 32 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_32_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_43_32_15_checked :
    (Witness.linear .positive case_43_32_15).check 43 32 15 = true := by
  change case_43_32_15.check 43 32 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_32_16 : Certificate := {
  objectiveScale := 975
  eta := 506992105
  rows := #[⟨.assumptionRow 16, 1432⟩]
  caps := #[0, 0, 149382332, 44480330, 13403208, 4160988, 1365624, 457457, 158631, 32519355, 24397197, 12497877] }

theorem case_43_32_16_checked :
    (Witness.linear .conditional case_43_32_16).check 43 32 16 = true := by
  change case_43_32_16.check 43 32 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_32_17 : Certificate := {
  objectiveScale := 785
  eta := 178123385
  rows := #[⟨.assumptionRow 17, 761⟩]
  caps := #[0, 0, 56304391, 18049240, 6443850, 2244000, 769860, 261716, 77878207, 70033183, 44138919, 22873245] }

theorem case_43_32_17_checked :
    (Witness.linear .conditional case_43_32_17).check 43 32 17 = true := by
  change case_43_32_17.check 43 32 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_32_18 : Certificate := {
  objectiveScale := 14
  eta := 543191
  rows := #[⟨.assumptionRow 18, 9⟩]
  caps := #[0, 0, 187473, 83334, 31008, 12852, 5292, 2002, 1604664, 1634380, 1144066, 662796] }

theorem case_43_32_18_checked :
    (Witness.linear .conditional case_43_32_18).check 43 32 18 = true := by
  change case_43_32_18.check 43 32 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_32_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 208012, 208012, 149226, 90440] }

theorem case_43_32_19_checked :
    (Witness.linear .negative case_43_32_19).check 43 32 19 = true := by
  change case_43_32_19.check 43 32 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_32_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58786, 58786] }

theorem case_43_32_20_checked :
    (Witness.linear .negative case_43_32_20).check 43 32 20 = true := by
  change case_43_32_20.check 43 32 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_33_1_checked :
    (Witness.rising).check 43 33 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_33_2_checked :
    (Witness.rising).check 43 33 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_33_3_checked :
    (Witness.rising).check 43 33 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_33_4_checked :
    (Witness.rising).check 43 33 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_33_5_checked :
    (Witness.rising).check 43 33 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_33_6_checked :
    (Witness.rising).check 43 33 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_33_7_checked :
    (Witness.rising).check 43 33 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_33_8_checked :
    (Witness.rising).check 43 33 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_33_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_43_33_9_checked :
    (Witness.linear .positive case_43_33_9).check 43 33 9 = true := by
  change case_43_33_9.check 43 33 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_33_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_43_33_10_checked :
    (Witness.linear .positive case_43_33_10).check 43 33 10 = true := by
  change case_43_33_10.check 43 33 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_33_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_43_33_11_checked :
    (Witness.linear .positive case_43_33_11).check 43 33 11 = true := by
  change case_43_33_11.check 43 33 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_33_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_43_33_12_checked :
    (Witness.linear .positive case_43_33_12).check 43 33 12 = true := by
  change case_43_33_12.check 43 33 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_33_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_43_33_13_checked :
    (Witness.linear .positive case_43_33_13).check 43 33 13 = true := by
  change case_43_33_13.check 43 33 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_33_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_43_33_14_checked :
    (Witness.linear .positive case_43_33_14).check 43 33 14 = true := by
  change case_43_33_14.check 43 33 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_33_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_43_33_15_checked :
    (Witness.linear .positive case_43_33_15).check 43 33 15 = true := by
  change case_43_33_15.check 43 33 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_33_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_43_33_16_checked :
    (Witness.linear .positive case_43_33_16).check 43 33 16 = true := by
  change case_43_33_16.check 43 33 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_33_17 : Certificate := {
  objectiveScale := 550
  eta := 262604225
  rows := #[⟨.assumptionRow 17, 607⟩]
  caps := #[0, 0, 82209314, 25759250, 8091150, 2551020, 889304, 314314, 90611950, 78272381, 47300880] }

theorem case_43_33_17_checked :
    (Witness.linear .conditional case_43_33_17).check 43 33 17 = true := by
  change case_43_33_17.check 43 33 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_33_18 : Certificate := {
  objectiveScale := 999
  eta := 186848090
  rows := #[⟨.assumptionRow 18, 799⟩]
  caps := #[0, 0, 68076734, 23396505, 7736496, 3093048, 1140020, 482885, 208049145, 196043881, 130668681] }

theorem case_43_33_18_checked :
    (Witness.linear .conditional case_43_33_18).check 43 33 18 = true := by
  change case_43_33_18.check 43 33 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_33_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 742900, 742900, 534888, 326876] }

theorem case_43_33_19_checked :
    (Witness.linear .negative case_43_33_19).check 43 33 19 = true := by
  change case_43_33_19.check 43 33 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_33_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 208012, 208012] }

theorem case_43_33_20_checked :
    (Witness.linear .negative case_43_33_20).check 43 33 20 = true := by
  change case_43_33_20.check 43 33 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_33_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_33_21_checked :
    (Witness.linear .negative case_43_33_21).check 43 33 21 = true := by
  change case_43_33_21.check 43 33 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_34_1_checked :
    (Witness.rising).check 43 34 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_34_2_checked :
    (Witness.rising).check 43 34 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_34_3_checked :
    (Witness.rising).check 43 34 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_34_4_checked :
    (Witness.rising).check 43 34 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_34_5_checked :
    (Witness.rising).check 43 34 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_34_6_checked :
    (Witness.rising).check 43 34 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_34_7_checked :
    (Witness.rising).check 43 34 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_34_8_checked :
    (Witness.rising).check 43 34 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_34_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_43_34_9_checked :
    (Witness.linear .positive case_43_34_9).check 43 34 9 = true := by
  change case_43_34_9.check 43 34 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_34_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_43_34_10_checked :
    (Witness.linear .positive case_43_34_10).check 43 34 10 = true := by
  change case_43_34_10.check 43 34 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_34_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_43_34_11_checked :
    (Witness.linear .positive case_43_34_11).check 43 34 11 = true := by
  change case_43_34_11.check 43 34 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_34_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_43_34_12_checked :
    (Witness.linear .positive case_43_34_12).check 43 34 12 = true := by
  change case_43_34_12.check 43 34 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_34_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_43_34_13_checked :
    (Witness.linear .positive case_43_34_13).check 43 34 13 = true := by
  change case_43_34_13.check 43 34 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_34_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_43_34_14_checked :
    (Witness.linear .positive case_43_34_14).check 43 34 14 = true := by
  change case_43_34_14.check 43 34 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_34_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_43_34_15_checked :
    (Witness.linear .positive case_43_34_15).check 43 34 15 = true := by
  change case_43_34_15.check 43 34 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_34_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_43_34_16_checked :
    (Witness.linear .positive case_43_34_16).check 43 34 16 = true := by
  change case_43_34_16.check 43 34 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_34_17 : Certificate := {
  objectiveScale := 13
  eta := 27098370
  rows := #[⟨.assumptionRow 17, 20⟩]
  caps := #[0, 0, 7837595, 2288132, 675070, 209950, 66300, 21320, 7007, 480700] }

theorem case_43_34_17_checked :
    (Witness.linear .conditional case_43_34_17).check 43 34 17 = true := by
  change case_43_34_17.check 43 34 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_34_18 : Certificate := {
  objectiveScale := 942
  eta := 144666665
  rows := #[⟨.assumptionRow 18, 739⟩]
  caps := #[0, 0, 55948673, 19911012, 6736488, 2581416, 985796, 693309240, 658058635, 444214870] }

theorem case_43_34_18_checked :
    (Witness.linear .conditional case_43_34_18).check 43 34 18 = true := by
  change case_43_34_18.check 43 34 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_34_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 2674440, 2674440, 1931540, 1188640] }

theorem case_43_34_19_checked :
    (Witness.linear .negative case_43_34_19).check 43 34 19 = true := by
  change case_43_34_19.check 43 34 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_34_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900] }

theorem case_43_34_20_checked :
    (Witness.linear .negative case_43_34_20).check 43 34 20 = true := by
  change case_43_34_20.check 43 34 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_34_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_34_21_checked :
    (Witness.linear .negative case_43_34_21).check 43 34 21 = true := by
  change case_43_34_21.check 43 34 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_34_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_34_22_checked :
    (Witness.linear .negative case_43_34_22).check 43 34 22 = true := by
  change case_43_34_22.check 43 34 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_35_1_checked :
    (Witness.rising).check 43 35 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_35_2_checked :
    (Witness.rising).check 43 35 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_35_3_checked :
    (Witness.rising).check 43 35 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_35_4_checked :
    (Witness.rising).check 43 35 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_35_5_checked :
    (Witness.rising).check 43 35 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_35_6_checked :
    (Witness.rising).check 43 35 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_35_7_checked :
    (Witness.rising).check 43 35 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_35_8_checked :
    (Witness.rising).check 43 35 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_35_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1] }

theorem case_43_35_9_checked :
    (Witness.linear .positive case_43_35_9).check 43 35 9 = true := by
  change case_43_35_9.check 43 35 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_35_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_43_35_10_checked :
    (Witness.linear .positive case_43_35_10).check 43 35 10 = true := by
  change case_43_35_10.check 43 35 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_35_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_43_35_11_checked :
    (Witness.linear .positive case_43_35_11).check 43 35 11 = true := by
  change case_43_35_11.check 43 35 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_35_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_43_35_12_checked :
    (Witness.linear .positive case_43_35_12).check 43 35 12 = true := by
  change case_43_35_12.check 43 35 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_35_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_43_35_13_checked :
    (Witness.linear .positive case_43_35_13).check 43 35 13 = true := by
  change case_43_35_13.check 43 35 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_35_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_43_35_14_checked :
    (Witness.linear .positive case_43_35_14).check 43 35 14 = true := by
  change case_43_35_14.check 43 35 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_35_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_43_35_15_checked :
    (Witness.linear .positive case_43_35_15).check 43 35 15 = true := by
  change case_43_35_15.check 43 35 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_35_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_43_35_16_checked :
    (Witness.linear .positive case_43_35_16).check 43 35 16 = true := by
  change case_43_35_16.check 43 35 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_35_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_43_35_17_checked :
    (Witness.linear .positive case_43_35_17).check 43 35 17 = true := by
  change case_43_35_17.check 43 35 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_35_18 : Certificate := {
  objectiveScale := 610
  eta := 303535830
  rows := #[⟨.assumptionRow 18, 563⟩]
  caps := #[0, 0, 103662955, 34485418, 11269470, 3635688, 1367820, 756368340, 696036120] }

theorem case_43_35_18_checked :
    (Witness.linear .conditional case_43_35_18).check 43 35 18 = true := by
  change case_43_35_18.check 43 35 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_35_19 : Certificate := {
  objectiveScale := 873
  eta := 53420950
  rows := #[⟨.assumptionRow 19, 530⟩]
  caps := #[0, 0, 21718026, 8695863, 3260685, 1449624, 570285, 1386598815, 1355174145] }

theorem case_43_35_19_checked :
    (Witness.linear .conditional case_43_35_19).check 43 35 19 = true := by
  change case_43_35_19.check 43 35 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_35_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 2674440, 2674440] }

theorem case_43_35_20_checked :
    (Witness.linear .negative case_43_35_20).check 43 35 20 = true := by
  change case_43_35_20.check 43 35 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_35_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_35_21_checked :
    (Witness.linear .negative case_43_35_21).check 43 35 21 = true := by
  change case_43_35_21.check 43 35 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_35_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_35_22_checked :
    (Witness.linear .negative case_43_35_22).check 43 35 22 = true := by
  change case_43_35_22.check 43 35 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_36_1_checked :
    (Witness.rising).check 43 36 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_36_2_checked :
    (Witness.rising).check 43 36 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_36_3_checked :
    (Witness.rising).check 43 36 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_36_4_checked :
    (Witness.rising).check 43 36 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_36_5_checked :
    (Witness.rising).check 43 36 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_36_6_checked :
    (Witness.rising).check 43 36 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_36_7_checked :
    (Witness.rising).check 43 36 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_36_8_checked :
    (Witness.rising).check 43 36 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_36_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_43_36_9_checked :
    (Witness.linear .positive case_43_36_9).check 43 36 9 = true := by
  change case_43_36_9.check 43 36 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_36_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_43_36_10_checked :
    (Witness.linear .positive case_43_36_10).check 43 36 10 = true := by
  change case_43_36_10.check 43 36 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_36_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_43_36_11_checked :
    (Witness.linear .positive case_43_36_11).check 43 36 11 = true := by
  change case_43_36_11.check 43 36 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_36_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_43_36_12_checked :
    (Witness.linear .positive case_43_36_12).check 43 36 12 = true := by
  change case_43_36_12.check 43 36 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_36_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42] }

theorem case_43_36_13_checked :
    (Witness.linear .positive case_43_36_13).check 43 36 13 = true := by
  change case_43_36_13.check 43 36 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_36_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_43_36_14_checked :
    (Witness.linear .positive case_43_36_14).check 43 36 14 = true := by
  change case_43_36_14.check 43 36 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_36_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_43_36_15_checked :
    (Witness.linear .positive case_43_36_15).check 43 36 15 = true := by
  change case_43_36_15.check 43 36 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_36_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_43_36_16_checked :
    (Witness.linear .positive case_43_36_16).check 43 36 16 = true := by
  change case_43_36_16.check 43 36 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_36_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_43_36_17_checked :
    (Witness.linear .positive case_43_36_17).check 43 36 17 = true := by
  change case_43_36_17.check 43 36 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_36_18 : Certificate := {
  objectiveScale := 8
  eta := 272786325
  rows := #[⟨.assumptionRow 18, 21⟩]
  caps := #[0, 0, 75847905, 21395520, 6091780, 1753244, 510986, 151164] }

theorem case_43_36_18_checked :
    (Witness.linear .conditional case_43_36_18).check 43 36 18 = true := by
  change case_43_36_18.check 43 36 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_36_19 : Certificate := {
  objectiveScale := 5
  eta := 284625
  rows := #[⟨.assumptionRow 19, 3⟩]
  caps := #[0, 0, 110561, 46398, 16473, 7752, 28514250, 27943965] }

theorem case_43_36_19_checked :
    (Witness.linear .conditional case_43_36_19).check 43 36 19 = true := by
  change case_43_36_19.check 43 36 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_36_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 9694845, 9694845] }

theorem case_43_36_20_checked :
    (Witness.linear .negative case_43_36_20).check 43 36 20 = true := by
  change case_43_36_20.check 43 36 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_36_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_36_21_checked :
    (Witness.linear .negative case_43_36_21).check 43 36 21 = true := by
  change case_43_36_21.check 43 36 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_36_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_36_22_checked :
    (Witness.linear .negative case_43_36_22).check 43 36 22 = true := by
  change case_43_36_22.check 43 36 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_36_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_43_36_23_checked :
    (Witness.linear .negative case_43_36_23).check 43 36 23 = true := by
  change case_43_36_23.check 43 36 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_37_1_checked :
    (Witness.rising).check 43 37 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_37_2_checked :
    (Witness.rising).check 43 37 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_37_3_checked :
    (Witness.rising).check 43 37 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_37_4_checked :
    (Witness.rising).check 43 37 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_37_5_checked :
    (Witness.rising).check 43 37 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_37_6_checked :
    (Witness.rising).check 43 37 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_37_7_checked :
    (Witness.rising).check 43 37 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_37_8_checked :
    (Witness.rising).check 43 37 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_37_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_43_37_9_checked :
    (Witness.linear .positive case_43_37_9).check 43 37 9 = true := by
  change case_43_37_9.check 43 37 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_37_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_43_37_10_checked :
    (Witness.linear .positive case_43_37_10).check 43 37 10 = true := by
  change case_43_37_10.check 43 37 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_37_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_43_37_11_checked :
    (Witness.linear .positive case_43_37_11).check 43 37 11 = true := by
  change case_43_37_11.check 43 37 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_37_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_43_37_12_checked :
    (Witness.linear .positive case_43_37_12).check 43 37 12 = true := by
  change case_43_37_12.check 43 37 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_37_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_43_37_13_checked :
    (Witness.linear .positive case_43_37_13).check 43 37 13 = true := by
  change case_43_37_13.check 43 37 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_37_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429] }

theorem case_43_37_14_checked :
    (Witness.linear .positive case_43_37_14).check 43 37 14 = true := by
  change case_43_37_14.check 43 37 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_37_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430] }

theorem case_43_37_15_checked :
    (Witness.linear .positive case_43_37_15).check 43 37 15 = true := by
  change case_43_37_15.check 43 37 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_37_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862] }

theorem case_43_37_16_checked :
    (Witness.linear .positive case_43_37_16).check 43 37 16 = true := by
  change case_43_37_16.check 43 37 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_37_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796] }

theorem case_43_37_17_checked :
    (Witness.linear .positive case_43_37_17).check 43 37 17 = true := by
  change case_43_37_17.check 43 37 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_37_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_43_37_18_checked :
    (Witness.linear .positive case_43_37_18).check 43 37 18 = true := by
  change case_43_37_18.check 43 37 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_37_19 : Certificate := {
  objectiveScale := 51
  eta := 24174150
  rows := #[⟨.assumptionRow 19, 40⟩]
  caps := #[0, 0, 7811375, 3023603, 1076559, 364344, 400099950] }

theorem case_43_37_19_checked :
    (Witness.linear .conditional case_43_37_19).check 43 37 19 = true := by
  change case_43_37_19.check 43 37 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_37_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 35357670, 35357670] }

theorem case_43_37_20_checked :
    (Witness.linear .negative case_43_37_20).check 43 37 20 = true := by
  change case_43_37_20.check 43 37 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_37_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_43_37_21_checked :
    (Witness.linear .negative case_43_37_21).check 43 37 21 = true := by
  change case_43_37_21.check 43 37 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_37_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_43_37_22_checked :
    (Witness.linear .negative case_43_37_22).check 43 37 22 = true := by
  change case_43_37_22.check 43 37 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_37_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_43_37_23_checked :
    (Witness.linear .negative case_43_37_23).check 43 37 23 = true := by
  change case_43_37_23.check 43 37 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_37_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_43_37_24_checked :
    (Witness.linear .negative case_43_37_24).check 43 37 24 = true := by
  change case_43_37_24.check 43 37 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_38_1_checked :
    (Witness.rising).check 43 38 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_38_2_checked :
    (Witness.rising).check 43 38 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_38_3_checked :
    (Witness.rising).check 43 38 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_38_4_checked :
    (Witness.rising).check 43 38 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_38_5_checked :
    (Witness.rising).check 43 38 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_38_6_checked :
    (Witness.rising).check 43 38 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_38_7_checked :
    (Witness.rising).check 43 38 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_38_8_checked :
    (Witness.rising).check 43 38 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_38_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_43_38_9_checked :
    (Witness.linear .positive case_43_38_9).check 43 38 9 = true := by
  change case_43_38_9.check 43 38 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_38_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_43_38_10_checked :
    (Witness.linear .positive case_43_38_10).check 43 38 10 = true := by
  change case_43_38_10.check 43 38 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_38_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_43_38_11_checked :
    (Witness.linear .positive case_43_38_11).check 43 38 11 = true := by
  change case_43_38_11.check 43 38 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_38_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_43_38_12_checked :
    (Witness.linear .positive case_43_38_12).check 43 38 12 = true := by
  change case_43_38_12.check 43 38 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_38_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_43_38_13_checked :
    (Witness.linear .positive case_43_38_13).check 43 38 13 = true := by
  change case_43_38_13.check 43 38 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_38_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_43_38_14_checked :
    (Witness.linear .positive case_43_38_14).check 43 38 14 = true := by
  change case_43_38_14.check 43 38 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_38_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862] }

theorem case_43_38_15_checked :
    (Witness.linear .positive case_43_38_15).check 43 38 15 = true := by
  change case_43_38_15.check 43 38 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_38_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796] }

theorem case_43_38_16_checked :
    (Witness.linear .positive case_43_38_16).check 43 38 16 = true := by
  change case_43_38_16.check 43 38 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_38_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786] }

theorem case_43_38_17_checked :
    (Witness.linear .positive case_43_38_17).check 43 38 17 = true := by
  change case_43_38_17.check 43 38 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_38_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012] }

theorem case_43_38_18_checked :
    (Witness.linear .positive case_43_38_18).check 43 38 18 = true := by
  change case_43_38_18.check 43 38 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_38_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900] }

theorem case_43_38_19_checked :
    (Witness.linear .positive case_43_38_19).check 43 38 19 = true := by
  change case_43_38_19.check 43 38 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_38_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 129644790, 129644790] }

theorem case_43_38_20_checked :
    (Witness.linear .negative case_43_38_20).check 43 38 20 = true := by
  change case_43_38_20.check 43 38 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_38_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_43_38_21_checked :
    (Witness.linear .negative case_43_38_21).check 43 38 21 = true := by
  change case_43_38_21.check 43 38 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_38_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_43_38_22_checked :
    (Witness.linear .negative case_43_38_22).check 43 38 22 = true := by
  change case_43_38_22.check 43 38 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_38_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_43_38_23_checked :
    (Witness.linear .negative case_43_38_23).check 43 38 23 = true := by
  change case_43_38_23.check 43 38 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_38_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_43_38_24_checked :
    (Witness.linear .negative case_43_38_24).check 43 38 24 = true := by
  change case_43_38_24.check 43 38 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_39_1_checked :
    (Witness.rising).check 43 39 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_39_2_checked :
    (Witness.rising).check 43 39 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_39_3_checked :
    (Witness.rising).check 43 39 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_39_4_checked :
    (Witness.rising).check 43 39 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_39_5_checked :
    (Witness.rising).check 43 39 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_39_6_checked :
    (Witness.rising).check 43 39 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_39_7_checked :
    (Witness.rising).check 43 39 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_39_8_checked :
    (Witness.rising).check 43 39 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_39_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_43_39_9_checked :
    (Witness.linear .positive case_43_39_9).check 43 39 9 = true := by
  change case_43_39_9.check 43 39 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_39_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_43_39_10_checked :
    (Witness.linear .positive case_43_39_10).check 43 39 10 = true := by
  change case_43_39_10.check 43 39 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_39_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_43_39_11_checked :
    (Witness.linear .positive case_43_39_11).check 43 39 11 = true := by
  change case_43_39_11.check 43 39 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_39_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_43_39_12_checked :
    (Witness.linear .positive case_43_39_12).check 43 39 12 = true := by
  change case_43_39_12.check 43 39 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_39_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_43_39_13_checked :
    (Witness.linear .positive case_43_39_13).check 43 39 13 = true := by
  change case_43_39_13.check 43 39 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_39_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_43_39_14_checked :
    (Witness.linear .positive case_43_39_14).check 43 39 14 = true := by
  change case_43_39_14.check 43 39 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_39_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796] }

theorem case_43_39_15_checked :
    (Witness.linear .positive case_43_39_15).check 43 39 15 = true := by
  change case_43_39_15.check 43 39 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_39_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786] }

theorem case_43_39_16_checked :
    (Witness.linear .positive case_43_39_16).check 43 39 16 = true := by
  change case_43_39_16.check 43 39 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_39_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012] }

theorem case_43_39_17_checked :
    (Witness.linear .positive case_43_39_17).check 43 39 17 = true := by
  change case_43_39_17.check 43 39 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_39_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900] }

theorem case_43_39_18_checked :
    (Witness.linear .positive case_43_39_18).check 43 39 18 = true := by
  change case_43_39_18.check 43 39 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_39_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440] }

theorem case_43_39_19_checked :
    (Witness.linear .positive case_43_39_19).check 43 39 19 = true := by
  change case_43_39_19.check 43 39 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_39_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 477638700, 477638700] }

theorem case_43_39_20_checked :
    (Witness.linear .negative case_43_39_20).check 43 39 20 = true := by
  change case_43_39_20.check 43 39 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_39_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_43_39_21_checked :
    (Witness.linear .negative case_43_39_21).check 43 39 21 = true := by
  change case_43_39_21.check 43 39 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_39_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_43_39_22_checked :
    (Witness.linear .negative case_43_39_22).check 43 39 22 = true := by
  change case_43_39_22.check 43 39 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_39_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_43_39_23_checked :
    (Witness.linear .negative case_43_39_23).check 43 39 23 = true := by
  change case_43_39_23.check 43 39 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_39_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_43_39_24_checked :
    (Witness.linear .negative case_43_39_24).check 43 39 24 = true := by
  change case_43_39_24.check 43 39 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_39_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_43_39_25_checked :
    (Witness.linear .negative case_43_39_25).check 43 39 25 = true := by
  change case_43_39_25.check 43 39 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_40_1_checked :
    (Witness.rising).check 43 40 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_40_2_checked :
    (Witness.rising).check 43 40 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_40_3_checked :
    (Witness.rising).check 43 40 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_40_4_checked :
    (Witness.rising).check 43 40 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_40_5_checked :
    (Witness.rising).check 43 40 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_40_6_checked :
    (Witness.rising).check 43 40 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_40_7_checked :
    (Witness.rising).check 43 40 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_40_8_checked :
    (Witness.rising).check 43 40 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_40_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_43_40_9_checked :
    (Witness.linear .positive case_43_40_9).check 43 40 9 = true := by
  change case_43_40_9.check 43 40 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_40_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_43_40_10_checked :
    (Witness.linear .positive case_43_40_10).check 43 40 10 = true := by
  change case_43_40_10.check 43 40 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_40_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_43_40_11_checked :
    (Witness.linear .positive case_43_40_11).check 43 40 11 = true := by
  change case_43_40_11.check 43 40 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_40_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_43_40_12_checked :
    (Witness.linear .positive case_43_40_12).check 43 40 12 = true := by
  change case_43_40_12.check 43 40 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_40_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_43_40_13_checked :
    (Witness.linear .positive case_43_40_13).check 43 40 13 = true := by
  change case_43_40_13.check 43 40 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_40_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_43_40_14_checked :
    (Witness.linear .positive case_43_40_14).check 43 40 14 = true := by
  change case_43_40_14.check 43 40 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_40_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_43_40_15_checked :
    (Witness.linear .positive case_43_40_15).check 43 40 15 = true := by
  change case_43_40_15.check 43 40 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_40_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012] }

theorem case_43_40_16_checked :
    (Witness.linear .positive case_43_40_16).check 43 40 16 = true := by
  change case_43_40_16.check 43 40 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_40_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900] }

theorem case_43_40_17_checked :
    (Witness.linear .positive case_43_40_17).check 43 40 17 = true := by
  change case_43_40_17.check 43 40 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_40_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440] }

theorem case_43_40_18_checked :
    (Witness.linear .positive case_43_40_18).check 43 40 18 = true := by
  change case_43_40_18.check 43 40 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_40_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845] }

theorem case_43_40_19_checked :
    (Witness.linear .positive case_43_40_19).check 43 40 19 = true := by
  change case_43_40_19.check 43 40 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_40_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670] }

theorem case_43_40_20_checked :
    (Witness.linear .positive case_43_40_20).check 43 40 20 = true := by
  change case_43_40_20.check 43 40 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_40_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_43_40_21_checked :
    (Witness.linear .negative case_43_40_21).check 43 40 21 = true := by
  change case_43_40_21.check 43 40 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_40_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_43_40_22_checked :
    (Witness.linear .negative case_43_40_22).check 43 40 22 = true := by
  change case_43_40_22.check 43 40 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_40_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_43_40_23_checked :
    (Witness.linear .negative case_43_40_23).check 43 40 23 = true := by
  change case_43_40_23.check 43 40 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_40_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_43_40_24_checked :
    (Witness.linear .negative case_43_40_24).check 43 40 24 = true := by
  change case_43_40_24.check 43 40 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_40_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_43_40_25_checked :
    (Witness.linear .negative case_43_40_25).check 43 40 25 = true := by
  change case_43_40_25.check 43 40 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_40_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_43_40_26_checked :
    (Witness.linear .negative case_43_40_26).check 43 40 26 = true := by
  change case_43_40_26.check 43 40 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_41_1_checked :
    (Witness.rising).check 43 41 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_41_2_checked :
    (Witness.rising).check 43 41 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_41_3_checked :
    (Witness.rising).check 43 41 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_41_4_checked :
    (Witness.rising).check 43 41 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_41_5_checked :
    (Witness.rising).check 43 41 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_41_6_checked :
    (Witness.rising).check 43 41 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_41_7_checked :
    (Witness.rising).check 43 41 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_41_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_43_41_8_checked :
    (Witness.linear .positive case_43_41_8).check 43 41 8 = true := by
  change case_43_41_8.check 43 41 8 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_41_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_43_41_9_checked :
    (Witness.linear .positive case_43_41_9).check 43 41 9 = true := by
  change case_43_41_9.check 43 41 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_41_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_43_41_10_checked :
    (Witness.linear .positive case_43_41_10).check 43 41 10 = true := by
  change case_43_41_10.check 43 41 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_41_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_43_41_11_checked :
    (Witness.linear .positive case_43_41_11).check 43 41 11 = true := by
  change case_43_41_11.check 43 41 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_41_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_43_41_12_checked :
    (Witness.linear .positive case_43_41_12).check 43 41 12 = true := by
  change case_43_41_12.check 43 41 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_41_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_43_41_13_checked :
    (Witness.linear .positive case_43_41_13).check 43 41 13 = true := by
  change case_43_41_13.check 43 41 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_41_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_43_41_14_checked :
    (Witness.linear .positive case_43_41_14).check 43 41 14 = true := by
  change case_43_41_14.check 43 41 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_41_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_43_41_15_checked :
    (Witness.linear .positive case_43_41_15).check 43 41 15 = true := by
  change case_43_41_15.check 43 41 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_41_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900] }

theorem case_43_41_16_checked :
    (Witness.linear .positive case_43_41_16).check 43 41 16 = true := by
  change case_43_41_16.check 43 41 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_41_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440] }

theorem case_43_41_17_checked :
    (Witness.linear .positive case_43_41_17).check 43 41 17 = true := by
  change case_43_41_17.check 43 41 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_41_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845] }

theorem case_43_41_18_checked :
    (Witness.linear .positive case_43_41_18).check 43 41 18 = true := by
  change case_43_41_18.check 43 41 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_41_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670] }

theorem case_43_41_19_checked :
    (Witness.linear .positive case_43_41_19).check 43 41 19 = true := by
  change case_43_41_19.check 43 41 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_41_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790] }

theorem case_43_41_20_checked :
    (Witness.linear .positive case_43_41_20).check 43 41 20 = true := by
  change case_43_41_20.check 43 41 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_41_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_43_41_21_checked :
    (Witness.linear .negative case_43_41_21).check 43 41 21 = true := by
  change case_43_41_21.check 43 41 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_41_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_43_41_22_checked :
    (Witness.linear .negative case_43_41_22).check 43 41 22 = true := by
  change case_43_41_22.check 43 41 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_41_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_43_41_23_checked :
    (Witness.linear .negative case_43_41_23).check 43 41 23 = true := by
  change case_43_41_23.check 43 41 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_41_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_43_41_24_checked :
    (Witness.linear .negative case_43_41_24).check 43 41 24 = true := by
  change case_43_41_24.check 43 41 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_41_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_43_41_25_checked :
    (Witness.linear .negative case_43_41_25).check 43 41 25 = true := by
  change case_43_41_25.check 43 41 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_41_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_43_41_26_checked :
    (Witness.linear .negative case_43_41_26).check 43 41 26 = true := by
  change case_43_41_26.check 43 41 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_42_1_checked :
    (Witness.rising).check 43 42 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_42_2_checked :
    (Witness.rising).check 43 42 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_42_3_checked :
    (Witness.rising).check 43 42 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_42_4_checked :
    (Witness.rising).check 43 42 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_42_5_checked :
    (Witness.rising).check 43 42 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_42_6_checked :
    (Witness.rising).check 43 42 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_43_42_7_checked :
    (Witness.rising).check 43 42 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_42_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_43_42_8_checked :
    (Witness.linear .positive case_43_42_8).check 43 42 8 = true := by
  change case_43_42_8.check 43 42 8 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_42_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_43_42_9_checked :
    (Witness.linear .positive case_43_42_9).check 43 42 9 = true := by
  change case_43_42_9.check 43 42 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_42_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_43_42_10_checked :
    (Witness.linear .positive case_43_42_10).check 43 42 10 = true := by
  change case_43_42_10.check 43 42 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_42_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_43_42_11_checked :
    (Witness.linear .positive case_43_42_11).check 43 42 11 = true := by
  change case_43_42_11.check 43 42 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_42_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_43_42_12_checked :
    (Witness.linear .positive case_43_42_12).check 43 42 12 = true := by
  change case_43_42_12.check 43 42 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_42_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_43_42_13_checked :
    (Witness.linear .positive case_43_42_13).check 43 42 13 = true := by
  change case_43_42_13.check 43 42 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_42_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_43_42_14_checked :
    (Witness.linear .positive case_43_42_14).check 43 42 14 = true := by
  change case_43_42_14.check 43 42 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_42_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_43_42_15_checked :
    (Witness.linear .positive case_43_42_15).check 43 42 15 = true := by
  change case_43_42_15.check 43 42 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_42_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_43_42_16_checked :
    (Witness.linear .positive case_43_42_16).check 43 42 16 = true := by
  change case_43_42_16.check 43 42 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_42_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0] }

theorem case_43_42_17_checked :
    (Witness.linear .positive case_43_42_17).check 43 42 17 = true := by
  change case_43_42_17.check 43 42 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_42_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0] }

theorem case_43_42_18_checked :
    (Witness.linear .positive case_43_42_18).check 43 42 18 = true := by
  change case_43_42_18.check 43 42 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_42_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0] }

theorem case_43_42_19_checked :
    (Witness.linear .positive case_43_42_19).check 43 42 19 = true := by
  change case_43_42_19.check 43 42 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_42_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0] }

theorem case_43_42_20_checked :
    (Witness.linear .positive case_43_42_20).check 43 42 20 = true := by
  change case_43_42_20.check 43 42 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_42_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0] }

theorem case_43_42_21_checked :
    (Witness.linear .positive case_43_42_21).check 43 42 21 = true := by
  change case_43_42_21.check 43 42 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_42_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_43_42_22_checked :
    (Witness.linear .negative case_43_42_22).check 43 42 22 = true := by
  change case_43_42_22.check 43 42 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_42_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_43_42_23_checked :
    (Witness.linear .negative case_43_42_23).check 43 42 23 = true := by
  change case_43_42_23.check 43 42 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_42_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_43_42_24_checked :
    (Witness.linear .negative case_43_42_24).check 43 42 24 = true := by
  change case_43_42_24.check 43 42 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_42_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_43_42_25_checked :
    (Witness.linear .negative case_43_42_25).check 43 42 25 = true := by
  change case_43_42_25.check 43 42 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_42_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_43_42_26_checked :
    (Witness.linear .negative case_43_42_26).check 43 42 26 = true := by
  change case_43_42_26.check 43 42 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_43_42_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_43_42_27_checked :
    (Witness.linear .negative case_43_42_27).check 43 42 27 = true := by
  change case_43_42_27.check 43 42 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_43 (a k : ℕ) (h : Domain 43 a k) :
    ∃ w : Witness, w.check 43 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 22 ≤ a := by omega
  have haHi : a ≤ 42 := by omega
  interval_cases a

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_43_22_1_checked⟩

    · exact ⟨Witness.rising, case_43_22_2_checked⟩

    · exact ⟨Witness.rising, case_43_22_3_checked⟩

    · exact ⟨Witness.rising, case_43_22_4_checked⟩

    · exact ⟨Witness.rising, case_43_22_5_checked⟩

    · exact ⟨Witness.rising, case_43_22_6_checked⟩

    · exact ⟨Witness.rising, case_43_22_7_checked⟩

    · exact ⟨Witness.rising, case_43_22_8_checked⟩

    · exact ⟨Witness.rising, case_43_22_9_checked⟩

    · exact ⟨Witness.linear .positive case_43_22_10, case_43_22_10_checked⟩

    · exact ⟨Witness.linear .positive case_43_22_11, case_43_22_11_checked⟩

    · exact ⟨Witness.linear .positive case_43_22_12, case_43_22_12_checked⟩

    · exact ⟨Witness.linear .conditional case_43_22_13, case_43_22_13_checked⟩

    · exact ⟨Witness.linear .conditional case_43_22_14, case_43_22_14_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_43_23_1_checked⟩

    · exact ⟨Witness.rising, case_43_23_2_checked⟩

    · exact ⟨Witness.rising, case_43_23_3_checked⟩

    · exact ⟨Witness.rising, case_43_23_4_checked⟩

    · exact ⟨Witness.rising, case_43_23_5_checked⟩

    · exact ⟨Witness.rising, case_43_23_6_checked⟩

    · exact ⟨Witness.rising, case_43_23_7_checked⟩

    · exact ⟨Witness.rising, case_43_23_8_checked⟩

    · exact ⟨Witness.rising, case_43_23_9_checked⟩

    · exact ⟨Witness.linear .positive case_43_23_10, case_43_23_10_checked⟩

    · exact ⟨Witness.linear .positive case_43_23_11, case_43_23_11_checked⟩

    · exact ⟨Witness.linear .positive case_43_23_12, case_43_23_12_checked⟩

    · exact ⟨Witness.linear .conditional case_43_23_13, case_43_23_13_checked⟩

    · exact ⟨Witness.linear .conditional case_43_23_14, case_43_23_14_checked⟩

  · have hkHi : k ≤ 15 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_43_24_1_checked⟩

    · exact ⟨Witness.rising, case_43_24_2_checked⟩

    · exact ⟨Witness.rising, case_43_24_3_checked⟩

    · exact ⟨Witness.rising, case_43_24_4_checked⟩

    · exact ⟨Witness.rising, case_43_24_5_checked⟩

    · exact ⟨Witness.rising, case_43_24_6_checked⟩

    · exact ⟨Witness.rising, case_43_24_7_checked⟩

    · exact ⟨Witness.rising, case_43_24_8_checked⟩

    · exact ⟨Witness.linear .positive case_43_24_9, case_43_24_9_checked⟩

    · exact ⟨Witness.linear .positive case_43_24_10, case_43_24_10_checked⟩

    · exact ⟨Witness.linear .positive case_43_24_11, case_43_24_11_checked⟩

    · exact ⟨Witness.linear .positive case_43_24_12, case_43_24_12_checked⟩

    · exact ⟨Witness.linear .conditional case_43_24_13, case_43_24_13_checked⟩

    · exact ⟨Witness.linear .conditional case_43_24_14, case_43_24_14_checked⟩

    · exact ⟨Witness.linear .conditional case_43_24_15, case_43_24_15_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_43_25_1_checked⟩

    · exact ⟨Witness.rising, case_43_25_2_checked⟩

    · exact ⟨Witness.rising, case_43_25_3_checked⟩

    · exact ⟨Witness.rising, case_43_25_4_checked⟩

    · exact ⟨Witness.rising, case_43_25_5_checked⟩

    · exact ⟨Witness.rising, case_43_25_6_checked⟩

    · exact ⟨Witness.rising, case_43_25_7_checked⟩

    · exact ⟨Witness.rising, case_43_25_8_checked⟩

    · exact ⟨Witness.linear .positive case_43_25_9, case_43_25_9_checked⟩

    · exact ⟨Witness.linear .positive case_43_25_10, case_43_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_43_25_11, case_43_25_11_checked⟩

    · exact ⟨Witness.linear .positive case_43_25_12, case_43_25_12_checked⟩

    · exact ⟨Witness.linear .conditional case_43_25_13, case_43_25_13_checked⟩

    · exact ⟨Witness.linear .conditional case_43_25_14, case_43_25_14_checked⟩

    · exact ⟨Witness.linear .conditional case_43_25_15, case_43_25_15_checked⟩

    · exact ⟨Witness.linear .negative case_43_25_16, case_43_25_16_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_43_26_1_checked⟩

    · exact ⟨Witness.rising, case_43_26_2_checked⟩

    · exact ⟨Witness.rising, case_43_26_3_checked⟩

    · exact ⟨Witness.rising, case_43_26_4_checked⟩

    · exact ⟨Witness.rising, case_43_26_5_checked⟩

    · exact ⟨Witness.rising, case_43_26_6_checked⟩

    · exact ⟨Witness.rising, case_43_26_7_checked⟩

    · exact ⟨Witness.rising, case_43_26_8_checked⟩

    · exact ⟨Witness.linear .positive case_43_26_9, case_43_26_9_checked⟩

    · exact ⟨Witness.linear .positive case_43_26_10, case_43_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_43_26_11, case_43_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_43_26_12, case_43_26_12_checked⟩

    · exact ⟨Witness.linear .conditional case_43_26_13, case_43_26_13_checked⟩

    · exact ⟨Witness.linear .conditional case_43_26_14, case_43_26_14_checked⟩

    · exact ⟨Witness.linear .conditional case_43_26_15, case_43_26_15_checked⟩

    · exact ⟨Witness.linear .negative case_43_26_16, case_43_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_43_27_1_checked⟩

    · exact ⟨Witness.rising, case_43_27_2_checked⟩

    · exact ⟨Witness.rising, case_43_27_3_checked⟩

    · exact ⟨Witness.rising, case_43_27_4_checked⟩

    · exact ⟨Witness.rising, case_43_27_5_checked⟩

    · exact ⟨Witness.rising, case_43_27_6_checked⟩

    · exact ⟨Witness.rising, case_43_27_7_checked⟩

    · exact ⟨Witness.rising, case_43_27_8_checked⟩

    · exact ⟨Witness.linear .positive case_43_27_9, case_43_27_9_checked⟩

    · exact ⟨Witness.linear .positive case_43_27_10, case_43_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_43_27_11, case_43_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_43_27_12, case_43_27_12_checked⟩

    · exact ⟨Witness.linear .positive case_43_27_13, case_43_27_13_checked⟩

    · exact ⟨Witness.linear .conditional case_43_27_14, case_43_27_14_checked⟩

    · exact ⟨Witness.linear .conditional case_43_27_15, case_43_27_15_checked⟩

    · exact ⟨Witness.linear .conditional case_43_27_16, case_43_27_16_checked⟩

    · exact ⟨Witness.linear .negative case_43_27_17, case_43_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_43_28_1_checked⟩

    · exact ⟨Witness.rising, case_43_28_2_checked⟩

    · exact ⟨Witness.rising, case_43_28_3_checked⟩

    · exact ⟨Witness.rising, case_43_28_4_checked⟩

    · exact ⟨Witness.rising, case_43_28_5_checked⟩

    · exact ⟨Witness.rising, case_43_28_6_checked⟩

    · exact ⟨Witness.rising, case_43_28_7_checked⟩

    · exact ⟨Witness.rising, case_43_28_8_checked⟩

    · exact ⟨Witness.linear .positive case_43_28_9, case_43_28_9_checked⟩

    · exact ⟨Witness.linear .positive case_43_28_10, case_43_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_43_28_11, case_43_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_43_28_12, case_43_28_12_checked⟩

    · exact ⟨Witness.linear .conditional case_43_28_13, case_43_28_13_checked⟩

    · exact ⟨Witness.linear .conditional case_43_28_14, case_43_28_14_checked⟩

    · exact ⟨Witness.linear .conditional case_43_28_15, case_43_28_15_checked⟩

    · exact ⟨Witness.linear .conditional case_43_28_16, case_43_28_16_checked⟩

    · exact ⟨Witness.linear .negative case_43_28_17, case_43_28_17_checked⟩

    · exact ⟨Witness.linear .negative case_43_28_18, case_43_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_43_29_1_checked⟩

    · exact ⟨Witness.rising, case_43_29_2_checked⟩

    · exact ⟨Witness.rising, case_43_29_3_checked⟩

    · exact ⟨Witness.rising, case_43_29_4_checked⟩

    · exact ⟨Witness.rising, case_43_29_5_checked⟩

    · exact ⟨Witness.rising, case_43_29_6_checked⟩

    · exact ⟨Witness.rising, case_43_29_7_checked⟩

    · exact ⟨Witness.rising, case_43_29_8_checked⟩

    · exact ⟨Witness.linear .positive case_43_29_9, case_43_29_9_checked⟩

    · exact ⟨Witness.linear .positive case_43_29_10, case_43_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_43_29_11, case_43_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_43_29_12, case_43_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_43_29_13, case_43_29_13_checked⟩

    · exact ⟨Witness.linear .conditional case_43_29_14, case_43_29_14_checked⟩

    · exact ⟨Witness.linear .conditional case_43_29_15, case_43_29_15_checked⟩

    · exact ⟨Witness.linear .conditional case_43_29_16, case_43_29_16_checked⟩

    · exact ⟨Witness.linear .negative case_43_29_17, case_43_29_17_checked⟩

    · exact ⟨Witness.linear .negative case_43_29_18, case_43_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_43_30_1_checked⟩

    · exact ⟨Witness.rising, case_43_30_2_checked⟩

    · exact ⟨Witness.rising, case_43_30_3_checked⟩

    · exact ⟨Witness.rising, case_43_30_4_checked⟩

    · exact ⟨Witness.rising, case_43_30_5_checked⟩

    · exact ⟨Witness.rising, case_43_30_6_checked⟩

    · exact ⟨Witness.rising, case_43_30_7_checked⟩

    · exact ⟨Witness.rising, case_43_30_8_checked⟩

    · exact ⟨Witness.linear .positive case_43_30_9, case_43_30_9_checked⟩

    · exact ⟨Witness.linear .positive case_43_30_10, case_43_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_43_30_11, case_43_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_43_30_12, case_43_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_43_30_13, case_43_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_43_30_14, case_43_30_14_checked⟩

    · exact ⟨Witness.linear .conditional case_43_30_15, case_43_30_15_checked⟩

    · exact ⟨Witness.linear .conditional case_43_30_16, case_43_30_16_checked⟩

    · exact ⟨Witness.linear .negative case_43_30_17, case_43_30_17_checked⟩

    · exact ⟨Witness.linear .negative case_43_30_18, case_43_30_18_checked⟩

    · exact ⟨Witness.linear .negative case_43_30_19, case_43_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_43_31_1_checked⟩

    · exact ⟨Witness.rising, case_43_31_2_checked⟩

    · exact ⟨Witness.rising, case_43_31_3_checked⟩

    · exact ⟨Witness.rising, case_43_31_4_checked⟩

    · exact ⟨Witness.rising, case_43_31_5_checked⟩

    · exact ⟨Witness.rising, case_43_31_6_checked⟩

    · exact ⟨Witness.rising, case_43_31_7_checked⟩

    · exact ⟨Witness.rising, case_43_31_8_checked⟩

    · exact ⟨Witness.linear .positive case_43_31_9, case_43_31_9_checked⟩

    · exact ⟨Witness.linear .positive case_43_31_10, case_43_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_43_31_11, case_43_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_43_31_12, case_43_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_43_31_13, case_43_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_43_31_14, case_43_31_14_checked⟩

    · exact ⟨Witness.linear .conditional case_43_31_15, case_43_31_15_checked⟩

    · exact ⟨Witness.linear .conditional case_43_31_16, case_43_31_16_checked⟩

    · exact ⟨Witness.linear .conditional case_43_31_17, case_43_31_17_checked⟩

    · exact ⟨Witness.linear .conditional case_43_31_18, case_43_31_18_checked⟩

    · exact ⟨Witness.linear .negative case_43_31_19, case_43_31_19_checked⟩

    · exact ⟨Witness.linear .negative case_43_31_20, case_43_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_43_32_1_checked⟩

    · exact ⟨Witness.rising, case_43_32_2_checked⟩

    · exact ⟨Witness.rising, case_43_32_3_checked⟩

    · exact ⟨Witness.rising, case_43_32_4_checked⟩

    · exact ⟨Witness.rising, case_43_32_5_checked⟩

    · exact ⟨Witness.rising, case_43_32_6_checked⟩

    · exact ⟨Witness.rising, case_43_32_7_checked⟩

    · exact ⟨Witness.rising, case_43_32_8_checked⟩

    · exact ⟨Witness.linear .positive case_43_32_9, case_43_32_9_checked⟩

    · exact ⟨Witness.linear .positive case_43_32_10, case_43_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_43_32_11, case_43_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_43_32_12, case_43_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_43_32_13, case_43_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_43_32_14, case_43_32_14_checked⟩

    · exact ⟨Witness.linear .positive case_43_32_15, case_43_32_15_checked⟩

    · exact ⟨Witness.linear .conditional case_43_32_16, case_43_32_16_checked⟩

    · exact ⟨Witness.linear .conditional case_43_32_17, case_43_32_17_checked⟩

    · exact ⟨Witness.linear .conditional case_43_32_18, case_43_32_18_checked⟩

    · exact ⟨Witness.linear .negative case_43_32_19, case_43_32_19_checked⟩

    · exact ⟨Witness.linear .negative case_43_32_20, case_43_32_20_checked⟩

  · have hkHi : k ≤ 21 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_43_33_1_checked⟩

    · exact ⟨Witness.rising, case_43_33_2_checked⟩

    · exact ⟨Witness.rising, case_43_33_3_checked⟩

    · exact ⟨Witness.rising, case_43_33_4_checked⟩

    · exact ⟨Witness.rising, case_43_33_5_checked⟩

    · exact ⟨Witness.rising, case_43_33_6_checked⟩

    · exact ⟨Witness.rising, case_43_33_7_checked⟩

    · exact ⟨Witness.rising, case_43_33_8_checked⟩

    · exact ⟨Witness.linear .positive case_43_33_9, case_43_33_9_checked⟩

    · exact ⟨Witness.linear .positive case_43_33_10, case_43_33_10_checked⟩

    · exact ⟨Witness.linear .positive case_43_33_11, case_43_33_11_checked⟩

    · exact ⟨Witness.linear .positive case_43_33_12, case_43_33_12_checked⟩

    · exact ⟨Witness.linear .positive case_43_33_13, case_43_33_13_checked⟩

    · exact ⟨Witness.linear .positive case_43_33_14, case_43_33_14_checked⟩

    · exact ⟨Witness.linear .positive case_43_33_15, case_43_33_15_checked⟩

    · exact ⟨Witness.linear .positive case_43_33_16, case_43_33_16_checked⟩

    · exact ⟨Witness.linear .conditional case_43_33_17, case_43_33_17_checked⟩

    · exact ⟨Witness.linear .conditional case_43_33_18, case_43_33_18_checked⟩

    · exact ⟨Witness.linear .negative case_43_33_19, case_43_33_19_checked⟩

    · exact ⟨Witness.linear .negative case_43_33_20, case_43_33_20_checked⟩

    · exact ⟨Witness.linear .negative case_43_33_21, case_43_33_21_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_43_34_1_checked⟩

    · exact ⟨Witness.rising, case_43_34_2_checked⟩

    · exact ⟨Witness.rising, case_43_34_3_checked⟩

    · exact ⟨Witness.rising, case_43_34_4_checked⟩

    · exact ⟨Witness.rising, case_43_34_5_checked⟩

    · exact ⟨Witness.rising, case_43_34_6_checked⟩

    · exact ⟨Witness.rising, case_43_34_7_checked⟩

    · exact ⟨Witness.rising, case_43_34_8_checked⟩

    · exact ⟨Witness.linear .positive case_43_34_9, case_43_34_9_checked⟩

    · exact ⟨Witness.linear .positive case_43_34_10, case_43_34_10_checked⟩

    · exact ⟨Witness.linear .positive case_43_34_11, case_43_34_11_checked⟩

    · exact ⟨Witness.linear .positive case_43_34_12, case_43_34_12_checked⟩

    · exact ⟨Witness.linear .positive case_43_34_13, case_43_34_13_checked⟩

    · exact ⟨Witness.linear .positive case_43_34_14, case_43_34_14_checked⟩

    · exact ⟨Witness.linear .positive case_43_34_15, case_43_34_15_checked⟩

    · exact ⟨Witness.linear .positive case_43_34_16, case_43_34_16_checked⟩

    · exact ⟨Witness.linear .conditional case_43_34_17, case_43_34_17_checked⟩

    · exact ⟨Witness.linear .conditional case_43_34_18, case_43_34_18_checked⟩

    · exact ⟨Witness.linear .negative case_43_34_19, case_43_34_19_checked⟩

    · exact ⟨Witness.linear .negative case_43_34_20, case_43_34_20_checked⟩

    · exact ⟨Witness.linear .negative case_43_34_21, case_43_34_21_checked⟩

    · exact ⟨Witness.linear .negative case_43_34_22, case_43_34_22_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_43_35_1_checked⟩

    · exact ⟨Witness.rising, case_43_35_2_checked⟩

    · exact ⟨Witness.rising, case_43_35_3_checked⟩

    · exact ⟨Witness.rising, case_43_35_4_checked⟩

    · exact ⟨Witness.rising, case_43_35_5_checked⟩

    · exact ⟨Witness.rising, case_43_35_6_checked⟩

    · exact ⟨Witness.rising, case_43_35_7_checked⟩

    · exact ⟨Witness.rising, case_43_35_8_checked⟩

    · exact ⟨Witness.linear .positive case_43_35_9, case_43_35_9_checked⟩

    · exact ⟨Witness.linear .positive case_43_35_10, case_43_35_10_checked⟩

    · exact ⟨Witness.linear .positive case_43_35_11, case_43_35_11_checked⟩

    · exact ⟨Witness.linear .positive case_43_35_12, case_43_35_12_checked⟩

    · exact ⟨Witness.linear .positive case_43_35_13, case_43_35_13_checked⟩

    · exact ⟨Witness.linear .positive case_43_35_14, case_43_35_14_checked⟩

    · exact ⟨Witness.linear .positive case_43_35_15, case_43_35_15_checked⟩

    · exact ⟨Witness.linear .positive case_43_35_16, case_43_35_16_checked⟩

    · exact ⟨Witness.linear .positive case_43_35_17, case_43_35_17_checked⟩

    · exact ⟨Witness.linear .conditional case_43_35_18, case_43_35_18_checked⟩

    · exact ⟨Witness.linear .conditional case_43_35_19, case_43_35_19_checked⟩

    · exact ⟨Witness.linear .negative case_43_35_20, case_43_35_20_checked⟩

    · exact ⟨Witness.linear .negative case_43_35_21, case_43_35_21_checked⟩

    · exact ⟨Witness.linear .negative case_43_35_22, case_43_35_22_checked⟩

  · have hkHi : k ≤ 23 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_43_36_1_checked⟩

    · exact ⟨Witness.rising, case_43_36_2_checked⟩

    · exact ⟨Witness.rising, case_43_36_3_checked⟩

    · exact ⟨Witness.rising, case_43_36_4_checked⟩

    · exact ⟨Witness.rising, case_43_36_5_checked⟩

    · exact ⟨Witness.rising, case_43_36_6_checked⟩

    · exact ⟨Witness.rising, case_43_36_7_checked⟩

    · exact ⟨Witness.rising, case_43_36_8_checked⟩

    · exact ⟨Witness.linear .positive case_43_36_9, case_43_36_9_checked⟩

    · exact ⟨Witness.linear .positive case_43_36_10, case_43_36_10_checked⟩

    · exact ⟨Witness.linear .positive case_43_36_11, case_43_36_11_checked⟩

    · exact ⟨Witness.linear .positive case_43_36_12, case_43_36_12_checked⟩

    · exact ⟨Witness.linear .positive case_43_36_13, case_43_36_13_checked⟩

    · exact ⟨Witness.linear .positive case_43_36_14, case_43_36_14_checked⟩

    · exact ⟨Witness.linear .positive case_43_36_15, case_43_36_15_checked⟩

    · exact ⟨Witness.linear .positive case_43_36_16, case_43_36_16_checked⟩

    · exact ⟨Witness.linear .positive case_43_36_17, case_43_36_17_checked⟩

    · exact ⟨Witness.linear .conditional case_43_36_18, case_43_36_18_checked⟩

    · exact ⟨Witness.linear .conditional case_43_36_19, case_43_36_19_checked⟩

    · exact ⟨Witness.linear .negative case_43_36_20, case_43_36_20_checked⟩

    · exact ⟨Witness.linear .negative case_43_36_21, case_43_36_21_checked⟩

    · exact ⟨Witness.linear .negative case_43_36_22, case_43_36_22_checked⟩

    · exact ⟨Witness.linear .negative case_43_36_23, case_43_36_23_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_43_37_1_checked⟩

    · exact ⟨Witness.rising, case_43_37_2_checked⟩

    · exact ⟨Witness.rising, case_43_37_3_checked⟩

    · exact ⟨Witness.rising, case_43_37_4_checked⟩

    · exact ⟨Witness.rising, case_43_37_5_checked⟩

    · exact ⟨Witness.rising, case_43_37_6_checked⟩

    · exact ⟨Witness.rising, case_43_37_7_checked⟩

    · exact ⟨Witness.rising, case_43_37_8_checked⟩

    · exact ⟨Witness.linear .positive case_43_37_9, case_43_37_9_checked⟩

    · exact ⟨Witness.linear .positive case_43_37_10, case_43_37_10_checked⟩

    · exact ⟨Witness.linear .positive case_43_37_11, case_43_37_11_checked⟩

    · exact ⟨Witness.linear .positive case_43_37_12, case_43_37_12_checked⟩

    · exact ⟨Witness.linear .positive case_43_37_13, case_43_37_13_checked⟩

    · exact ⟨Witness.linear .positive case_43_37_14, case_43_37_14_checked⟩

    · exact ⟨Witness.linear .positive case_43_37_15, case_43_37_15_checked⟩

    · exact ⟨Witness.linear .positive case_43_37_16, case_43_37_16_checked⟩

    · exact ⟨Witness.linear .positive case_43_37_17, case_43_37_17_checked⟩

    · exact ⟨Witness.linear .positive case_43_37_18, case_43_37_18_checked⟩

    · exact ⟨Witness.linear .conditional case_43_37_19, case_43_37_19_checked⟩

    · exact ⟨Witness.linear .negative case_43_37_20, case_43_37_20_checked⟩

    · exact ⟨Witness.linear .negative case_43_37_21, case_43_37_21_checked⟩

    · exact ⟨Witness.linear .negative case_43_37_22, case_43_37_22_checked⟩

    · exact ⟨Witness.linear .negative case_43_37_23, case_43_37_23_checked⟩

    · exact ⟨Witness.linear .negative case_43_37_24, case_43_37_24_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_43_38_1_checked⟩

    · exact ⟨Witness.rising, case_43_38_2_checked⟩

    · exact ⟨Witness.rising, case_43_38_3_checked⟩

    · exact ⟨Witness.rising, case_43_38_4_checked⟩

    · exact ⟨Witness.rising, case_43_38_5_checked⟩

    · exact ⟨Witness.rising, case_43_38_6_checked⟩

    · exact ⟨Witness.rising, case_43_38_7_checked⟩

    · exact ⟨Witness.rising, case_43_38_8_checked⟩

    · exact ⟨Witness.linear .positive case_43_38_9, case_43_38_9_checked⟩

    · exact ⟨Witness.linear .positive case_43_38_10, case_43_38_10_checked⟩

    · exact ⟨Witness.linear .positive case_43_38_11, case_43_38_11_checked⟩

    · exact ⟨Witness.linear .positive case_43_38_12, case_43_38_12_checked⟩

    · exact ⟨Witness.linear .positive case_43_38_13, case_43_38_13_checked⟩

    · exact ⟨Witness.linear .positive case_43_38_14, case_43_38_14_checked⟩

    · exact ⟨Witness.linear .positive case_43_38_15, case_43_38_15_checked⟩

    · exact ⟨Witness.linear .positive case_43_38_16, case_43_38_16_checked⟩

    · exact ⟨Witness.linear .positive case_43_38_17, case_43_38_17_checked⟩

    · exact ⟨Witness.linear .positive case_43_38_18, case_43_38_18_checked⟩

    · exact ⟨Witness.linear .positive case_43_38_19, case_43_38_19_checked⟩

    · exact ⟨Witness.linear .negative case_43_38_20, case_43_38_20_checked⟩

    · exact ⟨Witness.linear .negative case_43_38_21, case_43_38_21_checked⟩

    · exact ⟨Witness.linear .negative case_43_38_22, case_43_38_22_checked⟩

    · exact ⟨Witness.linear .negative case_43_38_23, case_43_38_23_checked⟩

    · exact ⟨Witness.linear .negative case_43_38_24, case_43_38_24_checked⟩

  · have hkHi : k ≤ 25 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_43_39_1_checked⟩

    · exact ⟨Witness.rising, case_43_39_2_checked⟩

    · exact ⟨Witness.rising, case_43_39_3_checked⟩

    · exact ⟨Witness.rising, case_43_39_4_checked⟩

    · exact ⟨Witness.rising, case_43_39_5_checked⟩

    · exact ⟨Witness.rising, case_43_39_6_checked⟩

    · exact ⟨Witness.rising, case_43_39_7_checked⟩

    · exact ⟨Witness.rising, case_43_39_8_checked⟩

    · exact ⟨Witness.linear .positive case_43_39_9, case_43_39_9_checked⟩

    · exact ⟨Witness.linear .positive case_43_39_10, case_43_39_10_checked⟩

    · exact ⟨Witness.linear .positive case_43_39_11, case_43_39_11_checked⟩

    · exact ⟨Witness.linear .positive case_43_39_12, case_43_39_12_checked⟩

    · exact ⟨Witness.linear .positive case_43_39_13, case_43_39_13_checked⟩

    · exact ⟨Witness.linear .positive case_43_39_14, case_43_39_14_checked⟩

    · exact ⟨Witness.linear .positive case_43_39_15, case_43_39_15_checked⟩

    · exact ⟨Witness.linear .positive case_43_39_16, case_43_39_16_checked⟩

    · exact ⟨Witness.linear .positive case_43_39_17, case_43_39_17_checked⟩

    · exact ⟨Witness.linear .positive case_43_39_18, case_43_39_18_checked⟩

    · exact ⟨Witness.linear .positive case_43_39_19, case_43_39_19_checked⟩

    · exact ⟨Witness.linear .negative case_43_39_20, case_43_39_20_checked⟩

    · exact ⟨Witness.linear .negative case_43_39_21, case_43_39_21_checked⟩

    · exact ⟨Witness.linear .negative case_43_39_22, case_43_39_22_checked⟩

    · exact ⟨Witness.linear .negative case_43_39_23, case_43_39_23_checked⟩

    · exact ⟨Witness.linear .negative case_43_39_24, case_43_39_24_checked⟩

    · exact ⟨Witness.linear .negative case_43_39_25, case_43_39_25_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_43_40_1_checked⟩

    · exact ⟨Witness.rising, case_43_40_2_checked⟩

    · exact ⟨Witness.rising, case_43_40_3_checked⟩

    · exact ⟨Witness.rising, case_43_40_4_checked⟩

    · exact ⟨Witness.rising, case_43_40_5_checked⟩

    · exact ⟨Witness.rising, case_43_40_6_checked⟩

    · exact ⟨Witness.rising, case_43_40_7_checked⟩

    · exact ⟨Witness.rising, case_43_40_8_checked⟩

    · exact ⟨Witness.linear .positive case_43_40_9, case_43_40_9_checked⟩

    · exact ⟨Witness.linear .positive case_43_40_10, case_43_40_10_checked⟩

    · exact ⟨Witness.linear .positive case_43_40_11, case_43_40_11_checked⟩

    · exact ⟨Witness.linear .positive case_43_40_12, case_43_40_12_checked⟩

    · exact ⟨Witness.linear .positive case_43_40_13, case_43_40_13_checked⟩

    · exact ⟨Witness.linear .positive case_43_40_14, case_43_40_14_checked⟩

    · exact ⟨Witness.linear .positive case_43_40_15, case_43_40_15_checked⟩

    · exact ⟨Witness.linear .positive case_43_40_16, case_43_40_16_checked⟩

    · exact ⟨Witness.linear .positive case_43_40_17, case_43_40_17_checked⟩

    · exact ⟨Witness.linear .positive case_43_40_18, case_43_40_18_checked⟩

    · exact ⟨Witness.linear .positive case_43_40_19, case_43_40_19_checked⟩

    · exact ⟨Witness.linear .positive case_43_40_20, case_43_40_20_checked⟩

    · exact ⟨Witness.linear .negative case_43_40_21, case_43_40_21_checked⟩

    · exact ⟨Witness.linear .negative case_43_40_22, case_43_40_22_checked⟩

    · exact ⟨Witness.linear .negative case_43_40_23, case_43_40_23_checked⟩

    · exact ⟨Witness.linear .negative case_43_40_24, case_43_40_24_checked⟩

    · exact ⟨Witness.linear .negative case_43_40_25, case_43_40_25_checked⟩

    · exact ⟨Witness.linear .negative case_43_40_26, case_43_40_26_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_43_41_1_checked⟩

    · exact ⟨Witness.rising, case_43_41_2_checked⟩

    · exact ⟨Witness.rising, case_43_41_3_checked⟩

    · exact ⟨Witness.rising, case_43_41_4_checked⟩

    · exact ⟨Witness.rising, case_43_41_5_checked⟩

    · exact ⟨Witness.rising, case_43_41_6_checked⟩

    · exact ⟨Witness.rising, case_43_41_7_checked⟩

    · exact ⟨Witness.linear .positive case_43_41_8, case_43_41_8_checked⟩

    · exact ⟨Witness.linear .positive case_43_41_9, case_43_41_9_checked⟩

    · exact ⟨Witness.linear .positive case_43_41_10, case_43_41_10_checked⟩

    · exact ⟨Witness.linear .positive case_43_41_11, case_43_41_11_checked⟩

    · exact ⟨Witness.linear .positive case_43_41_12, case_43_41_12_checked⟩

    · exact ⟨Witness.linear .positive case_43_41_13, case_43_41_13_checked⟩

    · exact ⟨Witness.linear .positive case_43_41_14, case_43_41_14_checked⟩

    · exact ⟨Witness.linear .positive case_43_41_15, case_43_41_15_checked⟩

    · exact ⟨Witness.linear .positive case_43_41_16, case_43_41_16_checked⟩

    · exact ⟨Witness.linear .positive case_43_41_17, case_43_41_17_checked⟩

    · exact ⟨Witness.linear .positive case_43_41_18, case_43_41_18_checked⟩

    · exact ⟨Witness.linear .positive case_43_41_19, case_43_41_19_checked⟩

    · exact ⟨Witness.linear .positive case_43_41_20, case_43_41_20_checked⟩

    · exact ⟨Witness.linear .negative case_43_41_21, case_43_41_21_checked⟩

    · exact ⟨Witness.linear .negative case_43_41_22, case_43_41_22_checked⟩

    · exact ⟨Witness.linear .negative case_43_41_23, case_43_41_23_checked⟩

    · exact ⟨Witness.linear .negative case_43_41_24, case_43_41_24_checked⟩

    · exact ⟨Witness.linear .negative case_43_41_25, case_43_41_25_checked⟩

    · exact ⟨Witness.linear .negative case_43_41_26, case_43_41_26_checked⟩

  · have hkHi : k ≤ 27 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_43_42_1_checked⟩

    · exact ⟨Witness.rising, case_43_42_2_checked⟩

    · exact ⟨Witness.rising, case_43_42_3_checked⟩

    · exact ⟨Witness.rising, case_43_42_4_checked⟩

    · exact ⟨Witness.rising, case_43_42_5_checked⟩

    · exact ⟨Witness.rising, case_43_42_6_checked⟩

    · exact ⟨Witness.rising, case_43_42_7_checked⟩

    · exact ⟨Witness.linear .positive case_43_42_8, case_43_42_8_checked⟩

    · exact ⟨Witness.linear .positive case_43_42_9, case_43_42_9_checked⟩

    · exact ⟨Witness.linear .positive case_43_42_10, case_43_42_10_checked⟩

    · exact ⟨Witness.linear .positive case_43_42_11, case_43_42_11_checked⟩

    · exact ⟨Witness.linear .positive case_43_42_12, case_43_42_12_checked⟩

    · exact ⟨Witness.linear .positive case_43_42_13, case_43_42_13_checked⟩

    · exact ⟨Witness.linear .positive case_43_42_14, case_43_42_14_checked⟩

    · exact ⟨Witness.linear .positive case_43_42_15, case_43_42_15_checked⟩

    · exact ⟨Witness.linear .positive case_43_42_16, case_43_42_16_checked⟩

    · exact ⟨Witness.linear .positive case_43_42_17, case_43_42_17_checked⟩

    · exact ⟨Witness.linear .positive case_43_42_18, case_43_42_18_checked⟩

    · exact ⟨Witness.linear .positive case_43_42_19, case_43_42_19_checked⟩

    · exact ⟨Witness.linear .positive case_43_42_20, case_43_42_20_checked⟩

    · exact ⟨Witness.linear .positive case_43_42_21, case_43_42_21_checked⟩

    · exact ⟨Witness.linear .negative case_43_42_22, case_43_42_22_checked⟩

    · exact ⟨Witness.linear .negative case_43_42_23, case_43_42_23_checked⟩

    · exact ⟨Witness.linear .negative case_43_42_24, case_43_42_24_checked⟩

    · exact ⟨Witness.linear .negative case_43_42_25, case_43_42_25_checked⟩

    · exact ⟨Witness.linear .negative case_43_42_26, case_43_42_26_checked⟩

    · exact ⟨Witness.linear .negative case_43_42_27, case_43_42_27_checked⟩


#print axioms coverage_43
end ForestUnimodality.FiniteRows.FiniteData
