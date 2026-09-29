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

theorem case_41_21_1_checked :
    (Witness.rising).check 41 21 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_21_2_checked :
    (Witness.rising).check 41 21 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_21_3_checked :
    (Witness.rising).check 41 21 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_21_4_checked :
    (Witness.rising).check 41 21 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_21_5_checked :
    (Witness.rising).check 41 21 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_21_6_checked :
    (Witness.rising).check 41 21 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_21_7_checked :
    (Witness.rising).check 41 21 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_21_8_checked :
    (Witness.rising).check 41 21 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_21_9 : Certificate := {
  objectiveScale := 1860841525400000
  eta := 27445468292424262080
  rows := #[⟨.count 2, 6313701315092371200⟩, ⟨.count 3, 934300245112153920⟩, ⟨.count 4, 147057095396090880⟩, ⟨.count 5, 28135923864048000⟩, ⟨.count 6, 6846408140251680⟩, ⟨.count 7, 2391553528444080⟩, ⟨.count 8, 1846870899793920⟩, ⟨.count 10, 295132068504000⟩, ⟨.path 9, 531979420452480⟩, ⟨.path 10, 301456327114800⟩, ⟨.privateRow 9 0, 19793187728160⟩, ⟨.hall 7 3, 1323409672260⟩, ⟨.hall 7 4, 1133681913936⟩, ⟨.hall 6 6, 1384570197920⟩, ⟨.hall 5 9, 1285347004695⟩, ⟨.hall 8 12, 13318780527360⟩, ⟨.hall 4 13, 23722445610864⟩, ⟨.hall 5 13, 30564322054695⟩, ⟨.hall 3 17, 3720194377579680⟩]
  caps := #[0, 42812098546451520, 619323955604640, 1032547338748640, 527438718526720, 23337670356000, 0, 5917502470880, 13970625606080, 11287333314400, 6324258610800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_41_21_9_checked :
    (Witness.linear .positive case_41_21_9).check 41 21 9 = true := by
  change case_41_21_9.check 41 21 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_21_10 : Certificate := {
  objectiveScale := 240669000000
  eta := 4943865879912960
  rows := #[⟨.count 2, 1270993859815680⟩, ⟨.count 3, 217670208275520⟩, ⟨.count 4, 40423766423040⟩, ⟨.count 5, 8462499645600⟩, ⟨.count 6, 2084963680800⟩, ⟨.count 7, 637753596480⟩, ⟨.count 8, 264158294400⟩, ⟨.count 9, 243402999840⟩, ⟨.path 10, 23739991275⟩, ⟨.path 11, 59959399500⟩, ⟨.privateRow 4 17, 1717028913600⟩, ⟨.privateRow 8 4, 7264353096⟩, ⟨.privateRow 8 5, 5975009040⟩, ⟨.privateRow 9 2, 4745700960⟩, ⟨.privateRow 10 0, 9091162080⟩, ⟨.privateRow 11 0, 5473409760⟩, ⟨.privateRow 12 0, 1132106976⟩, ⟨.privateRow 12 7, 16352656320⟩, ⟨.hall 8 3, 1092522816⟩, ⟨.hall 12 4, 850577728⟩, ⟨.hall 7 5, 575855280⟩, ⟨.hall 6 7, 557000444⟩, ⟨.hall 6 8, 45197152⟩, ⟨.hall 5 11, 2695492800⟩, ⟨.hall 9 11, 3301978680⟩, ⟨.hall 4 14, 35013922944⟩]
  caps := #[0, 15670558658040, 0, 0, 0, 25250425200, 9539406877, 8059523472, 250696875, 0, 2707430115, 0, 3647900256, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_41_21_10_checked :
    (Witness.linear .positive case_41_21_10).check 41 21 10 = true := by
  change case_41_21_10.check 41 21 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_21_11 : Certificate := {
  objectiveScale := 32089200000
  eta := 957534463005120
  rows := #[⟨.count 2, 297017968927680⟩, ⟨.count 3, 63263755114560⟩, ⟨.count 4, 12699005679360⟩, ⟨.count 5, 2825213391000⟩, ⟨.count 6, 709588479600⟩, ⟨.count 7, 207620332920⟩, ⟨.count 8, 71161009920⟩, ⟨.count 9, 31537265760⟩, ⟨.count 10, 31978346400⟩, ⟨.path 12, 7752517344⟩, ⟨.path 13, 1582989408⟩, ⟨.privateRow 8 6, 1693106415⟩, ⟨.privateRow 9 4, 1602320720⟩, ⟨.privateRow 11 0, 1543782240⟩, ⟨.privateRow 12 0, 781692912⟩, ⟨.privateRow 13 0, 179699520⟩, ⟨.hall 9 3, 312432120⟩, ⟨.hall 8 5, 172630920⟩, ⟨.hall 7 7, 195707655⟩, ⟨.hall 10 9, 130319280⟩, ⟨.hall 6 10, 642367440⟩, ⟨.hall 10 10, 100245600⟩, ⟨.hall 9 11, 404323920⟩, ⟨.hall 5 12, 1963859040⟩, ⟨.hall 4 15, 46687520880⟩]
  caps := #[0, 5017322618880, 0, 0, 11346741120, 0, 0, 2511300792, 1919495721, 764381200, 408991440, 632682336, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_41_21_11_checked :
    (Witness.linear .positive case_41_21_11).check 41 21 11 = true := by
  change case_41_21_11.check 41 21 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_21_12 : Certificate := {
  objectiveScale := 8751600000
  eta := 292014056093760
  rows := #[⟨.count 2, 83994251140800⟩, ⟨.count 3, 19122095472480⟩, ⟨.count 4, 4905796896000⟩, ⟨.count 5, 1274631157800⟩, ⟨.count 6, 392463751680⟩, ⟨.count 7, 131405274000⟩, ⟨.count 8, 49057968960⟩, ⟨.count 9, 22642139520⟩, ⟨.count 10, 19481061600⟩, ⟨.count 11, 8895126240⟩, ⟨.path 12, 2500507152⟩, ⟨.privateRow 9 5, 1460058600⟩, ⟨.privateRow 9 6, 641784000⟩, ⟨.privateRow 10 3, 216456240⟩, ⟨.privateRow 11 0, 504569520⟩, ⟨.privateRow 12 0, 1141091952⟩, ⟨.privateRow 13 0, 973372400⟩, ⟨.hall 10 2, 132175680⟩, ⟨.hall 10 3, 134496180⟩, ⟨.hall 9 4, 221255034⟩, ⟨.hall 8 6, 179430240⟩, ⟨.hall 7 7, 37887135⟩, ⟨.hall 7 8, 234494260⟩, ⟨.hall 11 9, 323459136⟩, ⟨.hall 6 10, 627664752⟩, ⟨.hall 5 13, 8437052910⟩, ⟨.hall 4 15, 59312733480⟩, ⟨.hall 3 17, 549371382560⟩, ⟨.assumptionRow 12, 14357874960⟩]
  caps := #[0, 1646308984320, 5724946656, 0, 9121889920, 1784801304, 1939792140, 0, 260663040, 0, 0, 213984576, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_41_21_12_checked :
    (Witness.linear .conditional case_41_21_12).check 41 21 12 = true := by
  change case_41_21_12.check 41 21 12 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_21_13 : Certificate := {
  objectiveScale := 25132800000
  eta := 244476884171520
  rows := #[⟨.count 2, 67910245603200⟩, ⟨.count 3, 19658228990400⟩, ⟨.count 4, 6111221276160⟩, ⟨.count 5, 1988599813200⟩, ⟨.count 6, 707836409280⟩, ⟨.count 7, 271570899600⟩, ⟨.count 8, 114288894720⟩, ⟨.count 9, 52562109600⟩, ⟨.count 10, 25729704000⟩, ⟨.count 11, 21833491680⟩, ⟨.count 12, 18329351040⟩, ⟨.count 14, 24528984480⟩, ⟨.path 10, 24066900⟩, ⟨.path 11, 3745684800⟩, ⟨.privateRow 3 18, 2581383604800⟩, ⟨.privateRow 13 0, 1422621200⟩, ⟨.hall 11 2, 698581884⟩, ⟨.hall 10 3, 270106200⟩, ⟨.hall 11 3, 318645756⟩, ⟨.hall 10 4, 602110080⟩, ⟨.hall 9 5, 656078280⟩, ⟨.hall 8 6, 77193600⟩, ⟨.hall 9 6, 188596980⟩, ⟨.hall 8 7, 937558160⟩, ⟨.hall 12 8, 598998400⟩, ⟨.hall 7 9, 2077804872⟩, ⟨.hall 6 12, 26377322400⟩, ⟨.hall 5 13, 32522805315⟩, ⟨.hall 4 14, 29943225312⟩, ⟨.hall 4 15, 34423028640⟩, ⟨.hall 3 17, 3819123948640⟩, ⟨.assumptionRow 13, 18245335680⟩]
  caps := #[0, 40618464480, 0, 0, 12033450000, 0, 0, 1482521040, 70181100, 0, 436738500, 157528800, 0, 522059120, 603815520, 0, 0, 0, 0, 0, 0] }

theorem case_41_21_13_checked :
    (Witness.linear .conditional case_41_21_13).check 41 21 13 = true := by
  change case_41_21_13.check 41 21 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_22_1_checked :
    (Witness.rising).check 41 22 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_22_2_checked :
    (Witness.rising).check 41 22 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_22_3_checked :
    (Witness.rising).check 41 22 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_22_4_checked :
    (Witness.rising).check 41 22 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_22_5_checked :
    (Witness.rising).check 41 22 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_22_6_checked :
    (Witness.rising).check 41 22 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_22_7_checked :
    (Witness.rising).check 41 22 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_22_8_checked :
    (Witness.rising).check 41 22 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_22_9 : Certificate := {
  objectiveScale := 37436533634500000
  eta := 740342014030088870400
  rows := #[⟨.count 2, 152368369049121825600⟩, ⟨.count 3, 20702522896786130400⟩, ⟨.count 4, 3257966750689450800⟩, ⟨.count 5, 604854586625889600⟩, ⟨.count 6, 144340299081178200⟩, ⟨.count 7, 49170871115566200⟩, ⟨.count 8, 37010333097738000⟩, ⟨.path 9, 11691529257328830⟩, ⟨.path 10, 5533777895946300⟩, ⟨.privateRow 5 12, 8248017090353040⟩, ⟨.privateRow 5 13, 29967795428282712⟩, ⟨.privateRow 6 9, 8837161168235400⟩, ⟨.privateRow 6 10, 9678795565210200⟩, ⟨.privateRow 6 11, 11864707124019750⟩, ⟨.privateRow 6 12, 12961169713411920⟩, ⟨.privateRow 7 5, 1153568823825600⟩, ⟨.privateRow 7 7, 10171547327541600⟩, ⟨.privateRow 7 8, 2124317588518125⟩, ⟨.privateRow 7 9, 129482214919200⟩, ⟨.privateRow 8 2, 711737174956500⟩, ⟨.privateRow 8 3, 1696306933646325⟩, ⟨.privateRow 8 4, 684931489146450⟩, ⟨.privateRow 9 0, 858310136775000⟩, ⟨.privateRow 10 0, 425933104181760⟩, ⟨.hall 4 13, 33211553410035⟩, ⟨.hall 4 14, 259435178087085⟩, ⟨.hall 5 16, 26684761174671600⟩, ⟨.hall 3 18, 264804759216597600⟩]
  caps := #[0, 470513234505705300, 8936858144487000, 0, 0, 0, 310681041825700, 0, 426200536762000, 284815674309530, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_41_22_9_checked :
    (Witness.linear .positive case_41_22_9).check 41 22 9 = true := by
  change case_41_22_9.check 41 22 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_22_10 : Certificate := {
  objectiveScale := 407957550000
  eta := 12835036419004800
  rows := #[⟨.count 2, 3074070450971520⟩, ⟨.count 3, 494013747427200⟩, ⟨.count 4, 84355177626720⟩, ⟨.count 5, 17243876089440⟩, ⟨.count 6, 4061299001760⟩, ⟨.count 7, 1147201735680⟩, ⟨.count 8, 478000723200⟩, ⟨.count 9, 410646075840⟩, ⟨.path 10, 61030449480⟩, ⟨.path 11, 90202552440⟩, ⟨.privateRow 6 10, 82430736960⟩, ⟨.privateRow 6 11, 305152247400⟩, ⟨.privateRow 6 12, 337331938944⟩, ⟨.privateRow 7 7, 31866714880⟩, ⟨.privateRow 7 8, 110751060420⟩, ⟨.privateRow 7 9, 149984920800⟩, ⟨.privateRow 7 10, 189493143840⟩, ⟨.privateRow 7 11, 158764525920⟩, ⟨.privateRow 8 4, 7332965640⟩, ⟨.privateRow 8 5, 44513817348⟩, ⟨.privateRow 8 6, 61741760080⟩, ⟨.privateRow 8 7, 73567298805⟩, ⟨.privateRow 9 2, 20459879440⟩, ⟨.privateRow 9 3, 23504994240⟩, ⟨.privateRow 10 0, 12785683680⟩, ⟨.privateRow 11 0, 7604556960⟩, ⟨.hall 5 11, 920519600⟩, ⟨.hall 4 15, 72344472200⟩, ⟨.hall 6 15, 253831187610⟩, ⟨.hall 3 18, 4709565020160⟩]
  caps := #[0, 23846261078640, 0, 898812074160, 146864718000, 0, 0, 3037714680, 0, 254716280, 9727955160, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_41_22_10_checked :
    (Witness.linear .positive case_41_22_10).check 41 22 10 = true := by
  change case_41_22_10.check 41 22 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_22_11 : Certificate := {
  objectiveScale := 99099000000
  eta := 4353404165510400
  rows := #[⟨.count 2, 1163409733886400⟩, ⟨.count 3, 219289121251200⟩, ⟨.count 4, 43968204680400⟩, ⟨.count 5, 9750271330800⟩, ⟨.count 6, 2417857041600⟩, ⟨.count 7, 665112848400⟩, ⟨.count 8, 226421395200⟩, ⟨.count 9, 100345845600⟩, ⟨.count 10, 100345845600⟩, ⟨.path 12, 28829250450⟩, ⟨.privateRow 10 3, 2238484248⟩, ⟨.privateRow 11 1, 233906400⟩, ⟨.privateRow 11 3, 4764760000⟩, ⟨.privateRow 12 0, 2572970400⟩, ⟨.hall 12 1, 4043239200⟩, ⟨.hall 9 4, 220711680⟩, ⟨.hall 8 5, 291121600⟩, ⟨.hall 7 7, 287534940⟩, ⟨.hall 6 10, 501029100⟩, ⟨.hall 4 15, 39453789375⟩]
  caps := #[0, 0, 1800252253800, 0, 92563420950, 1427025600, 15974758800, 3357654300, 605855250, 362605320, 0, 0, 526576050, 0, 0, 0, 0, 0, 0, 0] }

theorem case_41_22_11_checked :
    (Witness.linear .positive case_41_22_11).check 41 22 11 = true := by
  change case_41_22_11.check 41 22 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_22_12 : Certificate := {
  objectiveScale := 2686068000000
  eta := 158298782501059200
  rows := #[⟨.count 2, 37554365818569600⟩, ⟨.count 3, 8696506157539200⟩, ⟨.count 4, 2146163497077600⟩, ⟨.count 5, 570912113772000⟩, ⟨.count 6, 156792772936800⟩, ⟨.count 7, 51086327292000⟩, ⟨.count 8, 18642028204800⟩, ⟨.count 9, 8212921516800⟩, ⟨.count 10, 4986416635200⟩, ⟨.count 11, 4660507051200⟩, ⟨.path 12, 895412618100⟩, ⟨.privateRow 3 19, 83889126921600⟩, ⟨.privateRow 6 12, 13415602440240⟩, ⟨.privateRow 7 10, 7464493436400⟩, ⟨.privateRow 7 11, 16286167497600⟩, ⟨.privateRow 8 7, 520946100675⟩, ⟨.privateRow 8 8, 3226504881600⟩, ⟨.privateRow 8 9, 8096137249200⟩, ⟨.privateRow 8 10, 11113516814400⟩, ⟨.privateRow 9 5, 452652200000⟩, ⟨.privateRow 9 6, 1747690144200⟩, ⟨.privateRow 9 7, 3706057555200⟩, ⟨.privateRow 9 8, 5654531282400⟩, ⟨.privateRow 9 9, 1994566654080⟩, ⟨.privateRow 10 3, 313850929392⟩, ⟨.privateRow 10 4, 1049428860480⟩, ⟨.privateRow 10 5, 2001899619720⟩, ⟨.privateRow 10 6, 536354058240⟩, ⟨.privateRow 11 1, 234062337600⟩, ⟨.privateRow 11 2, 736555659840⟩, ⟨.privateRow 11 3, 21727305600⟩, ⟨.privateRow 12 0, 321835714200⟩, ⟨.privateRow 13 0, 268875406800⟩, ⟨.hall 7 10, 8201460960⟩, ⟨.hall 6 11, 83131885980⟩, ⟨.hall 7 11, 135028638360⟩, ⟨.hall 6 12, 223605567900⟩, ⟨.hall 5 14, 3836922349260⟩, ⟨.hall 4 15, 4809003599400⟩, ⟨.hall 3 18, 534241281974400⟩, ⟨.assumptionRow 12, 5005198006380⟩]
  caps := #[0, 0, 122099165622720, 19310192736120, 1236471813720, 2266113632640, 0, 473469256260, 116752917600, 11167413400, 290045550168, 110628617580, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_41_22_12_checked :
    (Witness.linear .conditional case_41_22_12).check 41 22 12 = true := by
  change case_41_22_12.check 41 22 12 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_22_13 : Certificate := {
  objectiveScale := 32558400000
  eta := 816775044845760
  rows := #[⟨.count 2, 211756493108160⟩, ⟨.count 3, 59230807796160⟩, ⟨.count 4, 17159139597600⟩, ⟨.count 5, 5211294248160⟩, ⟨.count 6, 1661440500720⟩, ⟨.count 7, 571971319920⟩, ⟨.count 8, 211841229600⟩, ⟨.count 9, 87995587680⟩, ⟨.count 10, 39997994400⟩, ⟨.count 11, 32590958400⟩, ⟨.count 12, 29331862560⟩, ⟨.count 14, 42368245920⟩, ⟨.path 10, 3245402160⟩, ⟨.path 11, 3057114060⟩, ⟨.privateRow 6 12, 124683695136⟩, ⟨.privateRow 7 10, 50748778080⟩, ⟨.privateRow 7 11, 209094277392⟩, ⟨.privateRow 8 8, 19729169460⟩, ⟨.privateRow 8 9, 88470872490⟩, ⟨.privateRow 8 10, 177457768488⟩, ⟨.privateRow 9 6, 7295930460⟩, ⟨.privateRow 9 7, 38770542720⟩, ⟨.privateRow 9 8, 83551366080⟩, ⟨.privateRow 9 9, 119875470624⟩, ⟨.privateRow 10 4, 2310995232⟩, ⟨.privateRow 10 5, 17932434156⟩, ⟨.privateRow 10 6, 41597914176⟩, ⟨.privateRow 10 7, 61952449104⟩, ⟨.privateRow 11 3, 9217644800⟩, ⟨.privateRow 11 4, 22517389440⟩, ⟨.privateRow 11 5, 6010280640⟩, ⟨.privateRow 12 1, 4073869800⟩, ⟨.privateRow 12 2, 5567622060⟩, ⟨.privateRow 13 0, 1955457504⟩, ⟨.hall 7 11, 3800786220⟩, ⟨.hall 7 12, 5497485840⟩, ⟨.hall 6 13, 43022143593⟩, ⟨.hall 8 13, 394816181760⟩, ⟨.hall 5 14, 68900321490⟩, ⟨.hall 4 15, 86164343265⟩, ⟨.hall 3 17, 688298170560⟩, ⟨.hall 2 19, 7994888005104⟩, ⟨.assumptionRow 13, 29500352280⟩]
  caps := #[0, 5065067962080, 0, 0, 21294393120, 0, 13378725360, 0, 753774840, 568163232, 0, 1237461260, 168489720, 222862248, 0, 0, 0, 0, 0, 0] }

theorem case_41_22_13_checked :
    (Witness.linear .conditional case_41_22_13).check 41 22 13 = true := by
  change case_41_22_13.check 41 22 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_22_14 : Certificate := {
  objectiveScale := 217854000000
  eta := 4991403051835200
  rows := #[⟨.count 2, 1382899546828800⟩, ⟨.count 3, 388940497545600⟩, ⟨.count 4, 112805454762000⟩, ⟨.count 5, 33682755506400⟩, ⟨.count 6, 10395351766800⟩, ⟨.count 7, 3275391319200⟩, ⟨.count 8, 1042910668800⟩, ⟨.count 9, 386647279200⟩, ⟨.count 10, 133326648000⟩, ⟨.count 11, 81477396000⟩, ⟨.count 12, 73329656400⟩, ⟨.count 13, 90789098400⟩, ⟨.count 15, 317761844400⟩, ⟨.path 10, 56554898400⟩, ⟨.privateRow 6 12, 546247742040⟩, ⟨.privateRow 7 10, 168774606000⟩, ⟨.privateRow 7 11, 1258476579360⟩, ⟨.privateRow 8 8, 40447707300⟩, ⟨.privateRow 8 9, 459668309100⟩, ⟨.privateRow 8 10, 1225420035840⟩, ⟨.privateRow 9 6, 1296231300⟩, ⟨.privateRow 9 7, 161685014400⟩, ⟨.privateRow 9 8, 522936741600⟩, ⟨.privateRow 9 9, 964988650080⟩, ⟨.privateRow 9 10, 107402022000⟩, ⟨.privateRow 10 5, 41664577500⟩, ⟨.privateRow 10 6, 222084102240⟩, ⟨.privateRow 10 7, 479753721720⟩, ⟨.privateRow 10 8, 701564821776⟩, ⟨.privateRow 11 3, 6090229600⟩, ⟨.privateRow 11 4, 85366089900⟩, ⟨.privateRow 11 5, 244008928800⟩, ⟨.privateRow 11 6, 287146095600⟩, ⟨.privateRow 12 2, 23764240500⟩, ⟨.privateRow 12 3, 123743795175⟩, ⟨.privateRow 12 4, 55870214400⟩, ⟨.privateRow 13 1, 55482226800⟩, ⟨.privateRow 14 0, 12609597000⟩, ⟨.hall 8 10, 27568825200⟩, ⟨.hall 7 11, 57419180280⟩, ⟨.hall 7 12, 3491888400⟩, ⟨.hall 9 12, 992770732800⟩, ⟨.hall 6 13, 396310626855⟩, ⟨.hall 5 14, 571192491870⟩, ⟨.hall 4 15, 677190989475⟩, ⟨.hall 3 17, 5448407764800⟩, ⟨.hall 2 19, 69144977341440⟩, ⟨.assumptionRow 14, 81721584000⟩]
  caps := #[0, 23630951836800, 683563608000, 650295434880, 59212717200, 52960307400, 0, 29284790535, 8978489520, 10071031320, 5929329924, 5053547800, 8391927600, 0, 18371955000, 0, 0, 0, 0, 0] }

theorem case_41_22_14_checked :
    (Witness.linear .conditional case_41_22_14).check 41 22 14 = true := by
  change case_41_22_14.check 41 22 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_23_1_checked :
    (Witness.rising).check 41 23 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_23_2_checked :
    (Witness.rising).check 41 23 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_23_3_checked :
    (Witness.rising).check 41 23 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_23_4_checked :
    (Witness.rising).check 41 23 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_23_5_checked :
    (Witness.rising).check 41 23 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_23_6_checked :
    (Witness.rising).check 41 23 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_23_7_checked :
    (Witness.rising).check 41 23 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_23_8_checked :
    (Witness.rising).check 41 23 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_23_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_41_23_9_checked :
    (Witness.linear .positive case_41_23_9).check 41 23 9 = true := by
  change case_41_23_9.check 41 23 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_23_10 : Certificate := {
  objectiveScale := 300600300000
  eta := 10537406442763200
  rows := #[⟨.count 2, 1910807890992000⟩, ⟨.count 3, 307593465379200⟩, ⟨.count 4, 56858186024640⟩, ⟨.count 5, 11817714308400⟩, ⟨.count 6, 2842397157600⟩, ⟨.count 7, 851438788200⟩, ⟨.count 8, 325909584000⟩, ⟨.count 9, 293318625600⟩, ⟨.path 10, 41379778440⟩, ⟨.path 11, 67030563600⟩, ⟨.privateRow 5 13, 260766465960⟩, ⟨.privateRow 5 14, 938759277456⟩, ⟨.privateRow 5 15, 1131837426720⟩, ⟨.privateRow 5 16, 621400940160⟩, ⟨.privateRow 6 10, 113631868350⟩, ⟨.privateRow 6 11, 309115263600⟩, ⟨.privateRow 6 12, 428920291800⟩, ⟨.privateRow 6 13, 524947222800⟩, ⟨.privateRow 6 14, 560157097500⟩, ⟨.privateRow 7 7, 34569695160⟩, ⟨.privateRow 7 8, 110964453600⟩, ⟨.privateRow 7 9, 162445558275⟩, ⟨.privateRow 7 10, 196626573000⟩, ⟨.privateRow 7 11, 128035908000⟩, ⟨.privateRow 8 4, 7808250450⟩, ⟨.privateRow 8 5, 42960808800⟩, ⟨.privateRow 8 6, 65996690760⟩, ⟨.privateRow 8 7, 42096654600⟩, ⟨.privateRow 9 2, 19053175680⟩, ⟨.privateRow 9 3, 15209113920⟩, ⟨.privateRow 10 0, 8846117280⟩, ⟨.privateRow 11 0, 5013993600⟩, ⟨.privateRow 12 0, 7468761300⟩, ⟨.hall 12 3, 1008767760⟩, ⟨.hall 4 17, 297073256480⟩, ⟨.hall 5 17, 573316343600⟩, ⟨.hall 3 18, 809456487840⟩]
  caps := #[0, 0, 0, 828145237920, 238810620048, 170301235104, 42080974650, 0, 37052321670, 7281674400, 0, 27545364000, 5334829500, 0, 0, 0, 0, 0, 0] }

theorem case_41_23_10_checked :
    (Witness.linear .positive case_41_23_10).check 41 23 10 = true := by
  change case_41_23_10.check 41 23 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_23_11 : Certificate := {
  objectiveScale := 466237200000
  eta := 25289775462631680
  rows := #[⟨.count 2, 5271965576317440⟩, ⟨.count 3, 1003174142770800⟩, ⟨.count 4, 203570947996416⟩, ⟨.count 5, 45206918396640⟩, ⟨.count 6, 11400317248320⟩, ⟨.count 7, 3136879746000⟩, ⟨.count 8, 1095056202240⟩, ⟨.count 9, 492775291008⟩, ⟨.count 10, 456273417600⟩, ⟨.path 12, 134496281920⟩, ⟨.privateRow 9 7, 12547518984⟩, ⟨.privateRow 11 2, 15554775600⟩, ⟨.privateRow 12 0, 11950018080⟩, ⟨.privateRow 12 9, 11950018080⟩, ⟨.hall 10 3, 279188280⟩, ⟨.hall 12 3, 1520911392⟩, ⟨.hall 9 4, 1330987392⟩, ⟨.hall 8 6, 1120298368⟩, ⟨.hall 7 7, 1357608406⟩, ⟨.hall 6 10, 2637086760⟩, ⟨.hall 5 13, 16579394832⟩, ⟨.hall 7 13, 970938969⟩, ⟨.hall 4 15, 69775341636⟩, ⟨.hall 3 18, 2639931954660⟩]
  caps := #[0, 13493277557760, 532629377280, 803171283200, 305627809344, 73586953440, 0, 1283945520, 71720649000, 0, 37332975360, 22914482600, 0, 0, 0, 0, 0, 0, 0] }

theorem case_41_23_11_checked :
    (Witness.linear .positive case_41_23_11).check 41 23 11 = true := by
  change case_41_23_11.check 41 23 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_23_12 : Certificate := {
  objectiveScale := 217255500000
  eta := 20440983926563200
  rows := #[⟨.count 2, 4380876628128000⟩, ⟨.count 3, 1055604847096800⟩, ⟨.count 4, 248871076534080⟩, ⟨.count 5, 67244458881600⟩, ⟨.count 6, 18744456931200⟩, ⟨.count 7, 5467133271600⟩, ⟨.count 8, 1955457504000⟩, ⟨.count 9, 821292151680⟩, ⟨.count 10, 456273417600⟩, ⟨.count 11, 448125678000⟩, ⟨.path 12, 86905418600⟩, ⟨.privateRow 3 20, 114182422754400⟩, ⟨.privateRow 6 12, 883447765200⟩, ⟨.privateRow 6 17, 113311778580000⟩, ⟨.privateRow 7 10, 682248481200⟩, ⟨.privateRow 7 11, 1299564466200⟩, ⟨.privateRow 7 12, 2366103579840⟩, ⟨.privateRow 7 15, 5819232018600⟩, ⟨.privateRow 8 10, 4092881192400⟩, ⟨.privateRow 9 5, 21510032544⟩, ⟨.privateRow 9 10, 512329866048⟩, ⟨.privateRow 9 11, 1028244737520⟩, ⟨.privateRow 9 12, 1008146979840⟩, ⟨.privateRow 10 3, 24295078080⟩, ⟨.privateRow 10 4, 91906502688⟩, ⟨.privateRow 10 9, 430200650880⟩, ⟨.privateRow 11 1, 22406283900⟩, ⟨.privateRow 11 2, 1481407200⟩, ⟨.privateRow 11 8, 89625135600⟩, ⟨.privateRow 11 9, 50923372500⟩, ⟨.privateRow 12 2, 25607181600⟩, ⟨.privateRow 12 6, 4267863600⟩, ⟨.privateRow 13 0, 18623404800⟩, ⟨.hall 7 10, 677112975⟩, ⟨.hall 10 11, 2924829600⟩, ⟨.hall 6 12, 4593402000⟩, ⟨.hall 5 14, 16998231250⟩, ⟨.hall 4 16, 919275797440⟩, ⟨.hall 3 18, 7883002387260⟩, ⟨.assumptionRow 12, 477962100000⟩]
  caps := #[0, 0, 1493752260000, 1782544363600, 87064417440, 167450883600, 172137165200, 7885570000, 0, 90534700256, 21998716040, 0, 0, 12398047200, 0, 0, 0, 0, 0] }

theorem case_41_23_12_checked :
    (Witness.linear .conditional case_41_23_12).check 41 23 12 = true := by
  change case_41_23_12.check 41 23 12 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_23_13 : Certificate := {
  objectiveScale := 65286375000
  eta := 3406830654427200
  rows := #[⟨.count 2, 862193804472000⟩, ⟨.count 3, 218461268025000⟩, ⟨.count 4, 56159109966960⟩, ⟨.count 5, 16228551339000⟩, ⟨.count 6, 4916578867200⟩, ⟨.count 7, 1568439873000⟩, ⟨.count 8, 537750813600⟩, ⟨.count 9, 205323037920⟩, ⟨.count 10, 81477396000⟩, ⟨.count 11, 67218851700⟩, ⟨.count 12, 76821544800⟩, ⟨.path 10, 18628630020⟩, ⟨.privateRow 2 21, 2330253525600⟩, ⟨.privateRow 4 17, 5786796255240⟩, ⟨.privateRow 5 15, 2671469220420⟩, ⟨.privateRow 5 16, 6108593170680⟩, ⟨.privateRow 6 12, 118433214900⟩, ⟨.privateRow 6 13, 1011483673200⟩, ⟨.privateRow 6 14, 2571921301950⟩, ⟨.privateRow 6 15, 3770657490600⟩, ⟨.privateRow 7 10, 84137882400⟩, ⟨.privateRow 7 11, 426786360000⟩, ⟨.privateRow 7 12, 1055656061460⟩, ⟨.privateRow 7 13, 1655664335325⟩, ⟨.privateRow 7 14, 1820243825400⟩, ⟨.privateRow 8 8, 43284866625⟩, ⟨.privateRow 8 9, 191180889900⟩, ⟨.privateRow 8 10, 467476559550⟩, ⟨.privateRow 8 11, 424904620140⟩, ⟨.privateRow 8 12, 1524645772650⟩, ⟨.privateRow 9 6, 19192453280⟩, ⟨.privateRow 9 7, 89421442110⟩, ⟨.privateRow 9 8, 223480857600⟩, ⟨.privateRow 9 9, 370450560480⟩, ⟨.privateRow 9 10, 228462618384⟩, ⟨.privateRow 10 4, 7332965640⟩, ⟨.privateRow 10 5, 43997793840⟩, ⟨.privateRow 10 6, 115901595810⟩, ⟨.privateRow 10 7, 136649232720⟩, ⟨.privateRow 11 2, 925879500⟩, ⟨.privateRow 11 3, 23628444840⟩, ⟨.privateRow 11 4, 62239677500⟩, ⟨.privateRow 12 1, 10475665200⟩, ⟨.privateRow 12 2, 10242872640⟩, ⟨.privateRow 13 0, 4073869800⟩, ⟨.hall 6 16, 3045748305600⟩, ⟨.hall 5 17, 10888387009500⟩, ⟨.hall 4 18, 24381810573120⟩, ⟨.hall 3 19, 41988255714405⟩, ⟨.hall 2 20, 43498065811200⟩, ⟨.assumptionRow 13, 65415631050⟩]
  caps := #[0, 9706099256700, 1750406057400, 173882769060, 0, 57425227860, 0, 13925462265, 5998447455, 5675732062, 2770191480, 0, 26469444540, 0, 65286375000, 0, 0, 0, 0] }

theorem case_41_23_13_checked :
    (Witness.linear .conditional case_41_23_13).check 41 23 13 = true := by
  change case_41_23_13.check 41 23 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_23_14 : Certificate := {
  objectiveScale := 22346848540800000
  eta := 761313195880824787200
  rows := #[⟨.count 2, 193755579263787340800⟩, ⟨.count 3, 50381020315642816800⟩, ⟨.count 4, 14120394809554313280⟩, ⟨.count 5, 4047454822895827200⟩, ⟨.count 6, 1190132497551254400⟩, ⟨.count 7, 355909876641118800⟩, ⟨.count 8, 124628374312041600⟩, ⟨.count 9, 46016630515215360⟩, ⟨.count 10, 15977996706672000⟩, ⟨.count 11, 13181847283004400⟩, ⟨.count 12, 15064968323433600⟩, ⟨.count 13, 16320382350386400⟩, ⟨.path 9, 3711603605149440⟩, ⟨.path 10, 2871646223674800⟩, ⟨.privateRow 2 21, 16450945409189491200⟩, ⟨.privateRow 4 17, 2654238182917841520⟩, ⟨.privateRow 5 14, 43738624699035552⟩, ⟨.privateRow 5 15, 919653545444273640⟩, ⟨.privateRow 5 16, 2451321429028037280⟩, ⟨.privateRow 6 12, 23434395169785600⟩, ⟨.privateRow 6 13, 328667392256243040⟩, ⟨.privateRow 6 14, 934969596573097800⟩, ⟨.privateRow 6 15, 1601908298391772800⟩, ⟨.privateRow 7 10, 6904777148240400⟩, ⟨.privateRow 7 11, 118636625547039600⟩, ⟨.privateRow 7 12, 366204271662131760⟩, ⟨.privateRow 7 13, 673058845200069900⟩, ⟨.privateRow 7 14, 888414659740264800⟩, ⟨.privateRow 8 9, 41999305628966400⟩, ⟨.privateRow 8 10, 147330444632771400⟩, ⟨.privateRow 8 11, 295672829056965360⟩, ⟨.privateRow 8 12, 422118700494390900⟩, ⟨.privateRow 8 13, 424482112507252800⟩, ⟨.privateRow 9 7, 11703882587637240⟩, ⟨.privateRow 9 8, 60396827551220160⟩, ⟨.privateRow 9 9, 136558611853023360⟩, ⟨.privateRow 9 10, 213849507922098048⟩, ⟨.privateRow 9 11, 163694576259854640⟩, ⟨.privateRow 10 5, 2805026088504640⟩, ⟨.privateRow 10 6, 22848535290540960⟩, ⟨.privateRow 10 7, 66194557784784000⟩, ⟨.privateRow 10 8, 116852415914794560⟩, ⟨.privateRow 10 9, 9331150076696448⟩, ⟨.privateRow 11 4, 8432831595188000⟩, ⟨.privateRow 11 5, 31506612255968850⟩, ⟨.privateRow 11 6, 37548292260679200⟩, ⟨.privateRow 12 2, 1443726130995720⟩, ⟨.privateRow 12 3, 15832165784349200⟩, ⟨.privateRow 12 4, 6904777148240400⟩, ⟨.privateRow 13 1, 6151528732068720⟩, ⟨.privateRow 14 0, 1305630588030912⟩, ⟨.hall 6 15, 37634727852107100⟩, ⟨.hall 7 15, 323229880252003725⟩, ⟨.hall 6 16, 1565427443726203200⟩, ⟨.hall 5 17, 5528982865147570400⟩, ⟨.hall 4 18, 10955271394569902400⟩, ⟨.hall 3 19, 18353085972127026120⟩, ⟨.hall 2 20, 23501350584556416000⟩, ⟨.assumptionRow 14, 12276683527265850⟩]
  caps := #[0, 0, 0, 0, 0, 6641152060502388, 5521654131493500, 0, 0, 2174131590004374, 1376851558000350, 2973682720408400, 0, 0, 683020119208326, 22346848540800000, 0, 0, 0] }

theorem case_41_23_14_checked :
    (Witness.linear .conditional case_41_23_14).check 41 23 14 = true := by
  change case_41_23_14.check 41 23 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_24_1_checked :
    (Witness.rising).check 41 24 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_24_2_checked :
    (Witness.rising).check 41 24 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_24_3_checked :
    (Witness.rising).check 41 24 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_24_4_checked :
    (Witness.rising).check 41 24 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_24_5_checked :
    (Witness.rising).check 41 24 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_24_6_checked :
    (Witness.rising).check 41 24 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_24_7_checked :
    (Witness.rising).check 41 24 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_24_8_checked :
    (Witness.rising).check 41 24 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_24_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_41_24_9_checked :
    (Witness.linear .positive case_41_24_9).check 41 24 9 = true := by
  change case_41_24_9.check 41 24 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_24_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_41_24_10_checked :
    (Witness.linear .positive case_41_24_10).check 41 24 10 = true := by
  change case_41_24_10.check 41 24 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_24_11 : Certificate := {
  objectiveScale := 4129125000
  eta := 337886761212000
  rows := #[⟨.count 2, 74276831128500⟩, ⟨.count 3, 15787467635940⟩, ⟨.count 4, 3578603628600⟩, ⟨.count 5, 819429811200⟩, ⟨.count 6, 198455657400⟩, ⟨.count 7, 50923372500⟩, ⟨.count 8, 14665931280⟩, ⟨.count 9, 4888643760⟩, ⟨.count 10, 4073869800⟩, ⟨.path 11, 1474659186⟩, ⟨.privateRow 11 5, 64664600⟩, ⟨.privateRow 13 1, 116396280⟩, ⟨.hall 11 1, 123111450⟩, ⟨.hall 12 1, 213393180⟩, ⟨.hall 13 6, 36027420⟩, ⟨.hall 11 7, 1243550⟩, ⟨.hall 10 8, 1808800⟩, ⟨.hall 11 10, 14922600⟩, ⟨.hall 12 10, 145495350⟩, ⟨.hall 6 11, 46267375⟩]
  caps := #[0, 0, 24967002060, 0, 6179483310, 0, 94342248, 689699010, 80660580, 715140426, 55255200, 1193077886, 671517000, 9699690, 0, 0, 0, 0] }

theorem case_41_24_11_checked :
    (Witness.linear .positive case_41_24_11).check 41 24 11 = true := by
  change case_41_24_11.check 41 24 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_24_12 : Certificate := {
  objectiveScale := 786500000
  eta := 66578672160000
  rows := #[⟨.count 2, 16145327998800⟩, ⟨.count 3, 4244390350200⟩, ⟨.count 4, 1122326187840⟩, ⟨.count 5, 299969841600⟩, ⟨.count 6, 80479713600⟩, ⟨.count 7, 23279256000⟩, ⟨.count 8, 7449361920⟩, ⟨.count 9, 2793510720⟩, ⟨.count 10, 1163962800⟩, ⟨.count 11, 914542200⟩, ⟨.path 11, 174777603⟩, ⟨.hall 12 4, 1478048⟩, ⟨.hall 8 7, 15845088⟩, ⟨.hall 11 9, 3517470⟩, ⟨.hall 7 10, 11409975⟩]
  caps := #[0, 205376709538, 277411134, 4453178730, 2367687465, 0, 267538986, 0, 0, 0, 0, 46735403, 343354000, 0, 0, 0, 0, 0] }

theorem case_41_24_12_checked :
    (Witness.linear .positive case_41_24_12).check 41 24 12 = true := by
  change case_41_24_12.check 41 24 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_24_13 : Certificate := {
  objectiveScale := 5840441673000000
  eta := 532785507595148808000
  rows := #[⟨.count 2, 118608202286062889400⟩, ⟨.count 3, 29683763994586862160⟩, ⟨.count 4, 7466245888748343840⟩, ⟨.count 5, 1895835401175830400⟩, ⟨.count 6, 543658681219539600⟩, ⟨.count 7, 164111420088415800⟩, ⟨.count 8, 53225325434080800⟩, ⟨.count 9, 17741775144693600⟩, ⟨.count 10, 8870887572346800⟩, ⟨.count 11, 6969983092558200⟩, ⟨.path 9, 1308043935198000⟩, ⟨.path 10, 1242728564397606⟩, ⟨.privateRow 2 22, 5708416152805165800⟩, ⟨.privateRow 4 17, 351112898287619325⟩, ⟨.privateRow 4 18, 1416532897177578180⟩, ⟨.privateRow 5 15, 245343404858048640⟩, ⟨.privateRow 5 16, 570841615280516580⟩, ⟨.privateRow 5 17, 1117985288046335280⟩, ⟨.privateRow 6 13, 124104421175827950⟩, ⟨.privateRow 6 14, 248363730864823860⟩, ⟨.privateRow 6 15, 459728468146651275⟩, ⟨.privateRow 6 16, 574636383853131600⟩, ⟨.privateRow 7 10, 4831465552796025⟩, ⟨.privateRow 7 11, 51324420954292200⟩, ⟨.privateRow 7 12, 113209422351854400⟩, ⟨.privateRow 7 13, 204157141129295640⟩, ⟨.privateRow 7 14, 256622104771461000⟩, ⟨.privateRow 7 15, 214379782998381000⟩, ⟨.privateRow 8 8, 3991899407556060⟩, ⟨.privateRow 8 9, 22953421593447345⟩, ⟨.privateRow 8 10, 50880876575674860⟩, ⟨.privateRow 8 11, 98762548305461040⟩, ⟨.privateRow 8 12, 127474654414623516⟩, ⟨.privateRow 8 13, 2217721893086700⟩, ⟨.privateRow 9 6, 2247291518327856⟩, ⟨.privateRow 9 7, 11345974722162080⟩, ⟨.privateRow 9 8, 24937050620041560⟩, ⟨.privateRow 9 9, 49958585883629280⟩, ⟨.privateRow 9 10, 18201747092889360⟩, ⟨.privateRow 10 4, 1008055405948500⟩, ⟨.privateRow 10 5, 6120912424919292⟩, ⟨.privateRow 10 6, 13897723863343320⟩, ⟨.privateRow 10 7, 12197470411976850⟩, ⟨.privateRow 11 2, 211211608865400⟩, ⟨.privateRow 11 3, 3628999461414600⟩, ⟨.privateRow 11 4, 5195805578088840⟩, ⟨.privateRow 12 1, 1936106414599500⟩, ⟨.privateRow 12 2, 105605804432700⟩, ⟨.privateRow 13 0, 464665539503880⟩, ⟨.privateRow 14 0, 823725274575060⟩, ⟨.hall 5 17, 10067753355917400⟩, ⟨.hall 5 18, 760828680735037200⟩, ⟨.hall 4 19, 2968376399458686216⟩, ⟨.hall 3 20, 6433294394431218600⟩, ⟨.hall 2 21, 9888821921273595300⟩, ⟨.assumptionRow 13, 6301369329833160⟩]
  caps := #[0, 2532292394246972280, 0, 6827038021051248, 36984821904963075, 28687618038441648, 3522990913073775, 8965880534114790, 773982246569730, 1600849364594304, 2787824938815384, 0, 4365262915233660, 21435121792910760, 0, 0, 0, 0] }

theorem case_41_24_13_checked :
    (Witness.linear .conditional case_41_24_13).check 41 24 13 = true := by
  change case_41_24_13.check 41 24 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_24_14 : Certificate := {
  objectiveScale := 60091049402559000000
  eta := 7687384493921203767696000
  rows := #[⟨.count 2, 1579256162338160339233200⟩, ⟨.count 3, 359301666563708436968400⟩, ⟨.count 4, 80454924672405145022160⟩, ⟨.count 5, 17721753551442813272400⟩, ⟨.count 6, 4177926355391958569400⟩, ⟨.count 7, 964136851244298131400⟩, ⟨.count 8, 257103160331812835040⟩, ⟨.count 9, 93492058302477394560⟩, ⟨.count 10, 58432536439048371600⟩, ⟨.count 11, 45911278630680863400⟩, ⟨.path 8, 72081785845441008000⟩, ⟨.path 9, 686236890357018000⟩, ⟨.privateRow 2 22, 73113711219359274964500⟩, ⟨.privateRow 4 17, 4207768686501901130610⟩, ⟨.privateRow 4 18, 17248867381546800379380⟩, ⟨.privateRow 5 15, 2681218672031762422560⟩, ⟨.privateRow 5 16, 6652544273585657106660⟩, ⟨.privateRow 5 17, 14195767352606522963280⟩, ⟨.privateRow 6 13, 1205171064055372664250⟩, ⟨.privateRow 6 14, 2736312206388579458640⟩, ⟨.privateRow 6 15, 5673868850774976701850⟩, ⟨.privateRow 6 16, 8113543184677545915300⟩, ⟨.privateRow 7 10, 21390482089294493175⟩, ⟨.privateRow 7 11, 444802777382960053200⟩, ⟨.privateRow 7 12, 1151955718369810754400⟩, ⟨.privateRow 7 13, 2426619763261623089160⟩, ⟨.privateRow 7 14, 3581079733193107345200⟩, ⟨.privateRow 7 15, 3935848704430186744200⟩, ⟨.privateRow 8 8, 7141754453661467640⟩, ⟨.privateRow 8 9, 166532728851287859060⟩, ⟨.privateRow 8 10, 474555670937128560780⟩, ⟨.privateRow 8 11, 1107783503323625378250⟩, ⟨.privateRow 8 12, 1729603078595831799360⟩, ⟨.privateRow 8 13, 1877875639809917042295⟩, ⟨.privateRow 9 7, 56556924158288794240⟩, ⟨.privateRow 9 8, 204513877536669300600⟩, ⟨.privateRow 9 9, 366177228351369795360⟩, ⟨.privateRow 9 10, 1235307103681807796640⟩, ⟨.privateRow 9 11, 218148136039113920640⟩, ⟨.privateRow 10 5, 12562995334395399894⟩, ⟨.privateRow 10 6, 86999554253694242160⟩, ⟨.privateRow 10 7, 266598447503158195425⟩, ⟨.privateRow 10 8, 388993742579950588080⟩, ⟨.privateRow 11 4, 30885769260639853560⟩, ⟨.privateRow 11 5, 140516337627235369800⟩, ⟨.privateRow 11 6, 82953332980434741825⟩, ⟨.privateRow 12 2, 3478127168990974500⟩, ⟨.privateRow 12 3, 68101729968843280710⟩, ⟨.privateRow 12 4, 2550626590593381300⟩, ⟨.privateRow 13 1, 18364511452272345360⟩, ⟨.privateRow 14 0, 5425878383625920220⟩, ⟨.hall 6 17, 3047998775759090653500⟩, ⟨.hall 5 18, 16972674794836967606400⟩, ⟨.hall 4 19, 43390749433856483999340⟩, ⟨.hall 3 20, 86264231795140630271040⟩, ⟨.hall 2 21, 128376282556589272405200⟩, ⟨.assumptionRow 14, 39105760623501841500⟩]
  caps := #[0, 0, 0, 0, 0, 0, 0, 11889032343881764110, 0, 16297950874326441320, 0, 0, 61005930860582055810, 85936216109440832520, 0, 60091049402559000000, 0, 0] }

theorem case_41_24_14_checked :
    (Witness.linear .conditional case_41_24_14).check 41 24 14 = true := by
  change case_41_24_14.check 41 24 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_24_15 : Certificate := {
  objectiveScale := 779896498689000000
  eta := 149717948739699682742400
  rows := #[⟨.count 2, 30217754781460087241400⟩, ⟨.count 3, 6687242774121936466440⟩, ⟨.count 4, 1420208931402519738480⟩, ⟨.count 5, 301280256615550212000⟩, ⟨.count 6, 62875879641506131200⟩, ⟨.count 7, 11670144327400759200⟩, ⟨.count 8, 1667163475342965600⟩, ⟨.path 7, 6354045281083500⟩, ⟨.path 8, 1557336381361924800⟩, ⟨.privateRow 2 22, 1370825167600753464600⟩, ⟨.privateRow 4 17, 79610033025261148410⟩, ⟨.privateRow 4 18, 318156317366551684020⟩, ⟨.privateRow 5 15, 49829134615893608976⟩, ⟨.privateRow 5 16, 119791649858661160380⟩, ⟨.privateRow 5 17, 264951970600457780640⟩, ⟨.privateRow 6 12, 1434667888645477200⟩, ⟨.privateRow 6 13, 20467408737469443750⟩, ⟨.privateRow 6 14, 47942858226648425040⟩, ⟨.privateRow 6 15, 103155740036845996500⟩, ⟨.privateRow 6 16, 157226085608187495900⟩, ⟨.privateRow 7 10, 1324799547370749450⟩, ⟨.privateRow 7 11, 7425682214155147800⟩, ⟨.privateRow 7 12, 19003678900486780500⟩, ⟨.privateRow 7 13, 42703201589856247440⟩, ⟨.privateRow 7 14, 67788057738498797700⟩, ⟨.privateRow 7 15, 82524592029476797200⟩, ⟨.privateRow 8 8, 657603370829725320⟩, ⟨.privateRow 8 9, 2834177908083041520⟩, ⟨.privateRow 8 10, 7454602396890689040⟩, ⟨.privateRow 8 11, 18415209888059174190⟩, ⟨.privateRow 8 12, 31651098579386201916⟩, ⟨.privateRow 8 13, 41679086883574140000⟩, ⟨.privateRow 8 14, 17755291012402583640⟩, ⟨.privateRow 9 6, 233402886548015184⟩, ⟨.privateRow 9 7, 1111442316895310400⟩, ⟨.privateRow 9 8, 3102776467999408200⟩, ⟨.privateRow 9 9, 8224673145025296960⟩, ⟨.privateRow 9 10, 15918323849756167840⟩, ⟨.privateRow 9 11, 19672529009046994080⟩, ⟨.privateRow 10 4, 56835118477601100⟩, ⟨.privateRow 10 5, 412622960147383986⟩, ⟨.privateRow 10 6, 1361516838196755240⟩, ⟨.privateRow 10 7, 3980352797381330370⟩, ⟨.privateRow 10 8, 8562075276939944760⟩, ⟨.privateRow 10 9, 4702790303363282130⟩, ⟨.privateRow 11 2, 14885388172705050⟩, ⟨.privateRow 11 3, 119083105381640400⟩, ⟨.privateRow 11 4, 583507216370037960⟩, ⟨.privateRow 11 5, 2083954344178707000⟩, ⟨.privateRow 11 6, 4205122158789176625⟩, ⟨.privateRow 12 0, 8396885635884900⟩, ⟨.privateRow 12 1, 45483130527709875⟩, ⟨.privateRow 12 2, 178624658072460600⟩, ⟨.privateRow 12 3, 1102511083991687370⟩, ⟨.privateRow 12 4, 1103723967472426300⟩, ⟨.privateRow 13 0, 130991415919804440⟩, ⟨.privateRow 13 1, 357249316144921200⟩, ⟨.privateRow 13 2, 235784548655647992⟩, ⟨.privateRow 14 0, 232212055494198780⟩, ⟨.hall 6 17, 96023985170101088100⟩, ⟨.hall 5 18, 369947335697721381600⟩, ⟨.hall 4 19, 868983954070390674516⟩, ⟨.hall 3 20, 1666560120942365288640⟩, ⟨.hall 2 21, 2443644863983951828200⟩]
  caps := #[0, 0, 18265440505839370200, 0, 763176077641725930, 0, 248729484390319800, 397713992206309740, 0, 0, 411790417412320674, 715097734600198950, 0, 2520944248731766704, 0, 6239171989512000000, 779896498689000000, 0] }

theorem case_41_24_15_checked :
    (Witness.linear .negative case_41_24_15).check 41 24 15 = true := by
  change case_41_24_15.check 41 24 15 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_25_1_checked :
    (Witness.rising).check 41 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_25_2_checked :
    (Witness.rising).check 41 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_25_3_checked :
    (Witness.rising).check 41 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_25_4_checked :
    (Witness.rising).check 41 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_25_5_checked :
    (Witness.rising).check 41 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_25_6_checked :
    (Witness.rising).check 41 25 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_25_7_checked :
    (Witness.rising).check 41 25 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_25_8_checked :
    (Witness.rising).check 41 25 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_25_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_41_25_9_checked :
    (Witness.linear .positive case_41_25_9).check 41 25 9 = true := by
  change case_41_25_9.check 41 25 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_25_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_41_25_10_checked :
    (Witness.linear .positive case_41_25_10).check 41 25 10 = true := by
  change case_41_25_10.check 41 25 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_25_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_41_25_11_checked :
    (Witness.linear .positive case_41_25_11).check 41 25 11 = true := by
  change case_41_25_11.check 41 25 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_25_12 : Certificate := {
  objectiveScale := 96250
  eta := 21285969705
  rows := #[⟨.count 2, 4915802892⟩, ⟨.count 3, 1094125032⟩, ⟨.count 4, 252490392⟩, ⟨.count 5, 60063465⟩, ⟨.count 6, 14244300⟩, ⟨.count 7, 3703518⟩, ⟨.count 8, 1012928⟩, ⟨.count 9, 284886⟩, ⟨.path 9, 84201⟩]
  caps := #[0, 0, 0, 1014832, 365211, 140250, 0, 1610, 0, 0, 96250, 96250, 0, 0, 0, 0, 0] }

theorem case_41_25_12_checked :
    (Witness.linear .positive case_41_25_12).check 41 25 12 = true := by
  change case_41_25_12.check 41 25 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_25_13 : Certificate := {
  objectiveScale := 634388139000000
  eta := 158387699732525663400
  rows := #[⟨.count 2, 31250906411872066920⟩, ⟨.count 3, 6308081547788900880⟩, ⟨.count 4, 1413516601009553040⟩, ⟨.count 5, 307668414398845500⟩, ⟨.count 6, 75119041437640200⟩, ⟨.count 7, 19019501981019540⟩, ⟨.count 8, 4972418818567200⟩, ⟨.count 9, 2237588468355240⟩, ⟨.count 10, 1598277477396600⟩, ⟨.path 8, 816305735044800⟩, ⟨.path 9, 184403944244520⟩, ⟨.privateRow 2 23, 1386558987557463720⟩, ⟨.privateRow 3 20, 200619340690548780⟩, ⟨.privateRow 3 21, 818984017375974450⟩, ⟨.privateRow 4 18, 205258785034658355⟩, ⟨.privateRow 4 19, 336970168151116500⟩, ⟨.privateRow 4 20, 536222093666559300⟩, ⟨.privateRow 5 15, 23636748026831940⟩, ⟨.privateRow 5 16, 87788054241803916⟩, ⟨.privateRow 5 17, 145336698611264160⟩, ⟨.privateRow 5 18, 226990919067592680⟩, ⟨.privateRow 5 19, 210679609478828490⟩, ⟨.privateRow 6 13, 18456299441365500⟩, ⟨.privateRow 6 14, 37781503701791850⟩, ⟨.privateRow 6 15, 61427131047942660⟩, ⟨.privateRow 6 16, 60268379876830125⟩, ⟨.privateRow 6 17, 169950171763171800⟩, ⟨.privateRow 7 10, 1065518318264400⟩, ⟨.privateRow 7 11, 9070224684225705⟩, ⟨.privateRow 7 12, 18425856060843660⟩, ⟨.privateRow 7 13, 17527776335449380⟩, ⟨.privateRow 7 14, 63931099095864000⟩, ⟨.privateRow 7 15, 17700923062167345⟩, ⟨.privateRow 8 8, 969621669620604⟩, ⟨.privateRow 8 9, 4447552387718440⟩, ⟨.privateRow 8 10, 9385440520045590⟩, ⟨.privateRow 8 11, 14366738657931660⟩, ⟨.privateRow 8 12, 15414498337558320⟩, ⟨.privateRow 9 6, 610251400460520⟩, ⟨.privateRow 9 7, 2436485221097928⟩, ⟨.privateRow 9 8, 5193415210503520⟩, ⟨.privateRow 9 9, 6153368287976910⟩, ⟨.privateRow 10 4, 332974474457625⟩, ⟨.privateRow 10 5, 1511098705902240⟩, ⟨.privateRow 10 6, 2381433441320934⟩, ⟨.privateRow 11 0, 17758638637740⟩, ⟨.privateRow 11 2, 143435158227900⟩, ⟨.privateRow 11 3, 932328528481350⟩, ⟨.privateRow 12 1, 225398105786700⟩, ⟨.hall 4 20, 134620628667576480⟩, ⟨.hall 3 21, 442563033491118540⟩, ⟨.hall 2 22, 941376168809916840⟩, ⟨.assumptionRow 13, 711769535418942⟩]
  caps := #[0, 544168309010157216, 3128261765428800, 15120208687632048, 2291153263979580, 4879415174520744, 223337711422980, 803390411079828, 191200270876776, 303429752184104, 197886364676091, 0, 260973323845542, 6266499993581058, 634388139000000, 0, 0] }

theorem case_41_25_13_checked :
    (Witness.linear .conditional case_41_25_13).check 41 25 13 = true := by
  change case_41_25_13.check 41 25 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_25_14 : Certificate := {
  objectiveScale := 1874969388600000
  eta := 335973908523539286000
  rows := #[⟨.count 2, 72314384120304646320⟩, ⟨.count 3, 14947410624108482520⟩, ⟨.count 4, 3417756557664889440⟩, ⟨.count 5, 773566299059954400⟩, ⟨.count 6, 175810522513626000⟩, ⟨.count 7, 42514180898749560⟩, ⟨.count 8, 11933805164561280⟩, ⟨.count 9, 4475176936710480⟩, ⟨.path 8, 2667048489705600⟩, ⟨.privateRow 2 23, 7999378774369983000⟩, ⟨.privateRow 3 20, 965004423574791600⟩, ⟨.privateRow 3 21, 2773117975114927440⟩, ⟨.privateRow 4 18, 635555038886757990⟩, ⟨.privateRow 4 19, 1139252185888296480⟩, ⟨.privateRow 4 20, 1926883326749340960⟩, ⟨.privateRow 5 15, 42194525403270240⟩, ⟨.privateRow 5 16, 253167152419621440⟩, ⟨.privateRow 5 17, 472051252949085810⟩, ⟨.privateRow 5 18, 830607046364375280⟩, ⟨.privateRow 5 19, 883740893168493360⟩, ⟨.privateRow 6 13, 30823922778363000⟩, ⟨.privateRow 6 14, 100691481075985800⟩, ⟨.privateRow 6 15, 194137437587773680⟩, ⟨.privateRow 6 16, 352819753135299450⟩, ⟨.privateRow 6 17, 422300426805457200⟩, ⟨.privateRow 6 18, 309000312296676000⟩, ⟨.privateRow 7 11, 15423377656877190⟩, ⟨.privateRow 7 12, 43792802880666840⟩, ⟨.privateRow 7 13, 83536636151928960⟩, ⟨.privateRow 7 14, 157781952568592352⟩, ⟨.privateRow 7 15, 202741498007758710⟩, ⟨.privateRow 7 16, 91314919875259080⟩, ⟨.privateRow 8 9, 6491769013129400⟩, ⟨.privateRow 8 10, 20449072391357610⟩, ⟨.privateRow 8 11, 39708315993986640⟩, ⟨.privateRow 8 12, 76533812982446820⟩, ⟨.privateRow 8 13, 86619535819440624⟩, ⟨.privateRow 9 7, 2411623127005092⟩, ⟨.privateRow 9 8, 9889588539150320⟩, ⟨.privateRow 9 9, 11654106606016875⟩, ⟨.privateRow 9 10, 61125234191101080⟩, ⟨.privateRow 10 5, 755549352951120⟩, ⟨.privateRow 10 6, 4826797981737732⟩, ⟨.privateRow 10 7, 12253460660040600⟩, ⟨.privateRow 10 8, 11827253332734840⟩, ⟨.privateRow 11 3, 88793193188700⟩, ⟨.privateRow 11 4, 2276334589019400⟩, ⟨.privateRow 11 5, 6872593152805380⟩, ⟨.privateRow 12 2, 683707587552990⟩, ⟨.privateRow 12 3, 1917932972875920⟩, ⟨.privateRow 13 1, 586035075045420⟩, ⟨.hall 5 19, 89370348944426550⟩, ⟨.hall 4 20, 683149458910089600⟩, ⟨.hall 3 21, 1797263023332476700⟩, ⟨.hall 2 22, 3598561118209337280⟩, ⟨.assumptionRow 14, 1421410064243400⟩]
  caps := #[0, 659554482601014000, 0, 6186827862295080, 0, 0, 2943056279484750, 0, 0, 1564157921662336, 1421410064243400, 2054097530394000, 2728663392625170, 1421410064243400, 17328283821756600, 1874969388600000, 0] }

theorem case_41_25_14_checked :
    (Witness.linear .conditional case_41_25_14).check 41 25 14 = true := by
  change case_41_25_14.check 41 25 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_25_15 : Certificate := {
  objectiveScale := 67902948858016800000
  eta := 18026211298234322309326200
  rows := #[⟨.count 2, 3571944472194206603695200⟩, ⟨.count 3, 684983056168961653783680⟩, ⟨.count 4, 134920905002977295442240⟩, ⟨.count 5, 24615746967998816229600⟩, ⟨.count 6, 4445349882427304650800⟩, ⟨.count 7, 698554981524290730840⟩, ⟨.count 8, 56448887395902281280⟩, ⟨.path 7, 224913442485195303840⟩, ⟨.path 8, 49739013617102409600⟩, ⟨.privateRow 2 23, 414708807364920597208680⟩, ⟨.privateRow 3 20, 53189972164635279933960⟩, ⟨.privateRow 3 21, 135569563200106993978020⟩, ⟨.privateRow 4 17, 2594632788518794143120⟩, ⟨.privateRow 4 18, 29987967421149909231060⟩, ⟨.privateRow 4 19, 54587082127683861395640⟩, ⟨.privateRow 4 20, 94803890349725170614000⟩, ⟨.privateRow 5 15, 3132409242549398912100⟩, ⟨.privateRow 5 16, 11389772651138911725696⟩, ⟨.privateRow 5 17, 21680152819450308753570⟩, ⟨.privateRow 5 18, 40272249093590856101760⟩, ⟨.privateRow 5 19, 45738719028376178805000⟩, ⟨.privateRow 6 13, 1753947572658392311200⟩, ⟨.privateRow 6 14, 4422669525884308198500⟩, ⟨.privateRow 6 15, 8567126678174526582120⟩, ⟨.privateRow 6 16, 16624701346016399535900⟩, ⟨.privateRow 6 17, 21833623232057918080800⟩, ⟨.privateRow 6 18, 18340848324436464426600⟩, ⟨.privateRow 7 10, 43344681393282108840⟩, ⟨.privateRow 7 11, 708761141968639134375⟩, ⟨.privateRow 7 12, 1868861379142907669520⟩, ⟨.privateRow 7 13, 3565352048559042301560⟩, ⟨.privateRow 7 14, 7190580238391595237192⟩, ⟨.privateRow 7 15, 10256057228742995730060⟩, ⟨.privateRow 7 16, 9419908084191193188600⟩, ⟨.privateRow 8 8, 25401999328156026576⟩, ⟨.privateRow 8 9, 272052276755251272280⟩, ⟨.privateRow 8 10, 808806714719412373965⟩, ⟨.privateRow 8 11, 1641049797866587748640⟩, ⟨.privateRow 8 12, 2502567341218334470080⟩, ⟨.privateRow 8 13, 6970026371209034181048⟩, ⟨.privateRow 8 14, 1414750240359800924580⟩, ⟨.privateRow 9 6, 7697575553986674720⟩, ⟨.privateRow 9 7, 105136052774867998884⟩, ⟨.privateRow 9 8, 361429681798763217640⟩, ⟨.privateRow 9 9, 815862825643900159125⟩, ⟨.privateRow 9 10, 1792252174819897430640⟩, ⟨.privateRow 9 11, 2319108457181652055920⟩, ⟨.privateRow 10 4, 756011884766548410⟩, ⟨.privateRow 10 5, 38762791182575754840⟩, ⟨.privateRow 10 6, 168741852679893605112⟩, ⟨.privateRow 10 7, 437478877318242679920⟩, ⟨.privateRow 10 8, 1068244793175132903330⟩, ⟨.privateRow 10 9, 349925500949088121200⟩, ⟨.privateRow 11 3, 11340178271498226150⟩, ⟨.privateRow 11 4, 78350322603078653400⟩, ⟨.privateRow 11 5, 254019993281560265760⟩, ⟨.privateRow 11 6, 396486232899789832800⟩, ⟨.privateRow 12 1, 5117618912265866160⟩, ⟨.privateRow 12 2, 30492479352250785870⟩, ⟨.privateRow 12 3, 151202376953309682000⟩, ⟨.privateRow 12 4, 53223236687565008064⟩, ⟨.privateRow 13 0, 23029285105196397720⟩, ⟨.privateRow 13 1, 41580653662160162550⟩, ⟨.privateRow 14 0, 36036566507205474210⟩, ⟨.hall 5 19, 8099911333388799664740⟩, ⟨.hall 4 20, 38263705518595843297440⟩, ⟨.hall 3 21, 92935028970582262944480⟩, ⟨.hall 2 22, 181361071580089045685040⟩, ⟨.assumptionRow 15, 16272690201420548280⟩]
  caps := #[0, 0, 0, 1509033983019844585920, 190068137806039705212, 385790891903770291224, 931909615110504030, 0, 30664882186256232343, 25643028954545130752, 0, 7278613112462943240, 44664793024671126714, 1272433358650376815200, 0, 594853849520730651720, 67902948858016800000] }

theorem case_41_25_15_checked :
    (Witness.linear .conditional case_41_25_15).check 41 25 15 = true := by
  change case_41_25_15.check 41 25 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_25_16 : Certificate := {
  objectiveScale := 118569901388400000
  eta := 58173708361312254110400
  rows := #[⟨.count 2, 7810862399914511377440⟩, ⟨.count 3, 1133960136281921108160⟩, ⟨.count 4, 217471806958176650880⟩, ⟨.count 5, 46302376481479918800⟩, ⟨.count 6, 9233318477245262400⟩, ⟨.count 7, 1520781866840396160⟩, ⟨.count 8, 168975762982266240⟩, ⟨.path 3, 160901790204470515200⟩, ⟨.path 8, 189774543486528000⟩, ⟨.privateRow 6 13, 885829573797339600⟩, ⟨.privateRow 7 11, 488822742912984480⟩, ⟨.privateRow 8 9, 190097733355049520⟩, ⟨.privateRow 9 7, 59141517043793184⟩, ⟨.privateRow 9 8, 178363305370169920⟩, ⟨.privateRow 10 5, 9875206927535040⟩, ⟨.privateRow 10 6, 65176365721731264⟩, ⟨.privateRow 10 7, 184062884677111440⟩, ⟨.privateRow 11 4, 8229339106279200⟩, ⟨.privateRow 12 3, 9052273016907120⟩, ⟨.hall 12 3, 4177972161649440⟩, ⟨.hall 10 4, 3481643468041200⟩, ⟨.hall 11 4, 10146503821148640⟩, ⟨.hall 10 5, 5968531659499200⟩, ⟨.hall 9 6, 5676887498864580⟩, ⟨.hall 12 6, 2263068254226780⟩, ⟨.hall 13 6, 2801894029042680⟩, ⟨.hall 8 8, 4203541450576944⟩, ⟨.hall 7 10, 3349995763824045⟩, ⟨.hall 5 14, 21179383955084355⟩, ⟨.hall 6 14, 59157398224524600⟩, ⟨.hall 7 14, 55398579646851441⟩, ⟨.hall 4 17, 32343158929580928⟩]
  caps := #[0, 0, 5373083024093806560, 0, 70979414994069120, 620847672447459600, 18582400629777600, 69868536009352920, 168652573113744720, 0, 188000653163601096, 0, 0, 1240596878226829200, 2396327888489008320, 4149946548594000000, 948559211107200000] }

theorem case_41_25_16_checked :
    (Witness.linear .negative case_41_25_16).check 41 25 16 = true := by
  change case_41_25_16.check 41 25 16 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_26_1_checked :
    (Witness.rising).check 41 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_26_2_checked :
    (Witness.rising).check 41 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_26_3_checked :
    (Witness.rising).check 41 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_26_4_checked :
    (Witness.rising).check 41 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_26_5_checked :
    (Witness.rising).check 41 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_26_6_checked :
    (Witness.rising).check 41 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_26_7_checked :
    (Witness.rising).check 41 26 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_26_8_checked :
    (Witness.rising).check 41 26 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_26_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_41_26_9_checked :
    (Witness.linear .positive case_41_26_9).check 41 26 9 = true := by
  change case_41_26_9.check 41 26 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_26_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_41_26_10_checked :
    (Witness.linear .positive case_41_26_10).check 41 26 10 = true := by
  change case_41_26_10.check 41 26 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_26_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_41_26_11_checked :
    (Witness.linear .positive case_41_26_11).check 41 26 11 = true := by
  change case_41_26_11.check 41 26 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_26_12 : Certificate := {
  objectiveScale := 23249482384880000
  eta := 27909460637200278007872
  rows := #[⟨.count 2, 3477406941060344916624⟩, ⟨.count 3, 491270899784640167808⟩, ⟨.count 4, 82919311474949858832⟩, ⟨.count 5, 15770123901664104000⟩, ⟨.count 6, 3217105275939477216⟩, ⟨.count 7, 662345203869892368⟩, ⟨.count 8, 147187823082198304⟩, ⟨.path 3, 63298079423510389920⟩, ⟨.path 7, 94766572449545269⟩, ⟨.path 8, 29281179768029280⟩]
  caps := #[0, 14475177657897121492, 2427577063955120497, 0, 168289372953205763, 0, 24691798282253074, 0, 0, 46498964769760000, 23249482384880000, 23249482384880000, 0, 0, 0, 0] }

theorem case_41_26_12_checked :
    (Witness.linear .positive case_41_26_12).check 41 26 12 = true := by
  change case_41_26_12.check 41 26 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_26_13 : Certificate := {
  objectiveScale := 10323118921122493200000
  eta := 4747547010355846584728480640
  rows := #[⟨.count 2, 809058911213622899422232640⟩, ⟨.count 3, 151583010021745036753898880⟩, ⟨.count 4, 30193363784819133337158720⟩, ⟨.count 5, 6068548688971068852552000⟩, ⟨.count 6, 1344416940325898330411520⟩, ⟨.count 7, 304983472573930639769280⟩, ⟨.count 8, 87138135021123039934080⟩, ⟨.path 3, 2272434366082666950964800⟩, ⟨.path 7, 15851376634268425059810⟩, ⟨.path 8, 19261160051409660384000⟩, ⟨.privateRow 2 24, 73429439136549933115879200⟩, ⟨.privateRow 3 21, 17390282089215555255415680⟩, ⟨.privateRow 3 22, 25571930552448857826369120⟩, ⟨.privateRow 4 18, 3122034894756808345066752⟩, ⟨.privateRow 4 19, 7843599180495106491923460⟩, ⟨.privateRow 4 20, 10749111370105677854725440⟩, ⟨.privateRow 4 21, 14480490794760196600474080⟩, ⟨.privateRow 5 15, 394789101524271731946240⟩, ⟨.privateRow 5 16, 1941935580470742032816640⟩, ⟨.privateRow 5 17, 3215397182279440173567552⟩, ⟨.privateRow 5 18, 4416036199820485488087840⟩, ⟨.privateRow 5 19, 6093445298977104006818880⟩, ⟨.privateRow 5 20, 4304001454793327293886880⟩, ⟨.privateRow 6 13, 389787550406987883990840⟩, ⟨.privateRow 6 14, 922952899509446076036480⟩, ⟨.privateRow 6 15, 1456451685353056524612480⟩, ⟨.privateRow 6 16, 1891519945208520845426208⟩, ⟨.privateRow 6 17, 2616478107821756993734920⟩, ⟨.privateRow 6 18, 619303173900124462388640⟩, ⟨.privateRow 7 10, 23029364255582517696864⟩, ⟨.privateRow 7 11, 233059932556495749664960⟩, ⟨.privateRow 7 12, 468367475738536339645680⟩, ⟨.privateRow 7 13, 716666702316583369253760⟩, ⟨.privateRow 7 14, 925324005224306566919040⟩, ⟨.privateRow 7 15, 440669997106822230523776⟩, ⟨.privateRow 8 8, 24260048954744482708920⟩, ⟨.privateRow 8 9, 132341042563330616899884⟩, ⟨.privateRow 8 10, 268070790377482685352760⟩, ⟨.privateRow 8 11, 406417707871956678442545⟩, ⟨.privateRow 8 12, 96474363773386222784160⟩, ⟨.privateRow 9 6, 18153778129400633319600⟩, ⟨.privateRow 9 7, 83177310701981083573440⟩, ⟨.privateRow 9 8, 176765931042849595294848⟩, ⟨.privateRow 9 9, 7607297501844074914880⟩, ⟨.privateRow 10 4, 13645257407153882627040⟩, ⟨.privateRow 10 5, 61463505952399287096360⟩, ⟨.privateRow 10 6, 5941236478712934540960⟩, ⟨.privateRow 11 2, 10669975716872208971520⟩, ⟨.privateRow 11 3, 10054400194744966146240⟩, ⟨.privateRow 12 0, 3423283875829833711696⟩, ⟨.hall 4 21, 700217156419738713756000⟩, ⟨.hall 3 22, 8090857021309120024686720⟩, ⟨.hall 2 23, 24031452808325432656105920⟩, ⟨.assumptionRow 13, 12158187127560253139360⟩]
  caps := #[0, 3159868783456099088974600, 2182365155261678577830640, 575475500866824703775630, 42617768813935152895772, 0, 44465502571437406790760, 2881085554909773186690, 0, 88690698739202744131584, 12762104289743527428160, 0, 58288749252906788311696, 111719239925909665260640, 10323118921122493200000, 0] }

theorem case_41_26_13_checked :
    (Witness.linear .conditional case_41_26_13).check 41 26 13 = true := by
  change case_41_26_13.check 41 26 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_26_14 : Certificate := {
  objectiveScale := 5160127563360000
  eta := 2949709849929457655040
  rows := #[⟨.count 2, 481290192600534757440⟩, ⟨.count 3, 81274326020195948640⟩, ⟨.count 4, 13585444525369997280⟩, ⟨.count 5, 2166737563854864000⟩, ⟨.count 6, 346678010216778240⟩, ⟨.count 7, 84262016372133600⟩, ⟨.count 8, 33704806548853440⟩, ⟨.count 9, 21667375638548640⟩, ⟨.path 6, 74251510526793600⟩, ⟨.path 7, 12369796006588020⟩, ⟨.privateRow 2 24, 46476520744686832800⟩, ⟨.privateRow 3 21, 10036809893012142240⟩, ⟨.privateRow 3 22, 15730514713586312640⟩, ⟨.privateRow 4 18, 1604830288961835936⟩, ⟨.privateRow 4 19, 4399380061943646780⟩, ⟨.privateRow 4 20, 6554381130660963600⟩, ⟨.privateRow 4 21, 9603161444468411820⟩, ⟨.privateRow 5 15, 161989427392958880⟩, ⟨.privateRow 5 16, 938919611003774400⟩, ⟨.privateRow 5 17, 1750723951594730112⟩, ⟨.privateRow 5 18, 2672309662087665600⟩, ⟨.privateRow 5 19, 4140876233144851200⟩, ⟨.privateRow 5 20, 3560672063268159840⟩, ⟨.privateRow 6 13, 135872501400065430⟩, ⟨.privateRow 6 14, 424061494640166240⟩, ⟨.privateRow 6 15, 767386220531931000⟩, ⟨.privateRow 6 16, 1138259466878421888⟩, ⟨.privateRow 6 17, 1803809021909174280⟩, ⟨.privateRow 6 18, 1653943007075879520⟩, ⟨.privateRow 7 11, 75434567037910080⟩, ⟨.privateRow 7 12, 200122288883817300⟩, ⟨.privateRow 7 13, 365250046478391360⟩, ⟨.privateRow 7 14, 292108323423396480⟩, ⟨.privateRow 7 15, 1371304129301922816⟩, ⟨.privateRow 8 9, 36653977121878116⟩, ⟨.privateRow 8 10, 105327520465167000⟩, ⟨.privateRow 8 11, 195382550462884785⟩, ⟨.privateRow 8 12, 299130158121074280⟩, ⟨.privateRow 8 13, 218027967362895690⟩, ⟨.privateRow 9 7, 17508990414988800⟩, ⟨.privateRow 9 8, 61390897642554480⟩, ⟨.privateRow 9 9, 122246798355762080⟩, ⟨.privateRow 9 10, 97804126146226500⟩, ⟨.privateRow 10 5, 8727137409970980⟩, ⟨.privateRow 10 6, 39395228433724800⟩, ⟨.privateRow 10 7, 50196086895971016⟩, ⟨.privateRow 11 3, 4444589874574080⟩, ⟨.privateRow 11 4, 24676733366124840⟩, ⟨.privateRow 12 1, 2837394428857560⟩, ⟨.privateRow 12 2, 6111311077539360⟩, ⟨.hall 4 21, 1260319016308912560⟩, ⟨.hall 3 22, 6113968169312203200⟩, ⟨.hall 2 23, 15836444105596994880⟩, ⟨.assumptionRow 14, 4295222610641820⟩]
  caps := #[0, 4568950378421241120, 672973497083376720, 137352497088915108, 89386256901509568, 6548770112999400, 5600383026033510, 0, 23316978835006857, 0, 4295222610641820, 67378508995449960, 0, 283865620290698160, 52466180586318180, 5160127563360000] }

theorem case_41_26_14_checked :
    (Witness.linear .conditional case_41_26_14).check 41 26 14 = true := by
  change case_41_26_14.check 41 26 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_26_15 : Certificate := {
  objectiveScale := 20067162746400000
  eta := 14372605837401377005440
  rows := #[⟨.count 2, 2255660473475467618560⟩, ⟨.count 3, 355604968979860279680⟩, ⟨.count 4, 53229519485367825600⟩, ⟨.count 5, 6933560204335564800⟩, ⟨.count 6, 693356020433556480⟩, ⟨.count 7, 33704806548853440⟩, ⟨.path 6, 518624070975410400⟩, ⟨.path 7, 8258447622895470⟩, ⟨.privateRow 2 24, 227218545862913404800⟩, ⟨.privateRow 3 21, 46026320828641433280⟩, ⟨.privateRow 3 22, 75395244763603084320⟩, ⟨.privateRow 4 18, 6919837533097817328⟩, ⟨.privateRow 4 19, 19613488989477883500⟩, ⟨.privateRow 4 20, 30984347163124555200⟩, ⟨.privateRow 4 21, 48244217473865092680⟩, ⟨.privateRow 5 15, 724309414202911680⟩, ⟨.privateRow 5 16, 3796605709110133920⟩, ⟨.privateRow 5 17, 7557580622725765632⟩, ⟨.privateRow 5 18, 12375682718884364880⟩, ⟨.privateRow 5 19, 20848830336647913600⟩, ⟨.privateRow 5 20, 20266218680589161280⟩, ⟨.privateRow 6 12, 24074861820609600⟩, ⟨.privateRow 6 13, 527239473871350240⟩, ⟨.privateRow 6 14, 1630212071852707200⟩, ⟨.privateRow 6 15, 3174270531047375760⟩, ⟨.privateRow 6 16, 5136612518045264256⟩, ⟨.privateRow 6 17, 8981127202178411280⟩, ⟨.privateRow 6 18, 10202926439574348480⟩, ⟨.privateRow 6 19, 3802624424565286320⟩, ⟨.privateRow 7 10, 20222883929312064⟩, ⟨.privateRow 7 11, 264288483097358720⟩, ⟨.privateRow 7 12, 728264570073440400⟩, ⟨.privateRow 7 13, 1438988883677579520⟩, ⟨.privateRow 7 14, 2367361412359944000⟩, ⟨.privateRow 7 15, 4197692907041489856⟩, ⟨.privateRow 7 16, 4497184188089873280⟩, ⟨.privateRow 8 8, 7277174141229720⟩, ⟨.privateRow 8 9, 125971714476339732⟩, ⟨.privateRow 8 10, 359049814207924840⟩, ⟨.privateRow 8 11, 727286528811978135⟩, ⟨.privateRow 8 12, 515202042961045440⟩, ⟨.privateRow 8 13, 3671717363415721620⟩, ⟨.privateRow 9 6, 1203743091030480⟩, ⟨.privateRow 9 7, 60843741692086080⟩, ⟨.privateRow 9 8, 198376861401823104⟩, ⟨.privateRow 9 9, 424252564972075840⟩, ⟨.privateRow 9 10, 743913230256836640⟩, ⟨.privateRow 9 11, 643142737207713600⟩, ⟨.privateRow 10 5, 30093577275762000⟩, ⟨.privateRow 10 6, 123438382425671040⟩, ⟨.privateRow 10 7, 292509571120406640⟩, ⟨.privateRow 10 8, 303343258939680960⟩, ⟨.privateRow 11 3, 16667212029652800⟩, ⟨.privateRow 11 4, 86669502554194560⟩, ⟨.privateRow 11 5, 152328216610402560⟩, ⟨.privateRow 12 1, 11349577715430240⟩, ⟨.privateRow 12 2, 67224421852932960⟩, ⟨.privateRow 13 0, 22699155430860480⟩, ⟨.hall 4 21, 9280859231845000800⟩, ⟨.hall 3 22, 33512835694162144320⟩, ⟨.hall 2 23, 79612558683028371000⟩, ⟨.assumptionRow 15, 8123072810241312⟩]
  caps := #[0, 8532081128567409336, 1301992740816267654, 0, 64895096587857822, 77630295709431036, 17435240898589800, 35107650662832462, 8123072810241312, 16389482828179136, 11635076478864384, 0, 0, 0, 994272987392945568, 192548554653758688] }

theorem case_41_26_15_checked :
    (Witness.linear .conditional case_41_26_15).check 41 26 15 = true := by
  change case_41_26_15.check 41 26 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_26_16 : Certificate := {
  objectiveScale := 4562082439200000
  eta := 6368573036881299404160
  rows := #[⟨.count 2, 735448053592045553760⟩, ⟨.count 3, 92518180582392845280⟩, ⟨.count 4, 13479470018626772160⟩, ⟨.count 5, 2289900783696926400⟩, ⟨.count 6, 334201735999010880⟩, ⟨.count 7, 28881631506087360⟩, ⟨.path 3, 16385445285911301600⟩, ⟨.path 7, 33116315890587930⟩, ⟨.privateRow 5 17, 788468540116184928⟩, ⟨.privateRow 6 13, 51445406120218110⟩, ⟨.privateRow 6 14, 189204157417429440⟩, ⟨.privateRow 6 15, 509554498714541280⟩, ⟨.privateRow 6 17, 3216691708990479720⟩, ⟨.privateRow 7 10, 825189471602496⟩, ⟨.privateRow 7 12, 178705094943915540⟩, ⟨.privateRow 7 14, 955844471272891200⟩, ⟨.privateRow 7 15, 276851067722637408⟩, ⟨.privateRow 7 17, 4980706119014065440⟩, ⟨.privateRow 8 9, 180510196913046⟩, ⟨.privateRow 8 10, 22864624942319160⟩, ⟨.privateRow 8 11, 185474227328154765⟩, ⟨.privateRow 9 7, 562629185183520⟩, ⟨.privateRow 9 8, 9902273659229952⟩, ⟨.privateRow 9 9, 53637315654162240⟩, ⟨.privateRow 9 10, 185925502820437380⟩, ⟨.privateRow 10 6, 3094460518509360⟩, ⟨.privateRow 11 4, 515743419751560⟩, ⟨.hall 10 5, 369805034492190⟩, ⟨.hall 11 5, 255037954822200⟩, ⟨.hall 9 6, 316297071421650⟩, ⟨.hall 12 6, 181360323429120⟩, ⟨.hall 8 8, 133420529082400⟩, ⟨.hall 7 9, 168399064387260⟩, ⟨.hall 6 12, 33568153517052⟩, ⟨.hall 5 14, 356488725269820⟩, ⟨.hall 4 17, 4232973812036112⟩, ⟨.hall 4 18, 9025122068644968⟩, ⟨.hall 3 19, 35974545046546392⟩]
  caps := #[0, 1510916114485270350, 0, 95368067408581110, 0, 0, 0, 8463780426463362, 3905140667087517, 3015071989371936, 0, 0, 73487848763609280, 0, 702560695636800000, 200731627324800000] }

theorem case_41_26_16_checked :
    (Witness.linear .negative case_41_26_16).check 41 26 16 = true := by
  change case_41_26_16.check 41 26 16 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_27_1_checked :
    (Witness.rising).check 41 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_27_2_checked :
    (Witness.rising).check 41 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_27_3_checked :
    (Witness.rising).check 41 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_27_4_checked :
    (Witness.rising).check 41 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_27_5_checked :
    (Witness.rising).check 41 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_27_6_checked :
    (Witness.rising).check 41 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_27_7_checked :
    (Witness.rising).check 41 27 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_27_8_checked :
    (Witness.rising).check 41 27 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_27_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_41_27_9_checked :
    (Witness.linear .positive case_41_27_9).check 41 27 9 = true := by
  change case_41_27_9.check 41 27 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_27_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_41_27_10_checked :
    (Witness.linear .positive case_41_27_10).check 41 27 10 = true := by
  change case_41_27_10.check 41 27 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_27_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_41_27_11_checked :
    (Witness.linear .positive case_41_27_11).check 41 27 11 = true := by
  change case_41_27_11.check 41 27 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_27_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_41_27_12_checked :
    (Witness.linear .positive case_41_27_12).check 41 27 12 = true := by
  change case_41_27_12.check 41 27 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_27_13 : Certificate := {
  objectiveScale := 779716185000
  eta := 2008201191226531158
  rows := #[⟨.count 2, 272787904378530618⟩, ⟨.count 3, 35325052365565116⟩, ⟨.count 4, 4460233884541050⟩, ⟨.count 5, 547971591529329⟩, ⟨.count 6, 101948203075224⟩, ⟨.count 7, 29734892563607⟩, ⟨.count 8, 8495683589602⟩, ⟨.path 5, 198688728426188⟩, ⟨.path 6, 1405537136003⟩]
  caps := #[0, 636257564086432, 0, 12685680099939, 2444371148318, 4892900165901, 2379870480779, 3013187206393, 2420343000398, 3898580925000, 1559432370000, 779716185000, 779716185000, 0, 0] }

theorem case_41_27_13_checked :
    (Witness.linear .positive case_41_27_13).check 41 27 13 = true := by
  change case_41_27_13.check 41 27 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_27_14 : Certificate := {
  objectiveScale := 11712636000000
  eta := 14646464323423732800
  rows := #[⟨.count 2, 2199469045155782400⟩, ⟨.count 3, 330689401894051200⟩, ⟨.count 4, 48240103024713600⟩, ⟨.count 5, 6816536296970400⟩, ⟨.count 6, 932175903859200⟩, ⟨.count 7, 203913478969200⟩, ⟨.count 8, 116521987982400⟩, ⟨.path 6, 439146868960800⟩, ⟨.privateRow 2 25, 184570828964121600⟩, ⟨.privateRow 3 21, 8731866474431100⟩, ⟨.privateRow 3 22, 44860965373224000⟩, ⟨.privateRow 3 23, 63446222456416800⟩, ⟨.privateRow 4 18, 1864351807718400⟩, ⟨.privateRow 4 19, 10784109987771120⟩, ⟨.privateRow 4 20, 19684933344776700⟩, ⟨.privateRow 4 21, 26333969284022400⟩, ⟨.privateRow 4 22, 35043987885706800⟩, ⟨.privateRow 5 15, 152935109226900⟩, ⟨.privateRow 5 16, 2187284174412480⟩, ⟨.privateRow 5 17, 5319228751396560⟩, ⟨.privateRow 5 18, 8214800152759200⟩, ⟨.privateRow 5 19, 11002588715238120⟩, ⟨.privateRow 5 20, 15206119431703200⟩, ⟨.privateRow 5 21, 7970103977996160⟩, ⟨.privateRow 6 13, 252464307295200⟩, ⟨.privateRow 6 14, 1286596950639000⟩, ⟨.privateRow 6 15, 2494125409432800⟩, ⟨.privateRow 6 16, 3799911496981600⟩, ⟨.privateRow 6 17, 4967720754316320⟩, ⟨.privateRow 6 18, 6408709339032000⟩, ⟨.privateRow 7 11, 190804755321180⟩, ⟨.privateRow 7 12, 707223732615400⟩, ⟨.privateRow 7 13, 1316334332988675⟩, ⟨.privateRow 7 14, 1985035295271600⟩, ⟨.privateRow 7 15, 2614462105355100⟩, ⟨.privateRow 7 16, 329174616050280⟩, ⟨.privateRow 8 9, 124466668981200⟩, ⟨.privateRow 8 10, 428218305835320⟩, ⟨.privateRow 8 11, 814035554932600⟩, ⟨.privateRow 8 12, 1157937255575100⟩, ⟨.privateRow 9 7, 85773130042600⟩, ⟨.privateRow 9 8, 303663362620800⟩, ⟨.privateRow 9 9, 466087951929600⟩, ⟨.privateRow 10 5, 67224223836000⟩, ⟨.privateRow 10 6, 203913478969200⟩, ⟨.privateRow 11 3, 62422493562000⟩, ⟨.privateRow 11 4, 13444844767200⟩, ⟨.privateRow 12 1, 21362364463440⟩, ⟨.hall 3 23, 13498344045336150⟩, ⟨.hall 2 24, 49680314796176064⟩, ⟨.assumptionRow 14, 10724089521600⟩]
  caps := #[0, 0, 3083465704737600, 423467372479320, 157952540982600, 2423172351600, 70139556008600, 0, 0, 185716597539200, 10724089521600, 223624944385200, 0, 762459808219200, 129827542478400] }

theorem case_41_27_14_checked :
    (Witness.linear .conditional case_41_27_14).check 41 27 14 = true := by
  change case_41_27_14.check 41 27 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_27_15 : Certificate := {
  objectiveScale := 2840662005192000000
  eta := 3983139864573552671788800
  rows := #[⟨.count 2, 583583995100081942366400⟩, ⟨.count 3, 83762764169228003059200⟩, ⟨.count 4, 11322000420003306633600⟩, ⟨.count 5, 1402725715752622060800⟩, ⟨.count 6, 150292040973495220800⟩, ⟨.count 7, 14611726205756479800⟩, ⟨.path 5, 90081762910810070400⟩, ⟨.path 6, 95146993099441483200⟩, ⟨.privateRow 2 25, 53729404648024541436000⟩, ⟨.privateRow 3 21, 1607289882633212778000⟩, ⟨.privateRow 3 22, 12092942926478458044000⟩, ⟨.privateRow 3 23, 18300143377981008343800⟩, ⟨.privateRow 4 18, 254661513871755790800⟩, ⟨.privateRow 4 19, 2519896553655603202080⟩, ⟨.privateRow 4 20, 5263352518259280545100⟩, ⟨.privateRow 4 21, 7648194973984534569600⟩, ⟨.privateRow 4 22, 11052727179925794363000⟩, ⟨.privateRow 5 16, 411513921713141676000⟩, ⟨.privateRow 5 17, 1244919072730452078960⟩, ⟨.privateRow 5 18, 2150178132860804958912⟩, ⟨.privateRow 5 19, 3186191268638098680960⟩, ⟨.privateRow 5 20, 4914549739833293720160⟩, ⟨.privateRow 5 21, 3977729351098506843840⟩, ⟨.privateRow 6 13, 25357916378244049600⟩, ⟨.privateRow 6 14, 243180871852947128100⟩, ⟨.privateRow 6 15, 563793952646603764800⟩, ⟨.privateRow 6 16, 967157115523881282000⟩, ⟨.privateRow 6 17, 1416641645472390136800⟩, ⟨.privateRow 6 18, 2262034375948300753800⟩, ⟨.privateRow 6 19, 1260783232610987685600⟩, ⟨.privateRow 7 11, 19412721959076466020⟩, ⟨.privateRow 7 12, 127098824773881760800⟩, ⟨.privateRow 7 13, 281275729460812236150⟩, ⟨.privateRow 7 14, 484572552741924075000⟩, ⟨.privateRow 7 15, 719801464755003731100⟩, ⟨.privateRow 7 16, 1040354905849861361760⟩, ⟨.privateRow 8 9, 11385760679810244000⟩, ⟨.privateRow 8 10, 70136285787631103040⟩, ⟨.privateRow 8 11, 161888649073301950800⟩, ⟨.privateRow 8 12, 283624042601023098975⟩, ⟨.privateRow 8 13, 429107632858848457800⟩, ⟨.privateRow 8 14, 76189715215730216100⟩, ⟨.privateRow 9 7, 6726032697887903400⟩, ⟨.privateRow 9 8, 43771924391270493600⟩, ⟨.privateRow 9 9, 110214163380563161920⟩, ⟨.privateRow 9 10, 202244845260629371200⟩, ⟨.privateRow 9 11, 17394912149710095000⟩, ⟨.privateRow 10 5, 4624370491492160640⟩, ⟨.privateRow 10 6, 32145797652664255560⟩, ⟨.privateRow 10 7, 91541515865674361760⟩, ⟨.privateRow 10 8, 5510708169028158096⟩, ⟨.privateRow 11 3, 4472977409925453000⟩, ⟨.privateRow 11 4, 29865726090886870800⟩, ⟨.privateRow 11 5, 10436947289826057000⟩, ⟨.privateRow 12 1, 6123009076697953440⟩, ⟨.privateRow 12 2, 6560366867890664400⟩, ⟨.hall 4 22, 272268190169375400000⟩, ⟨.hall 3 23, 5028521204238194262600⟩, ⟨.hall 2 24, 15363854375250504771648⟩, ⟨.assumptionRow 15, 1566108611862444000⟩]
  caps := #[0, 0, 0, 224933054915432638656, 0, 54006186756604724928, 0, 10642071708422638380, 6884845986735256605, 1566108611862444000, 43852941018545904504, 477117590392048320, 0, 654910364304007812000, 165849726995130672000] }

theorem case_41_27_15_checked :
    (Witness.linear .conditional case_41_27_15).check 41 27 15 = true := by
  change case_41_27_15.check 41 27 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_27_16 : Certificate := {
  objectiveScale := 231910192800000
  eta := 473915596125088877760
  rows := #[⟨.count 2, 70999783631773476480⟩, ⟨.count 3, 10519960467114418320⟩, ⟨.count 4, 1365194915599394880⟩, ⟨.count 5, 171252365737733280⟩, ⟨.count 6, 14472030907414080⟩, ⟨.path 6, 14269159175150880⟩, ⟨.privateRow 3 22, 1615507450183186560⟩, ⟨.privateRow 4 4, 964802060494272⟩, ⟨.privateRow 4 18, 11256024039099840⟩, ⟨.privateRow 4 19, 254707743970487808⟩, ⟨.privateRow 4 21, 2193718685048850960⟩, ⟨.privateRow 4 22, 163413348996217320⟩, ⟨.privateRow 5 19, 1210826585920311360⟩, ⟨.privateRow 5 20, 452974567402060704⟩, ⟨.privateRow 6 13, 3781785854406560⟩, ⟨.privateRow 6 17, 313185468859335072⟩, ⟨.privateRow 6 19, 994550124026178720⟩, ⟨.privateRow 7 9, 33500071544940⟩, ⟨.privateRow 7 11, 3356707168802988⟩, ⟨.privateRow 7 12, 3439340678613840⟩, ⟨.privateRow 7 13, 7964642009809485⟩, ⟨.privateRow 7 14, 16568178241226040⟩, ⟨.privateRow 7 16, 295229430511247232⟩, ⟨.privateRow 7 17, 12411776507400270⟩, ⟨.privateRow 7 18, 282472603266934080⟩, ⟨.privateRow 8 7, 15461571482280⟩, ⟨.privateRow 8 9, 2010004292696400⟩, ⟨.privateRow 8 11, 10876356561590520⟩, ⟨.privateRow 8 14, 56916621554853060⟩, ⟨.privateRow 8 17, 76782163981002480⟩, ⟨.privateRow 9 5, 19142898025680⟩, ⟨.privateRow 9 7, 513667763689080⟩, ⟨.privateRow 9 9, 134000286179760⟩, ⟨.privateRow 10 5, 259754400902304⟩, ⟨.privateRow 12 10, 737001573988680⟩, ⟨.hall 9 5, 35526966630012⟩, ⟨.hall 10 6, 11888519248980⟩, ⟨.hall 12 6, 5301110222496⟩, ⟨.hall 8 7, 14807366703360⟩, ⟨.hall 11 7, 5411550018798⟩, ⟨.hall 7 8, 4502843624664⟩, ⟨.hall 7 9, 1604796235119⟩, ⟨.hall 3 19, 183522131072280⟩, ⟨.hall 4 19, 442632227076000⟩, ⟨.hall 2 22, 15650068205916144⟩]
  caps := #[0, 0, 18991514819740320, 2043409479656688, 3546568928022120, 0, 0, 878388521906610, 117558547258680, 795123851327520, 0, 0, 10668341192559336, 6426713815689024, 48237320102400000] }

theorem case_41_27_16_checked :
    (Witness.linear .negative case_41_27_16).check 41 27 16 = true := by
  change case_41_27_16.check 41 27 16 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_27_17 : Certificate := {
  objectiveScale := 1532610133236000000
  eta := 3857771253728162075104800
  rows := #[⟨.count 2, 513046930536521518737600⟩, ⟨.count 3, 62959840831146706246800⟩, ⟨.count 4, 6662947149824954788800⟩, ⟨.count 5, 500973469911650736000⟩, ⟨.count 6, 16699115663721691200⟩, ⟨.path 5, 375293614133124086400⟩, ⟨.path 6, 11020535575972322400⟩, ⟨.hall 12 5, 91753382767701600⟩, ⟨.hall 10 7, 54095243048872200⟩, ⟨.hall 11 7, 44156315456956395⟩, ⟨.hall 9 9, 48015968115760848⟩, ⟨.hall 8 11, 66760817607206800⟩, ⟨.hall 7 12, 75081064015562220⟩, ⟨.hall 6 13, 74575268364082200⟩, ⟨.hall 5 15, 96161250913258050⟩]
  caps := #[0, 1767724423840446271200, 73009014028925738400, 13662022233110050800, 0, 5033960999905219200, 0, 0, 10019469398233014720, 2865980949151320000, 0, 0, 209605624055114987700, 0, 657489747158244000000] }

theorem case_41_27_17_checked :
    (Witness.linear .negative case_41_27_17).check 41 27 17 = true := by
  change case_41_27_17.check 41 27 17 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_28_1_checked :
    (Witness.rising).check 41 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_28_2_checked :
    (Witness.rising).check 41 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_28_3_checked :
    (Witness.rising).check 41 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_28_4_checked :
    (Witness.rising).check 41 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_28_5_checked :
    (Witness.rising).check 41 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_28_6_checked :
    (Witness.rising).check 41 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_28_7_checked :
    (Witness.rising).check 41 28 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_28_8_checked :
    (Witness.rising).check 41 28 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_28_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_41_28_9_checked :
    (Witness.linear .positive case_41_28_9).check 41 28 9 = true := by
  change case_41_28_9.check 41 28 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_28_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_41_28_10_checked :
    (Witness.linear .positive case_41_28_10).check 41 28 10 = true := by
  change case_41_28_10.check 41 28 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_28_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_41_28_11_checked :
    (Witness.linear .positive case_41_28_11).check 41 28 11 = true := by
  change case_41_28_11.check 41 28 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_28_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_41_28_12_checked :
    (Witness.linear .positive case_41_28_12).check 41 28 12 = true := by
  change case_41_28_12.check 41 28 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_28_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_41_28_13_checked :
    (Witness.linear .positive case_41_28_13).check 41 28 13 = true := by
  change case_41_28_13.check 41 28 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_28_14 : Certificate := {
  objectiveScale := 1781052000000
  eta := 4985525435442552000
  rows := #[⟨.count 2, 605179388117304000⟩, ⟨.count 3, 73617059766650400⟩, ⟨.count 4, 8069058508230720⟩, ⟨.count 5, 698619784262400⟩, ⟨.count 6, 43663736516400⟩, ⟨.count 7, 43663736516400⟩, ⟨.path 5, 498674254478400⟩, ⟨.privateRow 2 25, 12727979194530600⟩, ⟨.privateRow 2 26, 50911916778122400⟩, ⟨.privateRow 3 22, 8405269279407000⟩, ⟨.privateRow 3 23, 14409033050412000⟩, ⟨.privateRow 3 24, 16417564930166400⟩, ⟨.privateRow 4 18, 378003204699120⟩, ⟨.privateRow 4 19, 1667954734926480⟩, ⟨.privateRow 4 20, 4574213037458064⟩, ⟨.privateRow 4 21, 5750514099209880⟩, ⟨.privateRow 4 22, 6759146412738720⟩, ⟨.privateRow 4 23, 7689184000538040⟩, ⟨.privateRow 5 15, 104792967639360⟩, ⟨.privateRow 5 16, 366775386737760⟩, ⟨.privateRow 5 17, 1117791654819840⟩, ⟨.privateRow 5 18, 1961957227470240⟩, ⟨.privateRow 5 19, 2508045025502016⟩, ⟨.privateRow 5 20, 2855608368172560⟩, ⟨.privateRow 5 21, 2251108193734400⟩, ⟨.privateRow 6 12, 9262004715600⟩, ⟨.privateRow 6 13, 76411538903700⟩, ⟨.privateRow 6 14, 278962761077000⟩, ⟨.privateRow 6 15, 608563327697325⟩, ⟨.privateRow 6 16, 942928786199400⟩, ⟨.privateRow 6 17, 1237139201298000⟩, ⟨.privateRow 6 18, 963513119128560⟩, ⟨.privateRow 7 10, 3118838322600⟩, ⟨.privateRow 7 11, 66913258557600⟩, ⟨.privateRow 7 12, 192744208336680⟩, ⟨.privateRow 7 13, 367329846884000⟩, ⟨.privateRow 7 14, 550474963938900⟩, ⟨.privateRow 7 15, 286042029015600⟩, ⟨.privateRow 8 8, 1119582987600⟩, ⟨.privateRow 8 9, 60037637710050⟩, ⟨.privateRow 8 10, 141576357795600⟩, ⟨.privateRow 8 11, 294002492543760⟩, ⟨.privateRow 9 7, 61800980915520⟩, ⟨.privateRow 9 8, 100911746615680⟩, ⟨.privateRow 10 5, 50525180826120⟩, ⟨.privateRow 11 3, 11643663071040⟩, ⟨.hall 3 24, 806905850823072⟩, ⟨.hall 2 25, 9606022033608000⟩, ⟨.assumptionRow 14, 1751059084320⟩]
  caps := #[0, 0, 103120582361160, 345070351626000, 28415857697136, 8864161289984, 16066870092000, 0, 7670751549510, 41148731254400, 1751059084320, 270444482118720, 601552735230720, 135779852819520] }

theorem case_41_28_14_checked :
    (Witness.linear .conditional case_41_28_14).check 41 28 14 = true := by
  change case_41_28_14.check 41 28 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_28_15 : Certificate := {
  objectiveScale := 8396388000000
  eta := 20351318280401908800
  rows := #[⟨.count 2, 2524462590432182400⟩, ⟨.count 3, 306519430345128000⟩, ⟨.count 4, 32381027000562240⟩, ⟨.count 5, 2445169244918400⟩, ⟨.count 6, 261982419098400⟩, ⟨.count 7, 130991209549200⟩, ⟨.path 5, 2073925637784000⟩, ⟨.privateRow 2 25, 122476780928502000⟩, ⟨.privateRow 2 26, 289621564313281200⟩, ⟨.privateRow 3 22, 40934752984125000⟩, ⟨.privateRow 3 23, 81301877393536800⟩, ⟨.privateRow 3 24, 94313670875424000⟩, ⟨.privateRow 4 18, 830858529140640⟩, ⟨.privateRow 4 19, 7139020920431400⟩, ⟨.privateRow 4 20, 22085117929995120⟩, ⟨.privateRow 4 21, 31280700840348960⟩, ⟨.privateRow 4 22, 40292896057333920⟩, ⟨.privateRow 4 23, 50497111281216600⟩, ⟨.privateRow 5 15, 163011282994560⟩, ⟨.privateRow 5 16, 1174554512291160⟩, ⟨.privateRow 5 17, 4705703261138880⟩, ⟨.privateRow 5 18, 9443010750613440⟩, ⟨.privateRow 5 19, 13441444649208576⟩, ⟨.privateRow 5 20, 15692746903994160⟩, ⟨.privateRow 5 21, 26535908138900160⟩, ⟨.privateRow 6 13, 137540770026660⟩, ⟨.privateRow 6 14, 892680835446400⟩, ⟨.privateRow 6 15, 2518851800289825⟩, ⟨.privateRow 6 16, 4450582286350200⟩, ⟨.privateRow 6 17, 6527728609201800⟩, ⟨.privateRow 6 18, 8387803784800440⟩, ⟨.privateRow 6 19, 5801818989616650⟩, ⟨.privateRow 7 11, 100369887836400⟩, ⟨.privateRow 7 12, 604430866919880⟩, ⟨.privateRow 7 13, 1459616334976800⟩, ⟨.privateRow 7 14, 2505206882628450⟩, ⟨.privateRow 7 15, 3691813477294800⟩, ⟨.privateRow 7 16, 2597992322725800⟩, ⟨.privateRow 8 9, 78230861258550⟩, ⟨.privateRow 8 10, 448545656941200⟩, ⟨.privateRow 8 11, 1019548247657940⟩, ⟨.privateRow 8 12, 1748975223795800⟩, ⟨.privateRow 8 13, 769573356101550⟩, ⟨.privateRow 9 7, 72548977596480⟩, ⟨.privateRow 9 8, 398795460183120⟩, ⟨.privateRow 9 9, 911381264015040⟩, ⟨.privateRow 9 10, 62875780583616⟩, ⟨.privateRow 10 5, 89822543690880⟩, ⟨.privateRow 10 6, 405065124913680⟩, ⟨.privateRow 11 3, 139723956852480⟩, ⟨.privateRow 11 4, 18713029935600⟩, ⟨.privateRow 12 1, 90056456565075⟩, ⟨.hall 3 24, 10091562783670368⟩, ⟨.hall 2 25, 59963745232868400⟩, ⟨.assumptionRow 15, 5508259520400⟩]
  caps := #[0, 5342254030713600, 228231307231200, 969131804155200, 109673580612960, 265332086763744, 0, 112724256263580, 24653169122400, 80899056365568, 0, 1139321306541600, 0, 2442992443164000] }

theorem case_41_28_15_checked :
    (Witness.linear .conditional case_41_28_15).check 41 28 15 = true := by
  change case_41_28_15.check 41 28 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_28_16 : Certificate := {
  objectiveScale := 1861619760000
  eta := 2458416035505830400
  rows := #[⟨.count 2, 134888338581796800⟩, ⟨.count 3, 10372479897780000⟩, ⟨.path 3, 10308389778086400⟩, ⟨.privateRow 2 17, 4234276793827080⟩, ⟨.privateRow 2 23, 26686085781455100⟩, ⟨.privateRow 2 24, 49864736693772000⟩, ⟨.privateRow 2 25, 82150040790417600⟩, ⟨.privateRow 2 26, 114350828384192400⟩, ⟨.privateRow 3 18, 380324262918600⟩, ⟨.privateRow 3 19, 4116063451500000⟩, ⟨.privateRow 3 20, 3933859042713600⟩, ⟨.privateRow 3 21, 12732795323408160⟩, ⟨.privateRow 3 22, 15305170338057600⟩, ⟨.privateRow 3 23, 32715569929442400⟩, ⟨.privateRow 3 24, 33307185449538000⟩, ⟨.privateRow 4 13, 2304995532840⟩, ⟨.privateRow 4 14, 88008920344800⟩, ⟨.privateRow 4 15, 463304102100840⟩, ⟨.privateRow 4 16, 580858874275680⟩, ⟨.privateRow 4 17, 1261985054229900⟩, ⟨.privateRow 4 18, 2424196730395440⟩, ⟨.privateRow 4 19, 3741007749799320⟩, ⟨.privateRow 4 20, 7750316979621216⟩, ⟨.privateRow 4 21, 11088181010726820⟩, ⟨.privateRow 4 22, 14217212446557120⟩, ⟨.privateRow 4 23, 17328956415891120⟩, ⟨.privateRow 5 9, 819553967232⟩, ⟨.privateRow 5 11, 100710574050240⟩, ⟨.privateRow 5 12, 85028724100320⟩, ⟨.privateRow 5 13, 205074754073280⟩, ⟨.privateRow 5 14, 323314040073024⟩, ⟨.privateRow 5 15, 541588580012480⟩, ⟨.privateRow 5 16, 877434966167760⟩, ⟨.privateRow 5 17, 2000297075736960⟩, ⟨.privateRow 5 18, 3184991605155360⟩, ⟨.privateRow 5 19, 4562047158596928⟩, ⟨.privateRow 5 20, 5937668492595840⟩, ⟨.privateRow 5 21, 7773469379195520⟩, ⟨.privateRow 6 5, 213425512300⟩, ⟨.privateRow 6 7, 12485392469550⟩, ⟨.privateRow 6 8, 37648260369720⟩, ⟨.privateRow 6 9, 42532655665500⟩, ⟨.privateRow 6 10, 77128696675800⟩, ⟨.privateRow 6 11, 108526873004550⟩, ⟨.privateRow 6 12, 158904995067000⟩, ⟨.privateRow 6 13, 238951203571080⟩, ⟨.privateRow 6 14, 538685993045200⟩, ⟨.privateRow 6 15, 982984553275725⟩, ⟨.privateRow 6 16, 1511967307851000⟩, ⟨.privateRow 6 17, 2165415247795800⟩, ⟨.privateRow 6 18, 2842059491991720⟩, ⟨.privateRow 6 19, 1398363956589600⟩, ⟨.privateRow 7 3, 2426311087200⟩, ⟨.privateRow 7 4, 6768637675800⟩, ⟨.privateRow 7 5, 26923897400400⟩, ⟨.privateRow 7 6, 24284774363850⟩, ⟨.privateRow 7 7, 2853803993040⟩, ⟨.privateRow 7 8, 125833939803000⟩, ⟨.privateRow 7 9, 33181803824400⟩, ⟨.privateRow 7 10, 92748629773800⟩, ⟨.privateRow 7 11, 179909391589200⟩, ⟨.privateRow 7 12, 337187917946880⟩, ⟨.privateRow 7 13, 571492543221600⟩, ⟨.privateRow 7 14, 865196537505300⟩, ⟨.privateRow 7 15, 1223529261411600⟩, ⟨.privateRow 7 16, 262330443975600⟩, ⟨.privateRow 8 0, 2926978454400⟩, ⟨.privateRow 8 1, 6338737715310⟩, ⟨.privateRow 8 2, 11120592483000⟩, ⟨.privateRow 8 4, 84742482825000⟩, ⟨.privateRow 8 6, 89382604551240⟩, ⟨.privateRow 8 7, 27714827240100⟩, ⟨.privateRow 8 8, 89244698835600⟩, ⟨.privateRow 8 9, 159748995956550⟩, ⟨.privateRow 8 10, 89405887334400⟩, ⟨.privateRow 8 11, 760648525837200⟩, ⟨.privateRow 9 0, 68535200509776⟩, ⟨.privateRow 9 1, 10999276928640⟩, ⟨.privateRow 9 2, 67954683116320⟩, ⟨.privateRow 9 3, 17716828409280⟩, ⟨.privateRow 9 5, 253242175874688⟩, ⟨.privateRow 10 0, 155769171798240⟩, ⟨.privateRow 11 0, 66588759837600⟩, ⟨.privateRow 12 0, 29829353954400⟩, ⟨.hall 3 24, 2727270714456288⟩, ⟨.hall 2 25, 20908082556345600⟩]
  caps := #[0, 0, 0, 0, 25558508908296, 0, 49829496686725, 1786261096620, 43636709508000, 0, 86650953348960, 15214259860800, 0, 1694073981600000] }

theorem case_41_28_16_checked :
    (Witness.linear .negative case_41_28_16).check 41 28 16 = true := by
  change case_41_28_16.check 41 28 16 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_28_17 : Certificate := {
  objectiveScale := 18321058555800000
  eta := 48400789267477272225600
  rows := #[⟨.count 2, 6351031553843064488400⟩, ⟨.count 3, 771727506542586594000⟩, ⟨.count 4, 80357657824116953280⟩, ⟨.count 5, 5988714336485680800⟩, ⟨.path 5, 4837683217511944800⟩, ⟨.path 6, 90536757666755400⟩, ⟨.privateRow 6 12, 6186688364138100⟩, ⟨.privateRow 6 13, 6805357200551910⟩, ⟨.hall 10 6, 527888082783600⟩, ⟨.hall 11 6, 725846113827450⟩, ⟨.hall 6 10, 582282565681500⟩, ⟨.hall 7 10, 679347200102725⟩, ⟨.hall 9 10, 694842160640040⟩, ⟨.hall 8 11, 829154737747644⟩, ⟨.hall 10 11, 590208203667775⟩, ⟨.hall 11 11, 362923056913725⟩, ⟨.hall 5 13, 522031200927600⟩, ⟨.hall 4 17, 1919309335589100⟩]
  caps := #[0, 0, 3719515141196454600, 1221595906480349400, 65054723549535720, 182725015300928100, 90536757666755400, 37120130184828600, 0, 450455469657401208, 341980879002562800, 4302584568458776600, 0, 30009893914400400000] }

theorem case_41_28_17_checked :
    (Witness.linear .negative case_41_28_17).check 41 28 17 = true := by
  change case_41_28_17.check 41 28 17 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_28_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4862, 4862, 3432, 2002] }

theorem case_41_28_18_checked :
    (Witness.linear .negative case_41_28_18).check 41 28 18 = true := by
  change case_41_28_18.check 41 28 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_29_1_checked :
    (Witness.rising).check 41 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_29_2_checked :
    (Witness.rising).check 41 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_29_3_checked :
    (Witness.rising).check 41 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_29_4_checked :
    (Witness.rising).check 41 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_29_5_checked :
    (Witness.rising).check 41 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_29_6_checked :
    (Witness.rising).check 41 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_29_7_checked :
    (Witness.rising).check 41 29 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_29_8_checked :
    (Witness.rising).check 41 29 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_29_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_41_29_9_checked :
    (Witness.linear .positive case_41_29_9).check 41 29 9 = true := by
  change case_41_29_9.check 41 29 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_29_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_41_29_10_checked :
    (Witness.linear .positive case_41_29_10).check 41 29 10 = true := by
  change case_41_29_10.check 41 29 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_29_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_41_29_11_checked :
    (Witness.linear .positive case_41_29_11).check 41 29 11 = true := by
  change case_41_29_11.check 41 29 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_29_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_41_29_12_checked :
    (Witness.linear .positive case_41_29_12).check 41 29 12 = true := by
  change case_41_29_12.check 41 29 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_29_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_41_29_13_checked :
    (Witness.linear .positive case_41_29_13).check 41 29 13 = true := by
  change case_41_29_13.check 41 29 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_29_14 : Certificate := {
  objectiveScale := 821
  eta := 121263890
  rows := #[⟨.assumptionRow 14, 1790⟩]
  caps := #[0, 0, 35384650, 10475400, 3154840, 969969, 305855, 100815, 35772, 13566, 1160862, 655554, 233614] }

theorem case_41_29_14_checked :
    (Witness.linear .conditional case_41_29_14).check 41 29 14 = true := by
  change case_41_29_14.check 41 29 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_29_15 : Certificate := {
  objectiveScale := 218988019250000
  eta := 1062218542718362629600
  rows := #[⟨.count 2, 108653557433014994400⟩, ⟨.count 3, 9867373521083638560⟩, ⟨.count 4, 674692206569821440⟩, ⟨.count 5, 23426812728118800⟩, ⟨.path 4, 470299442289276600⟩, ⟨.path 5, 9389871813722400⟩, ⟨.privateRow 2 26, 9733840688533361400⟩, ⟨.privateRow 2 27, 12580198434999795600⟩, ⟨.privateRow 3 22, 1051395355237971744⟩, ⟨.privateRow 3 23, 2182207605624266220⟩, ⟨.privateRow 3 24, 4315218904519482960⟩, ⟨.privateRow 3 25, 3963816713597700960⟩, ⟨.privateRow 4 18, 34554548773975230⟩, ⟨.privateRow 4 19, 317935315595898000⟩, ⟨.privateRow 4 20, 524760605109861120⟩, ⟨.privateRow 4 21, 1198515739170557808⟩, ⟨.privateRow 4 22, 1548512321328652680⟩, ⟨.privateRow 4 23, 1766381679700157520⟩, ⟨.privateRow 4 24, 1511029420963662600⟩, ⟨.privateRow 5 15, 11244870109497024⟩, ⟨.privateRow 5 16, 69499544426752440⟩, ⟨.privateRow 5 17, 144074898277930620⟩, ⟨.privateRow 5 18, 329983390713216240⟩, ⟨.privateRow 5 19, 532179095807098740⟩, ⟨.privateRow 5 20, 687342685443005592⟩, ⟨.privateRow 5 21, 787726577982994650⟩, ⟨.privateRow 5 22, 173358414188079120⟩, ⟨.privateRow 6 12, 1533898452436350⟩, ⟨.privateRow 6 13, 14755849575503400⟩, ⟨.privateRow 6 14, 37650234741619500⟩, ⟨.privateRow 6 15, 103561386425096600⟩, ⟨.privateRow 6 16, 186159494000229750⟩, ⟨.privateRow 6 17, 224467113792893400⟩, ⟨.privateRow 6 18, 470209598328670200⟩, ⟨.privateRow 7 9, 119524554735300⟩, ⟨.privateRow 7 10, 2960531278828200⟩, ⟨.privateRow 7 11, 10179507911623050⟩, ⟨.privateRow 7 12, 33771119647028400⟩, ⟨.privateRow 7 13, 76304475743015520⟩, ⟨.privateRow 7 14, 126058563727496400⟩, ⟨.privateRow 7 15, 134495005215896325⟩, ⟨.privateRow 8 7, 468536254562376⟩, ⟨.privateRow 8 8, 2677350026070720⟩, ⟨.privateRow 8 9, 12073818867568920⟩, ⟨.privateRow 8 10, 34554548773975230⟩, ⟨.privateRow 8 11, 70280438184356400⟩, ⟨.privateRow 8 12, 16633037036964348⟩, ⟨.privateRow 9 5, 878505477304455⟩, ⟨.privateRow 9 6, 4685362545623760⟩, ⟨.privateRow 9 7, 18072112675977360⟩, ⟨.privateRow 9 8, 23426812728118800⟩, ⟨.privateRow 10 3, 1653657369043680⟩, ⟨.privateRow 10 4, 10542065727653460⟩, ⟨.privateRow 10 5, 1874145018249504⟩, ⟨.privateRow 11 1, 3904468788019800⟩, ⟨.hall 2 26, 1759613933800923200⟩, ⟨.assumptionRow 15, 163899393127470⟩]
  caps := #[0, 0, 845548017734420, 114641185479748928, 5643421350587020, 3678191758104864, 16333090770515480, 0, 13630252428920358, 0, 142857822431680356, 104355639703234920, 283118362863656320] }

theorem case_41_29_15_checked :
    (Witness.linear .conditional case_41_29_15).check 41 29 15 = true := by
  change case_41_29_15.check 41 29 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_29_16 : Certificate := {
  objectiveScale := 1150578000000
  eta := 7520760787923583200
  rows := #[⟨.count 2, 745525506365640000⟩, ⟨.count 3, 63830386050631200⟩, ⟨.count 4, 3708081919301760⟩, ⟨.path 4, 3705179927248800⟩, ⟨.privateRow 2 26, 69275235254425200⟩, ⟨.privateRow 2 27, 92143601910360000⟩, ⟨.privateRow 3 22, 7143642155377728⟩, ⟨.privateRow 3 23, 14776483069988640⟩, ⟨.privateRow 3 24, 30491155541246400⟩, ⟨.privateRow 3 25, 29351925553991040⟩, ⟨.privateRow 4 18, 358801601378220⟩, ⟨.privateRow 4 19, 2032743702749760⟩, ⟨.privateRow 4 20, 3371152789084080⟩, ⟨.privateRow 4 21, 8008116675118560⟩, ⟨.privateRow 4 22, 10903659559392600⟩, ⟨.privateRow 4 23, 13153266486840480⟩, ⟨.privateRow 4 24, 13726604454282720⟩, ⟨.privateRow 5 13, 465371726820⟩, ⟨.privateRow 5 14, 11676599691120⟩, ⟨.privateRow 5 15, 137936179829448⟩, ⟨.privateRow 5 16, 447997849018720⟩, ⟨.privateRow 5 17, 883740909231180⟩, ⟨.privateRow 5 18, 2071834927802640⟩, ⟨.privateRow 5 19, 3508902820222800⟩, ⟨.privateRow 5 20, 4779181485750672⟩, ⟨.privateRow 5 21, 5865079873112460⟩, ⟨.privateRow 5 22, 3695051510950800⟩, ⟨.privateRow 6 11, 4602577518000⟩, ⟨.privateRow 6 12, 42880680542700⟩, ⟨.privateRow 6 13, 115315487632800⟩, ⟨.privateRow 6 14, 234547350317280⟩, ⟨.privateRow 6 15, 620052424591600⟩, ⟨.privateRow 6 16, 1146808898235000⟩, ⟨.privateRow 6 17, 1792156017366000⟩, ⟨.privateRow 6 18, 2484420204466200⟩, ⟨.privateRow 6 19, 1933818969962880⟩, ⟨.privateRow 7 8, 2127413608320⟩, ⟨.privateRow 7 9, 15670680597000⟩, ⟨.privateRow 7 10, 40502682158400⟩, ⟨.privateRow 7 11, 79113193559400⟩, ⟨.privateRow 7 12, 207060199491600⟩, ⟨.privateRow 7 13, 449150198056560⟩, ⟨.privateRow 7 14, 761879998479600⟩, ⟨.privateRow 7 15, 1146808898235000⟩, ⟨.privateRow 7 16, 491204606349600⟩, ⟨.privateRow 8 6, 10121835058335⟩, ⟨.privateRow 8 7, 19359463835712⟩, ⟨.privateRow 8 8, 40287895207560⟩, ⟨.privateRow 8 9, 95365406172960⟩, ⟨.privateRow 8 10, 102847151627220⟩, ⟨.privateRow 8 11, 625967279093520⟩, ⟨.privateRow 8 12, 285365942886024⟩, ⟨.privateRow 9 4, 28250801298720⟩, ⟨.privateRow 9 5, 23733958067820⟩, ⟨.privateRow 9 6, 70736502476640⟩, ⟨.privateRow 9 7, 142802638458480⟩, ⟨.privateRow 9 8, 152928308998080⟩, ⟨.privateRow 10 1, 8817569560800⟩, ⟨.privateRow 10 2, 63290554847520⟩, ⟨.privateRow 10 3, 67013528662080⟩, ⟨.privateRow 11 0, 52905417364800⟩, ⟨.hall 2 26, 13775003113872000⟩, ⟨.assumptionRow 16, 344586392150⟩]
  caps := #[0, 380960183832800, 0, 0, 9256607525984, 9653945086240, 0, 26153931858980, 58838052283017, 0, 217937319943200, 0, 3795604157345000] }

theorem case_41_29_16_checked :
    (Witness.linear .conditional case_41_29_16).check 41 29 16 = true := by
  change case_41_29_16.check 41 29 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_29_17 : Certificate := {
  objectiveScale := 491
  eta := 7397973
  rows := #[⟨.assumptionRow 17, 319⟩]
  caps := #[0, 0, 3130839, 1139544, 484296, 194152, 75712, 34723, 13566, 5161540, 4951590, 3321936, 1823556] }

theorem case_41_29_17_checked :
    (Witness.linear .conditional case_41_29_17).check 41 29 17 = true := by
  change case_41_29_17.check 41 29 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_29_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 16796, 16796, 11934, 7072] }

theorem case_41_29_18_checked :
    (Witness.linear .negative case_41_29_18).check 41 29 18 = true := by
  change case_41_29_18.check 41 29 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_30_1_checked :
    (Witness.rising).check 41 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_30_2_checked :
    (Witness.rising).check 41 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_30_3_checked :
    (Witness.rising).check 41 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_30_4_checked :
    (Witness.rising).check 41 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_30_5_checked :
    (Witness.rising).check 41 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_30_6_checked :
    (Witness.rising).check 41 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_30_7_checked :
    (Witness.rising).check 41 30 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_30_8_checked :
    (Witness.rising).check 41 30 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_30_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_41_30_9_checked :
    (Witness.linear .positive case_41_30_9).check 41 30 9 = true := by
  change case_41_30_9.check 41 30 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_30_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_41_30_10_checked :
    (Witness.linear .positive case_41_30_10).check 41 30 10 = true := by
  change case_41_30_10.check 41 30 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_41_30_11_checked :
    (Witness.linear .positive case_41_30_11).check 41 30 11 = true := by
  change case_41_30_11.check 41 30 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_30_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_41_30_12_checked :
    (Witness.linear .positive case_41_30_12).check 41 30 12 = true := by
  change case_41_30_12.check 41 30 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_30_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_41_30_13_checked :
    (Witness.linear .positive case_41_30_13).check 41 30 13 = true := by
  change case_41_30_13.check 41 30 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_30_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_41_30_14_checked :
    (Witness.linear .positive case_41_30_14).check 41 30 14 = true := by
  change case_41_30_14.check 41 30 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_30_15 : Certificate := {
  objectiveScale := 164
  eta := 29745716
  rows := #[⟨.assumptionRow 15, 255⟩]
  caps := #[0, 0, 8918030, 2761650, 868530, 278200, 91091, 30635, 10659, 1522299, 1095939, 530043] }

theorem case_41_30_15_checked :
    (Witness.linear .conditional case_41_30_15).check 41 30 15 = true := by
  change case_41_30_15.check 41 30 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_30_16 : Certificate := {
  objectiveScale := 1
  eta := 81719
  rows := #[⟨.assumptionRow 16, 1⟩]
  caps := #[0, 0, 28424, 9690, 3264, 1092, 364, 143, 28424, 25194, 15504, 7752] }

theorem case_41_30_16_checked :
    (Witness.linear .conditional case_41_30_16).check 41 30 16 = true := by
  change case_41_30_16.check 41 30 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_30_17 : Certificate := {
  objectiveScale := 929
  eta := 11844030
  rows := #[⟨.assumptionRow 17, 591⟩]
  caps := #[0, 0, 5144421, 1961256, 790704, 335328, 122850, 60307, 33639804, 32477650, 22102890, 12441960] }

theorem case_41_30_17_checked :
    (Witness.linear .conditional case_41_30_17).check 41 30 17 = true := by
  change case_41_30_17.check 41 30 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_30_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 58786, 58786, 41990, 25194] }

theorem case_41_30_18_checked :
    (Witness.linear .negative case_41_30_18).check 41 30 18 = true := by
  change case_41_30_18.check 41 30 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_30_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16796, 16796] }

theorem case_41_30_19_checked :
    (Witness.linear .negative case_41_30_19).check 41 30 19 = true := by
  change case_41_30_19.check 41 30 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_31_1_checked :
    (Witness.rising).check 41 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_31_2_checked :
    (Witness.rising).check 41 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_31_3_checked :
    (Witness.rising).check 41 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_31_4_checked :
    (Witness.rising).check 41 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_31_5_checked :
    (Witness.rising).check 41 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_31_6_checked :
    (Witness.rising).check 41 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_31_7_checked :
    (Witness.rising).check 41 31 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_31_8_checked :
    (Witness.rising).check 41 31 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_31_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_41_31_9_checked :
    (Witness.linear .positive case_41_31_9).check 41 31 9 = true := by
  change case_41_31_9.check 41 31 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_31_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_41_31_10_checked :
    (Witness.linear .positive case_41_31_10).check 41 31 10 = true := by
  change case_41_31_10.check 41 31 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_41_31_11_checked :
    (Witness.linear .positive case_41_31_11).check 41 31 11 = true := by
  change case_41_31_11.check 41 31 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_41_31_12_checked :
    (Witness.linear .positive case_41_31_12).check 41 31 12 = true := by
  change case_41_31_12.check 41 31 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_31_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_41_31_13_checked :
    (Witness.linear .positive case_41_31_13).check 41 31 13 = true := by
  change case_41_31_13.check 41 31 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_31_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_41_31_14_checked :
    (Witness.linear .positive case_41_31_14).check 41 31 14 = true := by
  change case_41_31_14.check 41 31 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_31_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_41_31_15_checked :
    (Witness.linear .positive case_41_31_15).check 41 31 15 = true := by
  change case_41_31_15.check 41 31 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_31_16 : Certificate := {
  objectiveScale := 365
  eta := 63822539
  rows := #[⟨.assumptionRow 16, 417⟩]
  caps := #[0, 0, 19612560, 6056250, 2017458, 690404, 236964, 81939, 17079271, 14464263, 8493285] }

theorem case_41_31_16_checked :
    (Witness.linear .conditional case_41_31_16).check 41 31 16 = true := by
  change case_41_31_16.check 41 31 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_31_17 : Certificate := {
  objectiveScale := 983
  eta := 77166771
  rows := #[⟨.assumptionRow 17, 804⟩]
  caps := #[0, 0, 25677531, 9155112, 3457392, 1231888, 422422, 178633, 58510804, 54652246, 35866566] }

theorem case_41_31_17_checked :
    (Witness.linear .conditional case_41_31_17).check 41 31 17 = true := by
  change case_41_31_17.check 41 31 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_31_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 208012, 208012, 149226, 90440] }

theorem case_41_31_18_checked :
    (Witness.linear .negative case_41_31_18).check 41 31 18 = true := by
  change case_41_31_18.check 41 31 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_31_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 58786, 58786] }

theorem case_41_31_19_checked :
    (Witness.linear .negative case_41_31_19).check 41 31 19 = true := by
  change case_41_31_19.check 41 31 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_31_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_41_31_20_checked :
    (Witness.linear .negative case_41_31_20).check 41 31 20 = true := by
  change case_41_31_20.check 41 31 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_32_1_checked :
    (Witness.rising).check 41 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_32_2_checked :
    (Witness.rising).check 41 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_32_3_checked :
    (Witness.rising).check 41 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_32_4_checked :
    (Witness.rising).check 41 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_32_5_checked :
    (Witness.rising).check 41 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_32_6_checked :
    (Witness.rising).check 41 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_32_7_checked :
    (Witness.rising).check 41 32 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_32_8_checked :
    (Witness.rising).check 41 32 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_32_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_41_32_9_checked :
    (Witness.linear .positive case_41_32_9).check 41 32 9 = true := by
  change case_41_32_9.check 41 32 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_32_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_41_32_10_checked :
    (Witness.linear .positive case_41_32_10).check 41 32 10 = true := by
  change case_41_32_10.check 41 32 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_41_32_11_checked :
    (Witness.linear .positive case_41_32_11).check 41 32 11 = true := by
  change case_41_32_11.check 41 32 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_41_32_12_checked :
    (Witness.linear .positive case_41_32_12).check 41 32 12 = true := by
  change case_41_32_12.check 41 32 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_32_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_41_32_13_checked :
    (Witness.linear .positive case_41_32_13).check 41 32 13 = true := by
  change case_41_32_13.check 41 32 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_32_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_41_32_14_checked :
    (Witness.linear .positive case_41_32_14).check 41 32 14 = true := by
  change case_41_32_14.check 41 32 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_32_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_41_32_15_checked :
    (Witness.linear .positive case_41_32_15).check 41 32 15 = true := by
  change case_41_32_15.check 41 32 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_32_16 : Certificate := {
  objectiveScale := 2
  eta := 1114350
  rows := #[⟨.assumptionRow 16, 3⟩]
  caps := #[0, 0, 326876, 96900, 29070, 9282, 3016, 1001, 341, 57684] }

theorem case_41_32_16_checked :
    (Witness.linear .conditional case_41_32_16).check 41 32 16 = true := by
  change case_41_32_16.check 41 32 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_32_17 : Certificate := {
  objectiveScale := 999
  eta := 68076734
  rows := #[⟨.assumptionRow 17, 799⟩]
  caps := #[0, 0, 23396505, 7736496, 3093048, 1140020, 482885, 208049145, 196043881, 130668681] }

theorem case_41_32_17_checked :
    (Witness.linear .conditional case_41_32_17).check 41 32 17 = true := by
  change case_41_32_17.check 41 32 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_32_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 742900, 742900, 534888, 326876] }

theorem case_41_32_18_checked :
    (Witness.linear .negative case_41_32_18).check 41 32 18 = true := by
  change case_41_32_18.check 41 32 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_32_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 208012, 208012] }

theorem case_41_32_19_checked :
    (Witness.linear .negative case_41_32_19).check 41 32 19 = true := by
  change case_41_32_19.check 41 32 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_32_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_41_32_20_checked :
    (Witness.linear .negative case_41_32_20).check 41 32 20 = true := by
  change case_41_32_20.check 41 32 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_33_1_checked :
    (Witness.rising).check 41 33 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_33_2_checked :
    (Witness.rising).check 41 33 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_33_3_checked :
    (Witness.rising).check 41 33 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_33_4_checked :
    (Witness.rising).check 41 33 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_33_5_checked :
    (Witness.rising).check 41 33 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_33_6_checked :
    (Witness.rising).check 41 33 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_33_7_checked :
    (Witness.rising).check 41 33 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_33_8_checked :
    (Witness.rising).check 41 33 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_33_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1] }

theorem case_41_33_9_checked :
    (Witness.linear .positive case_41_33_9).check 41 33 9 = true := by
  change case_41_33_9.check 41 33 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_33_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_41_33_10_checked :
    (Witness.linear .positive case_41_33_10).check 41 33 10 = true := by
  change case_41_33_10.check 41 33 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_33_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_41_33_11_checked :
    (Witness.linear .positive case_41_33_11).check 41 33 11 = true := by
  change case_41_33_11.check 41 33 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_33_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_41_33_12_checked :
    (Witness.linear .positive case_41_33_12).check 41 33 12 = true := by
  change case_41_33_12.check 41 33 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_33_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_41_33_13_checked :
    (Witness.linear .positive case_41_33_13).check 41 33 13 = true := by
  change case_41_33_13.check 41 33 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_33_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_41_33_14_checked :
    (Witness.linear .positive case_41_33_14).check 41 33 14 = true := by
  change case_41_33_14.check 41 33 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_33_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_41_33_15_checked :
    (Witness.linear .positive case_41_33_15).check 41 33 15 = true := by
  change case_41_33_15.check 41 33 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_33_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_41_33_16_checked :
    (Witness.linear .positive case_41_33_16).check 41 33 16 = true := by
  change case_41_33_16.check 41 33 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_33_17 : Certificate := {
  objectiveScale := 287
  eta := 56265935
  rows := #[⟨.assumptionRow 17, 271⟩]
  caps := #[0, 0, 18223337, 5835318, 2005830, 724608, 255645, 100212840, 91260895] }

theorem case_41_33_17_checked :
    (Witness.linear .conditional case_41_33_17).check 41 33 17 = true := by
  change case_41_33_17.check 41 33 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_33_18 : Certificate := {
  objectiveScale := 993
  eta := 27875793
  rows := #[⟨.assumptionRow 18, 611⟩]
  caps := #[0, 0, 10672794, 4214181, 1775208, 638588, 334305, 442805545, 431364885] }

theorem case_41_33_18_checked :
    (Witness.linear .conditional case_41_33_18).check 41 33 18 = true := by
  change case_41_33_18.check 41 33 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_33_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 742900, 742900] }

theorem case_41_33_19_checked :
    (Witness.linear .negative case_41_33_19).check 41 33 19 = true := by
  change case_41_33_19.check 41 33 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_33_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_41_33_20_checked :
    (Witness.linear .negative case_41_33_20).check 41 33 20 = true := by
  change case_41_33_20.check 41 33 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_33_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_41_33_21_checked :
    (Witness.linear .negative case_41_33_21).check 41 33 21 = true := by
  change case_41_33_21.check 41 33 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_34_1_checked :
    (Witness.rising).check 41 34 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_34_2_checked :
    (Witness.rising).check 41 34 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_34_3_checked :
    (Witness.rising).check 41 34 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_34_4_checked :
    (Witness.rising).check 41 34 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_34_5_checked :
    (Witness.rising).check 41 34 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_34_6_checked :
    (Witness.rising).check 41 34 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_34_7_checked :
    (Witness.rising).check 41 34 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_34_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1] }

theorem case_41_34_8_checked :
    (Witness.linear .positive case_41_34_8).check 41 34 8 = true := by
  change case_41_34_8.check 41 34 8 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_34_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_41_34_9_checked :
    (Witness.linear .positive case_41_34_9).check 41 34 9 = true := by
  change case_41_34_9.check 41 34 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_34_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_41_34_10_checked :
    (Witness.linear .positive case_41_34_10).check 41 34 10 = true := by
  change case_41_34_10.check 41 34 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_34_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_41_34_11_checked :
    (Witness.linear .positive case_41_34_11).check 41 34 11 = true := by
  change case_41_34_11.check 41 34 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_34_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_41_34_12_checked :
    (Witness.linear .positive case_41_34_12).check 41 34 12 = true := by
  change case_41_34_12.check 41 34 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_34_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42] }

theorem case_41_34_13_checked :
    (Witness.linear .positive case_41_34_13).check 41 34 13 = true := by
  change case_41_34_13.check 41 34 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_34_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_41_34_14_checked :
    (Witness.linear .positive case_41_34_14).check 41 34 14 = true := by
  change case_41_34_14.check 41 34 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_34_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_41_34_15_checked :
    (Witness.linear .positive case_41_34_15).check 41 34 15 = true := by
  change case_41_34_15.check 41 34 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_34_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_41_34_16_checked :
    (Witness.linear .positive case_41_34_16).check 41 34 16 = true := by
  change case_41_34_16.check 41 34 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_34_17 : Certificate := {
  objectiveScale := 5
  eta := 46527390
  rows := #[⟨.assumptionRow 17, 13⟩]
  caps := #[0, 0, 13037895, 3714500, 1069776, 312018, 92378, 27846] }

theorem case_41_34_17_checked :
    (Witness.linear .conditional case_41_34_17).check 41 34 17 = true := by
  change case_41_34_17.check 41 34 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_34_18 : Certificate := {
  objectiveScale := 957
  eta := 23809071
  rows := #[⟨.assumptionRow 18, 581⟩]
  caps := #[0, 0, 9532908, 3574641, 1589160, 585548, 1519986510, 1485553095] }

theorem case_41_34_18_checked :
    (Witness.linear .conditional case_41_34_18).check 41 34 18 = true := by
  change case_41_34_18.check 41 34 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_34_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 2674440, 2674440] }

theorem case_41_34_19_checked :
    (Witness.linear .negative case_41_34_19).check 41 34 19 = true := by
  change case_41_34_19.check 41 34 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_34_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_41_34_20_checked :
    (Witness.linear .negative case_41_34_20).check 41 34 20 = true := by
  change case_41_34_20.check 41 34 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_34_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_41_34_21_checked :
    (Witness.linear .negative case_41_34_21).check 41 34 21 = true := by
  change case_41_34_21.check 41 34 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_34_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_41_34_22_checked :
    (Witness.linear .negative case_41_34_22).check 41 34 22 = true := by
  change case_41_34_22.check 41 34 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_35_1_checked :
    (Witness.rising).check 41 35 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_35_2_checked :
    (Witness.rising).check 41 35 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_35_3_checked :
    (Witness.rising).check 41 35 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_35_4_checked :
    (Witness.rising).check 41 35 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_35_5_checked :
    (Witness.rising).check 41 35 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_35_6_checked :
    (Witness.rising).check 41 35 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_35_7_checked :
    (Witness.rising).check 41 35 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_35_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1] }

theorem case_41_35_8_checked :
    (Witness.linear .positive case_41_35_8).check 41 35 8 = true := by
  change case_41_35_8.check 41 35 8 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_35_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_41_35_9_checked :
    (Witness.linear .positive case_41_35_9).check 41 35 9 = true := by
  change case_41_35_9.check 41 35 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_35_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_41_35_10_checked :
    (Witness.linear .positive case_41_35_10).check 41 35 10 = true := by
  change case_41_35_10.check 41 35 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_35_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_41_35_11_checked :
    (Witness.linear .positive case_41_35_11).check 41 35 11 = true := by
  change case_41_35_11.check 41 35 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_35_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_41_35_12_checked :
    (Witness.linear .positive case_41_35_12).check 41 35 12 = true := by
  change case_41_35_12.check 41 35 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_35_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_41_35_13_checked :
    (Witness.linear .positive case_41_35_13).check 41 35 13 = true := by
  change case_41_35_13.check 41 35 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_35_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429] }

theorem case_41_35_14_checked :
    (Witness.linear .positive case_41_35_14).check 41 35 14 = true := by
  change case_41_35_14.check 41 35 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_35_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430] }

theorem case_41_35_15_checked :
    (Witness.linear .positive case_41_35_15).check 41 35 15 = true := by
  change case_41_35_15.check 41 35 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_35_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862] }

theorem case_41_35_16_checked :
    (Witness.linear .positive case_41_35_16).check 41 35 16 = true := by
  change case_41_35_16.check 41 35 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_35_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796] }

theorem case_41_35_17_checked :
    (Witness.linear .positive case_41_35_17).check 41 35 17 = true := by
  change case_41_35_17.check 41 35 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_35_18 : Certificate := {
  objectiveScale := 398
  eta := 56001550
  rows := #[⟨.assumptionRow 18, 307⟩]
  caps := #[0, 0, 20646065, 7631844, 2643432, 969000, 1044572025] }

theorem case_41_35_18_checked :
    (Witness.linear .conditional case_41_35_18).check 41 35 18 = true := by
  change case_41_35_18.check 41 35 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_35_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 9694845, 9694845] }

theorem case_41_35_19_checked :
    (Witness.linear .negative case_41_35_19).check 41 35 19 = true := by
  change case_41_35_19.check 41 35 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_35_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_41_35_20_checked :
    (Witness.linear .negative case_41_35_20).check 41 35 20 = true := by
  change case_41_35_20.check 41 35 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_35_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_41_35_21_checked :
    (Witness.linear .negative case_41_35_21).check 41 35 21 = true := by
  change case_41_35_21.check 41 35 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_35_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_41_35_22_checked :
    (Witness.linear .negative case_41_35_22).check 41 35 22 = true := by
  change case_41_35_22.check 41 35 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_36_1_checked :
    (Witness.rising).check 41 36 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_36_2_checked :
    (Witness.rising).check 41 36 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_36_3_checked :
    (Witness.rising).check 41 36 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_36_4_checked :
    (Witness.rising).check 41 36 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_36_5_checked :
    (Witness.rising).check 41 36 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_36_6_checked :
    (Witness.rising).check 41 36 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_36_7_checked :
    (Witness.rising).check 41 36 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_36_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2] }

theorem case_41_36_8_checked :
    (Witness.linear .positive case_41_36_8).check 41 36 8 = true := by
  change case_41_36_8.check 41 36 8 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_36_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_41_36_9_checked :
    (Witness.linear .positive case_41_36_9).check 41 36 9 = true := by
  change case_41_36_9.check 41 36 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_36_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_41_36_10_checked :
    (Witness.linear .positive case_41_36_10).check 41 36 10 = true := by
  change case_41_36_10.check 41 36 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_36_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_41_36_11_checked :
    (Witness.linear .positive case_41_36_11).check 41 36 11 = true := by
  change case_41_36_11.check 41 36 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_36_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_41_36_12_checked :
    (Witness.linear .positive case_41_36_12).check 41 36 12 = true := by
  change case_41_36_12.check 41 36 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_36_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_41_36_13_checked :
    (Witness.linear .positive case_41_36_13).check 41 36 13 = true := by
  change case_41_36_13.check 41 36 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_36_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_41_36_14_checked :
    (Witness.linear .positive case_41_36_14).check 41 36 14 = true := by
  change case_41_36_14.check 41 36 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_36_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862] }

theorem case_41_36_15_checked :
    (Witness.linear .positive case_41_36_15).check 41 36 15 = true := by
  change case_41_36_15.check 41 36 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_36_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796] }

theorem case_41_36_16_checked :
    (Witness.linear .positive case_41_36_16).check 41 36 16 = true := by
  change case_41_36_16.check 41 36 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_36_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786] }

theorem case_41_36_17_checked :
    (Witness.linear .positive case_41_36_17).check 41 36 17 = true := by
  change case_41_36_17.check 41 36 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_36_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012] }

theorem case_41_36_18_checked :
    (Witness.linear .positive case_41_36_18).check 41 36 18 = true := by
  change case_41_36_18.check 41 36 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_36_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 35357670, 35357670] }

theorem case_41_36_19_checked :
    (Witness.linear .negative case_41_36_19).check 41 36 19 = true := by
  change case_41_36_19.check 41 36 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_36_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_41_36_20_checked :
    (Witness.linear .negative case_41_36_20).check 41 36 20 = true := by
  change case_41_36_20.check 41 36 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_36_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_41_36_21_checked :
    (Witness.linear .negative case_41_36_21).check 41 36 21 = true := by
  change case_41_36_21.check 41 36 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_36_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_41_36_22_checked :
    (Witness.linear .negative case_41_36_22).check 41 36 22 = true := by
  change case_41_36_22.check 41 36 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_36_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_41_36_23_checked :
    (Witness.linear .negative case_41_36_23).check 41 36 23 = true := by
  change case_41_36_23.check 41 36 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_37_1_checked :
    (Witness.rising).check 41 37 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_37_2_checked :
    (Witness.rising).check 41 37 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_37_3_checked :
    (Witness.rising).check 41 37 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_37_4_checked :
    (Witness.rising).check 41 37 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_37_5_checked :
    (Witness.rising).check 41 37 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_37_6_checked :
    (Witness.rising).check 41 37 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_37_7_checked :
    (Witness.rising).check 41 37 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_37_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5] }

theorem case_41_37_8_checked :
    (Witness.linear .positive case_41_37_8).check 41 37 8 = true := by
  change case_41_37_8.check 41 37 8 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_37_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_41_37_9_checked :
    (Witness.linear .positive case_41_37_9).check 41 37 9 = true := by
  change case_41_37_9.check 41 37 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_37_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_41_37_10_checked :
    (Witness.linear .positive case_41_37_10).check 41 37 10 = true := by
  change case_41_37_10.check 41 37 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_37_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_41_37_11_checked :
    (Witness.linear .positive case_41_37_11).check 41 37 11 = true := by
  change case_41_37_11.check 41 37 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_37_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_41_37_12_checked :
    (Witness.linear .positive case_41_37_12).check 41 37 12 = true := by
  change case_41_37_12.check 41 37 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_37_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_41_37_13_checked :
    (Witness.linear .positive case_41_37_13).check 41 37 13 = true := by
  change case_41_37_13.check 41 37 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_37_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_41_37_14_checked :
    (Witness.linear .positive case_41_37_14).check 41 37 14 = true := by
  change case_41_37_14.check 41 37 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_37_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796] }

theorem case_41_37_15_checked :
    (Witness.linear .positive case_41_37_15).check 41 37 15 = true := by
  change case_41_37_15.check 41 37 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_37_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786] }

theorem case_41_37_16_checked :
    (Witness.linear .positive case_41_37_16).check 41 37 16 = true := by
  change case_41_37_16.check 41 37 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_37_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012] }

theorem case_41_37_17_checked :
    (Witness.linear .positive case_41_37_17).check 41 37 17 = true := by
  change case_41_37_17.check 41 37 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_37_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900] }

theorem case_41_37_18_checked :
    (Witness.linear .positive case_41_37_18).check 41 37 18 = true := by
  change case_41_37_18.check 41 37 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_37_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 129644790, 129644790] }

theorem case_41_37_19_checked :
    (Witness.linear .negative case_41_37_19).check 41 37 19 = true := by
  change case_41_37_19.check 41 37 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_37_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_41_37_20_checked :
    (Witness.linear .negative case_41_37_20).check 41 37 20 = true := by
  change case_41_37_20.check 41 37 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_37_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_41_37_21_checked :
    (Witness.linear .negative case_41_37_21).check 41 37 21 = true := by
  change case_41_37_21.check 41 37 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_37_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_41_37_22_checked :
    (Witness.linear .negative case_41_37_22).check 41 37 22 = true := by
  change case_41_37_22.check 41 37 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_37_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_41_37_23_checked :
    (Witness.linear .negative case_41_37_23).check 41 37 23 = true := by
  change case_41_37_23.check 41 37 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_37_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_41_37_24_checked :
    (Witness.linear .negative case_41_37_24).check 41 37 24 = true := by
  change case_41_37_24.check 41 37 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_38_1_checked :
    (Witness.rising).check 41 38 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_38_2_checked :
    (Witness.rising).check 41 38 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_38_3_checked :
    (Witness.rising).check 41 38 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_38_4_checked :
    (Witness.rising).check 41 38 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_38_5_checked :
    (Witness.rising).check 41 38 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_38_6_checked :
    (Witness.rising).check 41 38 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_38_7_checked :
    (Witness.rising).check 41 38 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_38_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14] }

theorem case_41_38_8_checked :
    (Witness.linear .positive case_41_38_8).check 41 38 8 = true := by
  change case_41_38_8.check 41 38 8 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_38_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_41_38_9_checked :
    (Witness.linear .positive case_41_38_9).check 41 38 9 = true := by
  change case_41_38_9.check 41 38 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_38_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_41_38_10_checked :
    (Witness.linear .positive case_41_38_10).check 41 38 10 = true := by
  change case_41_38_10.check 41 38 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_38_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_41_38_11_checked :
    (Witness.linear .positive case_41_38_11).check 41 38 11 = true := by
  change case_41_38_11.check 41 38 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_38_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_41_38_12_checked :
    (Witness.linear .positive case_41_38_12).check 41 38 12 = true := by
  change case_41_38_12.check 41 38 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_38_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_41_38_13_checked :
    (Witness.linear .positive case_41_38_13).check 41 38 13 = true := by
  change case_41_38_13.check 41 38 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_38_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_41_38_14_checked :
    (Witness.linear .positive case_41_38_14).check 41 38 14 = true := by
  change case_41_38_14.check 41 38 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_38_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_41_38_15_checked :
    (Witness.linear .positive case_41_38_15).check 41 38 15 = true := by
  change case_41_38_15.check 41 38 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_38_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012] }

theorem case_41_38_16_checked :
    (Witness.linear .positive case_41_38_16).check 41 38 16 = true := by
  change case_41_38_16.check 41 38 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_38_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900] }

theorem case_41_38_17_checked :
    (Witness.linear .positive case_41_38_17).check 41 38 17 = true := by
  change case_41_38_17.check 41 38 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_38_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440] }

theorem case_41_38_18_checked :
    (Witness.linear .positive case_41_38_18).check 41 38 18 = true := by
  change case_41_38_18.check 41 38 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_38_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845] }

theorem case_41_38_19_checked :
    (Witness.linear .positive case_41_38_19).check 41 38 19 = true := by
  change case_41_38_19.check 41 38 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_38_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_41_38_20_checked :
    (Witness.linear .negative case_41_38_20).check 41 38 20 = true := by
  change case_41_38_20.check 41 38 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_38_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_41_38_21_checked :
    (Witness.linear .negative case_41_38_21).check 41 38 21 = true := by
  change case_41_38_21.check 41 38 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_38_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_41_38_22_checked :
    (Witness.linear .negative case_41_38_22).check 41 38 22 = true := by
  change case_41_38_22.check 41 38 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_38_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_41_38_23_checked :
    (Witness.linear .negative case_41_38_23).check 41 38 23 = true := by
  change case_41_38_23.check 41 38 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_38_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_41_38_24_checked :
    (Witness.linear .negative case_41_38_24).check 41 38 24 = true := by
  change case_41_38_24.check 41 38 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_39_1_checked :
    (Witness.rising).check 41 39 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_39_2_checked :
    (Witness.rising).check 41 39 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_39_3_checked :
    (Witness.rising).check 41 39 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_39_4_checked :
    (Witness.rising).check 41 39 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_39_5_checked :
    (Witness.rising).check 41 39 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_39_6_checked :
    (Witness.rising).check 41 39 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_39_7_checked :
    (Witness.rising).check 41 39 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_39_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_41_39_8_checked :
    (Witness.linear .positive case_41_39_8).check 41 39 8 = true := by
  change case_41_39_8.check 41 39 8 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_39_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_41_39_9_checked :
    (Witness.linear .positive case_41_39_9).check 41 39 9 = true := by
  change case_41_39_9.check 41 39 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_39_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_41_39_10_checked :
    (Witness.linear .positive case_41_39_10).check 41 39 10 = true := by
  change case_41_39_10.check 41 39 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_39_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_41_39_11_checked :
    (Witness.linear .positive case_41_39_11).check 41 39 11 = true := by
  change case_41_39_11.check 41 39 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_39_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_41_39_12_checked :
    (Witness.linear .positive case_41_39_12).check 41 39 12 = true := by
  change case_41_39_12.check 41 39 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_39_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_41_39_13_checked :
    (Witness.linear .positive case_41_39_13).check 41 39 13 = true := by
  change case_41_39_13.check 41 39 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_39_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_41_39_14_checked :
    (Witness.linear .positive case_41_39_14).check 41 39 14 = true := by
  change case_41_39_14.check 41 39 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_39_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_41_39_15_checked :
    (Witness.linear .positive case_41_39_15).check 41 39 15 = true := by
  change case_41_39_15.check 41 39 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_39_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900] }

theorem case_41_39_16_checked :
    (Witness.linear .positive case_41_39_16).check 41 39 16 = true := by
  change case_41_39_16.check 41 39 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_39_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440] }

theorem case_41_39_17_checked :
    (Witness.linear .positive case_41_39_17).check 41 39 17 = true := by
  change case_41_39_17.check 41 39 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_39_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845] }

theorem case_41_39_18_checked :
    (Witness.linear .positive case_41_39_18).check 41 39 18 = true := by
  change case_41_39_18.check 41 39 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_39_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670] }

theorem case_41_39_19_checked :
    (Witness.linear .positive case_41_39_19).check 41 39 19 = true := by
  change case_41_39_19.check 41 39 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_39_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_41_39_20_checked :
    (Witness.linear .negative case_41_39_20).check 41 39 20 = true := by
  change case_41_39_20.check 41 39 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_39_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_41_39_21_checked :
    (Witness.linear .negative case_41_39_21).check 41 39 21 = true := by
  change case_41_39_21.check 41 39 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_39_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_41_39_22_checked :
    (Witness.linear .negative case_41_39_22).check 41 39 22 = true := by
  change case_41_39_22.check 41 39 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_39_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_41_39_23_checked :
    (Witness.linear .negative case_41_39_23).check 41 39 23 = true := by
  change case_41_39_23.check 41 39 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_39_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_41_39_24_checked :
    (Witness.linear .negative case_41_39_24).check 41 39 24 = true := by
  change case_41_39_24.check 41 39 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_39_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_41_39_25_checked :
    (Witness.linear .negative case_41_39_25).check 41 39 25 = true := by
  change case_41_39_25.check 41 39 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_40_1_checked :
    (Witness.rising).check 41 40 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_40_2_checked :
    (Witness.rising).check 41 40 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_40_3_checked :
    (Witness.rising).check 41 40 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_40_4_checked :
    (Witness.rising).check 41 40 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_40_5_checked :
    (Witness.rising).check 41 40 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_40_6_checked :
    (Witness.rising).check 41 40 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_41_40_7_checked :
    (Witness.rising).check 41 40 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_40_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_41_40_8_checked :
    (Witness.linear .positive case_41_40_8).check 41 40 8 = true := by
  change case_41_40_8.check 41 40 8 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_40_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_41_40_9_checked :
    (Witness.linear .positive case_41_40_9).check 41 40 9 = true := by
  change case_41_40_9.check 41 40 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_40_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_41_40_10_checked :
    (Witness.linear .positive case_41_40_10).check 41 40 10 = true := by
  change case_41_40_10.check 41 40 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_40_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_41_40_11_checked :
    (Witness.linear .positive case_41_40_11).check 41 40 11 = true := by
  change case_41_40_11.check 41 40 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_40_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_41_40_12_checked :
    (Witness.linear .positive case_41_40_12).check 41 40 12 = true := by
  change case_41_40_12.check 41 40 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_40_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_41_40_13_checked :
    (Witness.linear .positive case_41_40_13).check 41 40 13 = true := by
  change case_41_40_13.check 41 40 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_40_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_41_40_14_checked :
    (Witness.linear .positive case_41_40_14).check 41 40 14 = true := by
  change case_41_40_14.check 41 40 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_40_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_41_40_15_checked :
    (Witness.linear .positive case_41_40_15).check 41 40 15 = true := by
  change case_41_40_15.check 41 40 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_40_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_41_40_16_checked :
    (Witness.linear .positive case_41_40_16).check 41 40 16 = true := by
  change case_41_40_16.check 41 40 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_40_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0] }

theorem case_41_40_17_checked :
    (Witness.linear .positive case_41_40_17).check 41 40 17 = true := by
  change case_41_40_17.check 41 40 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_40_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0] }

theorem case_41_40_18_checked :
    (Witness.linear .positive case_41_40_18).check 41 40 18 = true := by
  change case_41_40_18.check 41 40 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_40_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0] }

theorem case_41_40_19_checked :
    (Witness.linear .positive case_41_40_19).check 41 40 19 = true := by
  change case_41_40_19.check 41 40 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_40_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0] }

theorem case_41_40_20_checked :
    (Witness.linear .positive case_41_40_20).check 41 40 20 = true := by
  change case_41_40_20.check 41 40 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_40_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_41_40_21_checked :
    (Witness.linear .negative case_41_40_21).check 41 40 21 = true := by
  change case_41_40_21.check 41 40 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_40_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_41_40_22_checked :
    (Witness.linear .negative case_41_40_22).check 41 40 22 = true := by
  change case_41_40_22.check 41 40 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_40_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_41_40_23_checked :
    (Witness.linear .negative case_41_40_23).check 41 40 23 = true := by
  change case_41_40_23.check 41 40 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_40_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_41_40_24_checked :
    (Witness.linear .negative case_41_40_24).check 41 40 24 = true := by
  change case_41_40_24.check 41 40 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_40_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_41_40_25_checked :
    (Witness.linear .negative case_41_40_25).check 41 40 25 = true := by
  change case_41_40_25.check 41 40 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_41_40_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_41_40_26_checked :
    (Witness.linear .negative case_41_40_26).check 41 40 26 = true := by
  change case_41_40_26.check 41 40 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_41 (a k : ℕ) (h : Domain 41 a k) :
    ∃ w : Witness, w.check 41 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 21 ≤ a := by omega
  have haHi : a ≤ 40 := by omega
  interval_cases a

  · have hkHi : k ≤ 13 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_41_21_1_checked⟩

    · exact ⟨Witness.rising, case_41_21_2_checked⟩

    · exact ⟨Witness.rising, case_41_21_3_checked⟩

    · exact ⟨Witness.rising, case_41_21_4_checked⟩

    · exact ⟨Witness.rising, case_41_21_5_checked⟩

    · exact ⟨Witness.rising, case_41_21_6_checked⟩

    · exact ⟨Witness.rising, case_41_21_7_checked⟩

    · exact ⟨Witness.rising, case_41_21_8_checked⟩

    · exact ⟨Witness.linear .positive case_41_21_9, case_41_21_9_checked⟩

    · exact ⟨Witness.linear .positive case_41_21_10, case_41_21_10_checked⟩

    · exact ⟨Witness.linear .positive case_41_21_11, case_41_21_11_checked⟩

    · exact ⟨Witness.linear .conditional case_41_21_12, case_41_21_12_checked⟩

    · exact ⟨Witness.linear .conditional case_41_21_13, case_41_21_13_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_41_22_1_checked⟩

    · exact ⟨Witness.rising, case_41_22_2_checked⟩

    · exact ⟨Witness.rising, case_41_22_3_checked⟩

    · exact ⟨Witness.rising, case_41_22_4_checked⟩

    · exact ⟨Witness.rising, case_41_22_5_checked⟩

    · exact ⟨Witness.rising, case_41_22_6_checked⟩

    · exact ⟨Witness.rising, case_41_22_7_checked⟩

    · exact ⟨Witness.rising, case_41_22_8_checked⟩

    · exact ⟨Witness.linear .positive case_41_22_9, case_41_22_9_checked⟩

    · exact ⟨Witness.linear .positive case_41_22_10, case_41_22_10_checked⟩

    · exact ⟨Witness.linear .positive case_41_22_11, case_41_22_11_checked⟩

    · exact ⟨Witness.linear .conditional case_41_22_12, case_41_22_12_checked⟩

    · exact ⟨Witness.linear .conditional case_41_22_13, case_41_22_13_checked⟩

    · exact ⟨Witness.linear .conditional case_41_22_14, case_41_22_14_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_41_23_1_checked⟩

    · exact ⟨Witness.rising, case_41_23_2_checked⟩

    · exact ⟨Witness.rising, case_41_23_3_checked⟩

    · exact ⟨Witness.rising, case_41_23_4_checked⟩

    · exact ⟨Witness.rising, case_41_23_5_checked⟩

    · exact ⟨Witness.rising, case_41_23_6_checked⟩

    · exact ⟨Witness.rising, case_41_23_7_checked⟩

    · exact ⟨Witness.rising, case_41_23_8_checked⟩

    · exact ⟨Witness.linear .positive case_41_23_9, case_41_23_9_checked⟩

    · exact ⟨Witness.linear .positive case_41_23_10, case_41_23_10_checked⟩

    · exact ⟨Witness.linear .positive case_41_23_11, case_41_23_11_checked⟩

    · exact ⟨Witness.linear .conditional case_41_23_12, case_41_23_12_checked⟩

    · exact ⟨Witness.linear .conditional case_41_23_13, case_41_23_13_checked⟩

    · exact ⟨Witness.linear .conditional case_41_23_14, case_41_23_14_checked⟩

  · have hkHi : k ≤ 15 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_41_24_1_checked⟩

    · exact ⟨Witness.rising, case_41_24_2_checked⟩

    · exact ⟨Witness.rising, case_41_24_3_checked⟩

    · exact ⟨Witness.rising, case_41_24_4_checked⟩

    · exact ⟨Witness.rising, case_41_24_5_checked⟩

    · exact ⟨Witness.rising, case_41_24_6_checked⟩

    · exact ⟨Witness.rising, case_41_24_7_checked⟩

    · exact ⟨Witness.rising, case_41_24_8_checked⟩

    · exact ⟨Witness.linear .positive case_41_24_9, case_41_24_9_checked⟩

    · exact ⟨Witness.linear .positive case_41_24_10, case_41_24_10_checked⟩

    · exact ⟨Witness.linear .positive case_41_24_11, case_41_24_11_checked⟩

    · exact ⟨Witness.linear .positive case_41_24_12, case_41_24_12_checked⟩

    · exact ⟨Witness.linear .conditional case_41_24_13, case_41_24_13_checked⟩

    · exact ⟨Witness.linear .conditional case_41_24_14, case_41_24_14_checked⟩

    · exact ⟨Witness.linear .negative case_41_24_15, case_41_24_15_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_41_25_1_checked⟩

    · exact ⟨Witness.rising, case_41_25_2_checked⟩

    · exact ⟨Witness.rising, case_41_25_3_checked⟩

    · exact ⟨Witness.rising, case_41_25_4_checked⟩

    · exact ⟨Witness.rising, case_41_25_5_checked⟩

    · exact ⟨Witness.rising, case_41_25_6_checked⟩

    · exact ⟨Witness.rising, case_41_25_7_checked⟩

    · exact ⟨Witness.rising, case_41_25_8_checked⟩

    · exact ⟨Witness.linear .positive case_41_25_9, case_41_25_9_checked⟩

    · exact ⟨Witness.linear .positive case_41_25_10, case_41_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_41_25_11, case_41_25_11_checked⟩

    · exact ⟨Witness.linear .positive case_41_25_12, case_41_25_12_checked⟩

    · exact ⟨Witness.linear .conditional case_41_25_13, case_41_25_13_checked⟩

    · exact ⟨Witness.linear .conditional case_41_25_14, case_41_25_14_checked⟩

    · exact ⟨Witness.linear .conditional case_41_25_15, case_41_25_15_checked⟩

    · exact ⟨Witness.linear .negative case_41_25_16, case_41_25_16_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_41_26_1_checked⟩

    · exact ⟨Witness.rising, case_41_26_2_checked⟩

    · exact ⟨Witness.rising, case_41_26_3_checked⟩

    · exact ⟨Witness.rising, case_41_26_4_checked⟩

    · exact ⟨Witness.rising, case_41_26_5_checked⟩

    · exact ⟨Witness.rising, case_41_26_6_checked⟩

    · exact ⟨Witness.rising, case_41_26_7_checked⟩

    · exact ⟨Witness.rising, case_41_26_8_checked⟩

    · exact ⟨Witness.linear .positive case_41_26_9, case_41_26_9_checked⟩

    · exact ⟨Witness.linear .positive case_41_26_10, case_41_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_41_26_11, case_41_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_41_26_12, case_41_26_12_checked⟩

    · exact ⟨Witness.linear .conditional case_41_26_13, case_41_26_13_checked⟩

    · exact ⟨Witness.linear .conditional case_41_26_14, case_41_26_14_checked⟩

    · exact ⟨Witness.linear .conditional case_41_26_15, case_41_26_15_checked⟩

    · exact ⟨Witness.linear .negative case_41_26_16, case_41_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_41_27_1_checked⟩

    · exact ⟨Witness.rising, case_41_27_2_checked⟩

    · exact ⟨Witness.rising, case_41_27_3_checked⟩

    · exact ⟨Witness.rising, case_41_27_4_checked⟩

    · exact ⟨Witness.rising, case_41_27_5_checked⟩

    · exact ⟨Witness.rising, case_41_27_6_checked⟩

    · exact ⟨Witness.rising, case_41_27_7_checked⟩

    · exact ⟨Witness.rising, case_41_27_8_checked⟩

    · exact ⟨Witness.linear .positive case_41_27_9, case_41_27_9_checked⟩

    · exact ⟨Witness.linear .positive case_41_27_10, case_41_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_41_27_11, case_41_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_41_27_12, case_41_27_12_checked⟩

    · exact ⟨Witness.linear .positive case_41_27_13, case_41_27_13_checked⟩

    · exact ⟨Witness.linear .conditional case_41_27_14, case_41_27_14_checked⟩

    · exact ⟨Witness.linear .conditional case_41_27_15, case_41_27_15_checked⟩

    · exact ⟨Witness.linear .negative case_41_27_16, case_41_27_16_checked⟩

    · exact ⟨Witness.linear .negative case_41_27_17, case_41_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_41_28_1_checked⟩

    · exact ⟨Witness.rising, case_41_28_2_checked⟩

    · exact ⟨Witness.rising, case_41_28_3_checked⟩

    · exact ⟨Witness.rising, case_41_28_4_checked⟩

    · exact ⟨Witness.rising, case_41_28_5_checked⟩

    · exact ⟨Witness.rising, case_41_28_6_checked⟩

    · exact ⟨Witness.rising, case_41_28_7_checked⟩

    · exact ⟨Witness.rising, case_41_28_8_checked⟩

    · exact ⟨Witness.linear .positive case_41_28_9, case_41_28_9_checked⟩

    · exact ⟨Witness.linear .positive case_41_28_10, case_41_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_41_28_11, case_41_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_41_28_12, case_41_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_41_28_13, case_41_28_13_checked⟩

    · exact ⟨Witness.linear .conditional case_41_28_14, case_41_28_14_checked⟩

    · exact ⟨Witness.linear .conditional case_41_28_15, case_41_28_15_checked⟩

    · exact ⟨Witness.linear .negative case_41_28_16, case_41_28_16_checked⟩

    · exact ⟨Witness.linear .negative case_41_28_17, case_41_28_17_checked⟩

    · exact ⟨Witness.linear .negative case_41_28_18, case_41_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_41_29_1_checked⟩

    · exact ⟨Witness.rising, case_41_29_2_checked⟩

    · exact ⟨Witness.rising, case_41_29_3_checked⟩

    · exact ⟨Witness.rising, case_41_29_4_checked⟩

    · exact ⟨Witness.rising, case_41_29_5_checked⟩

    · exact ⟨Witness.rising, case_41_29_6_checked⟩

    · exact ⟨Witness.rising, case_41_29_7_checked⟩

    · exact ⟨Witness.rising, case_41_29_8_checked⟩

    · exact ⟨Witness.linear .positive case_41_29_9, case_41_29_9_checked⟩

    · exact ⟨Witness.linear .positive case_41_29_10, case_41_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_41_29_11, case_41_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_41_29_12, case_41_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_41_29_13, case_41_29_13_checked⟩

    · exact ⟨Witness.linear .conditional case_41_29_14, case_41_29_14_checked⟩

    · exact ⟨Witness.linear .conditional case_41_29_15, case_41_29_15_checked⟩

    · exact ⟨Witness.linear .conditional case_41_29_16, case_41_29_16_checked⟩

    · exact ⟨Witness.linear .conditional case_41_29_17, case_41_29_17_checked⟩

    · exact ⟨Witness.linear .negative case_41_29_18, case_41_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_41_30_1_checked⟩

    · exact ⟨Witness.rising, case_41_30_2_checked⟩

    · exact ⟨Witness.rising, case_41_30_3_checked⟩

    · exact ⟨Witness.rising, case_41_30_4_checked⟩

    · exact ⟨Witness.rising, case_41_30_5_checked⟩

    · exact ⟨Witness.rising, case_41_30_6_checked⟩

    · exact ⟨Witness.rising, case_41_30_7_checked⟩

    · exact ⟨Witness.rising, case_41_30_8_checked⟩

    · exact ⟨Witness.linear .positive case_41_30_9, case_41_30_9_checked⟩

    · exact ⟨Witness.linear .positive case_41_30_10, case_41_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_41_30_11, case_41_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_41_30_12, case_41_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_41_30_13, case_41_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_41_30_14, case_41_30_14_checked⟩

    · exact ⟨Witness.linear .conditional case_41_30_15, case_41_30_15_checked⟩

    · exact ⟨Witness.linear .conditional case_41_30_16, case_41_30_16_checked⟩

    · exact ⟨Witness.linear .conditional case_41_30_17, case_41_30_17_checked⟩

    · exact ⟨Witness.linear .negative case_41_30_18, case_41_30_18_checked⟩

    · exact ⟨Witness.linear .negative case_41_30_19, case_41_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_41_31_1_checked⟩

    · exact ⟨Witness.rising, case_41_31_2_checked⟩

    · exact ⟨Witness.rising, case_41_31_3_checked⟩

    · exact ⟨Witness.rising, case_41_31_4_checked⟩

    · exact ⟨Witness.rising, case_41_31_5_checked⟩

    · exact ⟨Witness.rising, case_41_31_6_checked⟩

    · exact ⟨Witness.rising, case_41_31_7_checked⟩

    · exact ⟨Witness.rising, case_41_31_8_checked⟩

    · exact ⟨Witness.linear .positive case_41_31_9, case_41_31_9_checked⟩

    · exact ⟨Witness.linear .positive case_41_31_10, case_41_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_41_31_11, case_41_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_41_31_12, case_41_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_41_31_13, case_41_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_41_31_14, case_41_31_14_checked⟩

    · exact ⟨Witness.linear .positive case_41_31_15, case_41_31_15_checked⟩

    · exact ⟨Witness.linear .conditional case_41_31_16, case_41_31_16_checked⟩

    · exact ⟨Witness.linear .conditional case_41_31_17, case_41_31_17_checked⟩

    · exact ⟨Witness.linear .negative case_41_31_18, case_41_31_18_checked⟩

    · exact ⟨Witness.linear .negative case_41_31_19, case_41_31_19_checked⟩

    · exact ⟨Witness.linear .negative case_41_31_20, case_41_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_41_32_1_checked⟩

    · exact ⟨Witness.rising, case_41_32_2_checked⟩

    · exact ⟨Witness.rising, case_41_32_3_checked⟩

    · exact ⟨Witness.rising, case_41_32_4_checked⟩

    · exact ⟨Witness.rising, case_41_32_5_checked⟩

    · exact ⟨Witness.rising, case_41_32_6_checked⟩

    · exact ⟨Witness.rising, case_41_32_7_checked⟩

    · exact ⟨Witness.rising, case_41_32_8_checked⟩

    · exact ⟨Witness.linear .positive case_41_32_9, case_41_32_9_checked⟩

    · exact ⟨Witness.linear .positive case_41_32_10, case_41_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_41_32_11, case_41_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_41_32_12, case_41_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_41_32_13, case_41_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_41_32_14, case_41_32_14_checked⟩

    · exact ⟨Witness.linear .positive case_41_32_15, case_41_32_15_checked⟩

    · exact ⟨Witness.linear .conditional case_41_32_16, case_41_32_16_checked⟩

    · exact ⟨Witness.linear .conditional case_41_32_17, case_41_32_17_checked⟩

    · exact ⟨Witness.linear .negative case_41_32_18, case_41_32_18_checked⟩

    · exact ⟨Witness.linear .negative case_41_32_19, case_41_32_19_checked⟩

    · exact ⟨Witness.linear .negative case_41_32_20, case_41_32_20_checked⟩

  · have hkHi : k ≤ 21 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_41_33_1_checked⟩

    · exact ⟨Witness.rising, case_41_33_2_checked⟩

    · exact ⟨Witness.rising, case_41_33_3_checked⟩

    · exact ⟨Witness.rising, case_41_33_4_checked⟩

    · exact ⟨Witness.rising, case_41_33_5_checked⟩

    · exact ⟨Witness.rising, case_41_33_6_checked⟩

    · exact ⟨Witness.rising, case_41_33_7_checked⟩

    · exact ⟨Witness.rising, case_41_33_8_checked⟩

    · exact ⟨Witness.linear .positive case_41_33_9, case_41_33_9_checked⟩

    · exact ⟨Witness.linear .positive case_41_33_10, case_41_33_10_checked⟩

    · exact ⟨Witness.linear .positive case_41_33_11, case_41_33_11_checked⟩

    · exact ⟨Witness.linear .positive case_41_33_12, case_41_33_12_checked⟩

    · exact ⟨Witness.linear .positive case_41_33_13, case_41_33_13_checked⟩

    · exact ⟨Witness.linear .positive case_41_33_14, case_41_33_14_checked⟩

    · exact ⟨Witness.linear .positive case_41_33_15, case_41_33_15_checked⟩

    · exact ⟨Witness.linear .positive case_41_33_16, case_41_33_16_checked⟩

    · exact ⟨Witness.linear .conditional case_41_33_17, case_41_33_17_checked⟩

    · exact ⟨Witness.linear .conditional case_41_33_18, case_41_33_18_checked⟩

    · exact ⟨Witness.linear .negative case_41_33_19, case_41_33_19_checked⟩

    · exact ⟨Witness.linear .negative case_41_33_20, case_41_33_20_checked⟩

    · exact ⟨Witness.linear .negative case_41_33_21, case_41_33_21_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_41_34_1_checked⟩

    · exact ⟨Witness.rising, case_41_34_2_checked⟩

    · exact ⟨Witness.rising, case_41_34_3_checked⟩

    · exact ⟨Witness.rising, case_41_34_4_checked⟩

    · exact ⟨Witness.rising, case_41_34_5_checked⟩

    · exact ⟨Witness.rising, case_41_34_6_checked⟩

    · exact ⟨Witness.rising, case_41_34_7_checked⟩

    · exact ⟨Witness.linear .positive case_41_34_8, case_41_34_8_checked⟩

    · exact ⟨Witness.linear .positive case_41_34_9, case_41_34_9_checked⟩

    · exact ⟨Witness.linear .positive case_41_34_10, case_41_34_10_checked⟩

    · exact ⟨Witness.linear .positive case_41_34_11, case_41_34_11_checked⟩

    · exact ⟨Witness.linear .positive case_41_34_12, case_41_34_12_checked⟩

    · exact ⟨Witness.linear .positive case_41_34_13, case_41_34_13_checked⟩

    · exact ⟨Witness.linear .positive case_41_34_14, case_41_34_14_checked⟩

    · exact ⟨Witness.linear .positive case_41_34_15, case_41_34_15_checked⟩

    · exact ⟨Witness.linear .positive case_41_34_16, case_41_34_16_checked⟩

    · exact ⟨Witness.linear .conditional case_41_34_17, case_41_34_17_checked⟩

    · exact ⟨Witness.linear .conditional case_41_34_18, case_41_34_18_checked⟩

    · exact ⟨Witness.linear .negative case_41_34_19, case_41_34_19_checked⟩

    · exact ⟨Witness.linear .negative case_41_34_20, case_41_34_20_checked⟩

    · exact ⟨Witness.linear .negative case_41_34_21, case_41_34_21_checked⟩

    · exact ⟨Witness.linear .negative case_41_34_22, case_41_34_22_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_41_35_1_checked⟩

    · exact ⟨Witness.rising, case_41_35_2_checked⟩

    · exact ⟨Witness.rising, case_41_35_3_checked⟩

    · exact ⟨Witness.rising, case_41_35_4_checked⟩

    · exact ⟨Witness.rising, case_41_35_5_checked⟩

    · exact ⟨Witness.rising, case_41_35_6_checked⟩

    · exact ⟨Witness.rising, case_41_35_7_checked⟩

    · exact ⟨Witness.linear .positive case_41_35_8, case_41_35_8_checked⟩

    · exact ⟨Witness.linear .positive case_41_35_9, case_41_35_9_checked⟩

    · exact ⟨Witness.linear .positive case_41_35_10, case_41_35_10_checked⟩

    · exact ⟨Witness.linear .positive case_41_35_11, case_41_35_11_checked⟩

    · exact ⟨Witness.linear .positive case_41_35_12, case_41_35_12_checked⟩

    · exact ⟨Witness.linear .positive case_41_35_13, case_41_35_13_checked⟩

    · exact ⟨Witness.linear .positive case_41_35_14, case_41_35_14_checked⟩

    · exact ⟨Witness.linear .positive case_41_35_15, case_41_35_15_checked⟩

    · exact ⟨Witness.linear .positive case_41_35_16, case_41_35_16_checked⟩

    · exact ⟨Witness.linear .positive case_41_35_17, case_41_35_17_checked⟩

    · exact ⟨Witness.linear .conditional case_41_35_18, case_41_35_18_checked⟩

    · exact ⟨Witness.linear .negative case_41_35_19, case_41_35_19_checked⟩

    · exact ⟨Witness.linear .negative case_41_35_20, case_41_35_20_checked⟩

    · exact ⟨Witness.linear .negative case_41_35_21, case_41_35_21_checked⟩

    · exact ⟨Witness.linear .negative case_41_35_22, case_41_35_22_checked⟩

  · have hkHi : k ≤ 23 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_41_36_1_checked⟩

    · exact ⟨Witness.rising, case_41_36_2_checked⟩

    · exact ⟨Witness.rising, case_41_36_3_checked⟩

    · exact ⟨Witness.rising, case_41_36_4_checked⟩

    · exact ⟨Witness.rising, case_41_36_5_checked⟩

    · exact ⟨Witness.rising, case_41_36_6_checked⟩

    · exact ⟨Witness.rising, case_41_36_7_checked⟩

    · exact ⟨Witness.linear .positive case_41_36_8, case_41_36_8_checked⟩

    · exact ⟨Witness.linear .positive case_41_36_9, case_41_36_9_checked⟩

    · exact ⟨Witness.linear .positive case_41_36_10, case_41_36_10_checked⟩

    · exact ⟨Witness.linear .positive case_41_36_11, case_41_36_11_checked⟩

    · exact ⟨Witness.linear .positive case_41_36_12, case_41_36_12_checked⟩

    · exact ⟨Witness.linear .positive case_41_36_13, case_41_36_13_checked⟩

    · exact ⟨Witness.linear .positive case_41_36_14, case_41_36_14_checked⟩

    · exact ⟨Witness.linear .positive case_41_36_15, case_41_36_15_checked⟩

    · exact ⟨Witness.linear .positive case_41_36_16, case_41_36_16_checked⟩

    · exact ⟨Witness.linear .positive case_41_36_17, case_41_36_17_checked⟩

    · exact ⟨Witness.linear .positive case_41_36_18, case_41_36_18_checked⟩

    · exact ⟨Witness.linear .negative case_41_36_19, case_41_36_19_checked⟩

    · exact ⟨Witness.linear .negative case_41_36_20, case_41_36_20_checked⟩

    · exact ⟨Witness.linear .negative case_41_36_21, case_41_36_21_checked⟩

    · exact ⟨Witness.linear .negative case_41_36_22, case_41_36_22_checked⟩

    · exact ⟨Witness.linear .negative case_41_36_23, case_41_36_23_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_41_37_1_checked⟩

    · exact ⟨Witness.rising, case_41_37_2_checked⟩

    · exact ⟨Witness.rising, case_41_37_3_checked⟩

    · exact ⟨Witness.rising, case_41_37_4_checked⟩

    · exact ⟨Witness.rising, case_41_37_5_checked⟩

    · exact ⟨Witness.rising, case_41_37_6_checked⟩

    · exact ⟨Witness.rising, case_41_37_7_checked⟩

    · exact ⟨Witness.linear .positive case_41_37_8, case_41_37_8_checked⟩

    · exact ⟨Witness.linear .positive case_41_37_9, case_41_37_9_checked⟩

    · exact ⟨Witness.linear .positive case_41_37_10, case_41_37_10_checked⟩

    · exact ⟨Witness.linear .positive case_41_37_11, case_41_37_11_checked⟩

    · exact ⟨Witness.linear .positive case_41_37_12, case_41_37_12_checked⟩

    · exact ⟨Witness.linear .positive case_41_37_13, case_41_37_13_checked⟩

    · exact ⟨Witness.linear .positive case_41_37_14, case_41_37_14_checked⟩

    · exact ⟨Witness.linear .positive case_41_37_15, case_41_37_15_checked⟩

    · exact ⟨Witness.linear .positive case_41_37_16, case_41_37_16_checked⟩

    · exact ⟨Witness.linear .positive case_41_37_17, case_41_37_17_checked⟩

    · exact ⟨Witness.linear .positive case_41_37_18, case_41_37_18_checked⟩

    · exact ⟨Witness.linear .negative case_41_37_19, case_41_37_19_checked⟩

    · exact ⟨Witness.linear .negative case_41_37_20, case_41_37_20_checked⟩

    · exact ⟨Witness.linear .negative case_41_37_21, case_41_37_21_checked⟩

    · exact ⟨Witness.linear .negative case_41_37_22, case_41_37_22_checked⟩

    · exact ⟨Witness.linear .negative case_41_37_23, case_41_37_23_checked⟩

    · exact ⟨Witness.linear .negative case_41_37_24, case_41_37_24_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_41_38_1_checked⟩

    · exact ⟨Witness.rising, case_41_38_2_checked⟩

    · exact ⟨Witness.rising, case_41_38_3_checked⟩

    · exact ⟨Witness.rising, case_41_38_4_checked⟩

    · exact ⟨Witness.rising, case_41_38_5_checked⟩

    · exact ⟨Witness.rising, case_41_38_6_checked⟩

    · exact ⟨Witness.rising, case_41_38_7_checked⟩

    · exact ⟨Witness.linear .positive case_41_38_8, case_41_38_8_checked⟩

    · exact ⟨Witness.linear .positive case_41_38_9, case_41_38_9_checked⟩

    · exact ⟨Witness.linear .positive case_41_38_10, case_41_38_10_checked⟩

    · exact ⟨Witness.linear .positive case_41_38_11, case_41_38_11_checked⟩

    · exact ⟨Witness.linear .positive case_41_38_12, case_41_38_12_checked⟩

    · exact ⟨Witness.linear .positive case_41_38_13, case_41_38_13_checked⟩

    · exact ⟨Witness.linear .positive case_41_38_14, case_41_38_14_checked⟩

    · exact ⟨Witness.linear .positive case_41_38_15, case_41_38_15_checked⟩

    · exact ⟨Witness.linear .positive case_41_38_16, case_41_38_16_checked⟩

    · exact ⟨Witness.linear .positive case_41_38_17, case_41_38_17_checked⟩

    · exact ⟨Witness.linear .positive case_41_38_18, case_41_38_18_checked⟩

    · exact ⟨Witness.linear .positive case_41_38_19, case_41_38_19_checked⟩

    · exact ⟨Witness.linear .negative case_41_38_20, case_41_38_20_checked⟩

    · exact ⟨Witness.linear .negative case_41_38_21, case_41_38_21_checked⟩

    · exact ⟨Witness.linear .negative case_41_38_22, case_41_38_22_checked⟩

    · exact ⟨Witness.linear .negative case_41_38_23, case_41_38_23_checked⟩

    · exact ⟨Witness.linear .negative case_41_38_24, case_41_38_24_checked⟩

  · have hkHi : k ≤ 25 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_41_39_1_checked⟩

    · exact ⟨Witness.rising, case_41_39_2_checked⟩

    · exact ⟨Witness.rising, case_41_39_3_checked⟩

    · exact ⟨Witness.rising, case_41_39_4_checked⟩

    · exact ⟨Witness.rising, case_41_39_5_checked⟩

    · exact ⟨Witness.rising, case_41_39_6_checked⟩

    · exact ⟨Witness.rising, case_41_39_7_checked⟩

    · exact ⟨Witness.linear .positive case_41_39_8, case_41_39_8_checked⟩

    · exact ⟨Witness.linear .positive case_41_39_9, case_41_39_9_checked⟩

    · exact ⟨Witness.linear .positive case_41_39_10, case_41_39_10_checked⟩

    · exact ⟨Witness.linear .positive case_41_39_11, case_41_39_11_checked⟩

    · exact ⟨Witness.linear .positive case_41_39_12, case_41_39_12_checked⟩

    · exact ⟨Witness.linear .positive case_41_39_13, case_41_39_13_checked⟩

    · exact ⟨Witness.linear .positive case_41_39_14, case_41_39_14_checked⟩

    · exact ⟨Witness.linear .positive case_41_39_15, case_41_39_15_checked⟩

    · exact ⟨Witness.linear .positive case_41_39_16, case_41_39_16_checked⟩

    · exact ⟨Witness.linear .positive case_41_39_17, case_41_39_17_checked⟩

    · exact ⟨Witness.linear .positive case_41_39_18, case_41_39_18_checked⟩

    · exact ⟨Witness.linear .positive case_41_39_19, case_41_39_19_checked⟩

    · exact ⟨Witness.linear .negative case_41_39_20, case_41_39_20_checked⟩

    · exact ⟨Witness.linear .negative case_41_39_21, case_41_39_21_checked⟩

    · exact ⟨Witness.linear .negative case_41_39_22, case_41_39_22_checked⟩

    · exact ⟨Witness.linear .negative case_41_39_23, case_41_39_23_checked⟩

    · exact ⟨Witness.linear .negative case_41_39_24, case_41_39_24_checked⟩

    · exact ⟨Witness.linear .negative case_41_39_25, case_41_39_25_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_41_40_1_checked⟩

    · exact ⟨Witness.rising, case_41_40_2_checked⟩

    · exact ⟨Witness.rising, case_41_40_3_checked⟩

    · exact ⟨Witness.rising, case_41_40_4_checked⟩

    · exact ⟨Witness.rising, case_41_40_5_checked⟩

    · exact ⟨Witness.rising, case_41_40_6_checked⟩

    · exact ⟨Witness.rising, case_41_40_7_checked⟩

    · exact ⟨Witness.linear .positive case_41_40_8, case_41_40_8_checked⟩

    · exact ⟨Witness.linear .positive case_41_40_9, case_41_40_9_checked⟩

    · exact ⟨Witness.linear .positive case_41_40_10, case_41_40_10_checked⟩

    · exact ⟨Witness.linear .positive case_41_40_11, case_41_40_11_checked⟩

    · exact ⟨Witness.linear .positive case_41_40_12, case_41_40_12_checked⟩

    · exact ⟨Witness.linear .positive case_41_40_13, case_41_40_13_checked⟩

    · exact ⟨Witness.linear .positive case_41_40_14, case_41_40_14_checked⟩

    · exact ⟨Witness.linear .positive case_41_40_15, case_41_40_15_checked⟩

    · exact ⟨Witness.linear .positive case_41_40_16, case_41_40_16_checked⟩

    · exact ⟨Witness.linear .positive case_41_40_17, case_41_40_17_checked⟩

    · exact ⟨Witness.linear .positive case_41_40_18, case_41_40_18_checked⟩

    · exact ⟨Witness.linear .positive case_41_40_19, case_41_40_19_checked⟩

    · exact ⟨Witness.linear .positive case_41_40_20, case_41_40_20_checked⟩

    · exact ⟨Witness.linear .negative case_41_40_21, case_41_40_21_checked⟩

    · exact ⟨Witness.linear .negative case_41_40_22, case_41_40_22_checked⟩

    · exact ⟨Witness.linear .negative case_41_40_23, case_41_40_23_checked⟩

    · exact ⟨Witness.linear .negative case_41_40_24, case_41_40_24_checked⟩

    · exact ⟨Witness.linear .negative case_41_40_25, case_41_40_25_checked⟩

    · exact ⟨Witness.linear .negative case_41_40_26, case_41_40_26_checked⟩


#print axioms coverage_41
end ForestUnimodality.FiniteRows.FiniteData
