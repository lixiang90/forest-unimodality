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

theorem case_38_19_1_checked :
    (Witness.rising).check 38 19 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_19_2_checked :
    (Witness.rising).check 38 19 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_19_3_checked :
    (Witness.rising).check 38 19 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_19_4_checked :
    (Witness.rising).check 38 19 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_19_5_checked :
    (Witness.rising).check 38 19 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_19_6_checked :
    (Witness.rising).check 38 19 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_19_7_checked :
    (Witness.rising).check 38 19 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_19_8_checked :
    (Witness.rising).check 38 19 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_19_9 : Certificate := {
  objectiveScale := 820083000000
  eta := 0
  rows := #[⟨.count 2, 561258900602400⟩, ⟨.count 3, 252002320970400⟩, ⟨.count 4, 43254129718800⟩, ⟨.count 5, 9037396668300⟩, ⟨.count 6, 2417932717200⟩, ⟨.count 7, 976472828100⟩, ⟨.count 8, 819754966800⟩, ⟨.path 9, 152257322700⟩, ⟨.path 10, 175766152800⟩, ⟨.privateRow 8 2, 7835893065⟩, ⟨.privateRow 10 0, 17556784182⟩, ⟨.hall 8 1, 24183502140⟩, ⟨.hall 8 2, 1656070640⟩, ⟨.hall 0 3, 195897326625⟩, ⟨.hall 7 3, 3957521750⟩, ⟨.hall 0 4, 1744792189140⟩, ⟨.hall 1 4, 162688065540⟩, ⟨.hall 0 5, 638065578150⟩, ⟨.hall 6 5, 2209253900⟩, ⟨.hall 0 6, 123996549600⟩, ⟨.hall 5 9, 4420247370⟩, ⟨.hall 1 11, 3874892175⟩, ⟨.hall 4 12, 37658211360⟩, ⟨.hall 3 15, 430974118575⟩]
  caps := #[0, 122274375300, 2783186749200, 0, 67813145400, 0, 7028726400, 0, 5375285355, 0, 198310980, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_38_19_9_checked :
    (Witness.linear .positive case_38_19_9).check 38 19 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_19_10 : Certificate := {
  objectiveScale := 7200000
  eta := 0
  rows := #[⟨.count 2, 2107385280⟩, ⟨.count 3, 3874590720⟩, ⟨.count 4, 771891120⟩, ⟨.count 5, 180180000⟩, ⟨.count 6, 48494160⟩, ⟨.count 7, 16465680⟩, ⟨.count 8, 7207200⟩, ⟨.count 9, 7166880⟩, ⟨.path 11, 2066880⟩, ⟨.path 12, 172980⟩, ⟨.privateRow 8 4, 162855⟩, ⟨.privateRow 9 2, 58240⟩, ⟨.privateRow 11 0, 229600⟩, ⟨.privateRow 12 0, 20790⟩, ⟨.privateRow 12 3, 390852⟩, ⟨.hall 9 1, 253008⟩, ⟨.hall 9 2, 37296⟩, ⟨.hall 1 3, 144144⟩, ⟨.hall 8 3, 68292⟩, ⟨.hall 0 4, 39063024⟩, ⟨.hall 1 4, 3428568⟩, ⟨.hall 0 5, 10501920⟩, ⟨.hall 7 5, 43500⟩, ⟨.hall 6 7, 52620⟩, ⟨.hall 5 10, 210600⟩, ⟨.hall 4 13, 3675672⟩]
  caps := #[0, 167927760, 0, 0, 302940, 0, 80100, 1200, 0, 33120, 29520, 480, 6660, 0, 0, 0, 0, 0, 0, 0] }

theorem case_38_19_10_checked :
    (Witness.linear .positive case_38_19_10).check 38 19 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_19_11 : Certificate := {
  objectiveScale := 2800000
  eta := 220540320
  rows := #[⟨.count 2, 3210086880⟩, ⟨.count 3, 2002160160⟩, ⟨.count 4, 521080560⟩, ⟨.count 5, 139098960⟩, ⟨.count 6, 45405360⟩, ⟨.count 7, 16715160⟩, ⟨.count 8, 7428960⟩, ⟨.count 9, 4626720⟩, ⟨.count 10, 4626720⟩, ⟨.path 11, 933360⟩, ⟨.privateRow 4 15, 39999960⟩, ⟨.privateRow 12 0, 349965⟩, ⟨.hall 1 1, 2162160⟩, ⟨.hall 10 1, 398160⟩, ⟨.hall 9 2, 113526⟩, ⟨.hall 9 3, 38826⟩, ⟨.hall 10 3, 5310⟩, ⟨.hall 0 4, 26954928⟩, ⟨.hall 1 4, 1214928⟩, ⟨.hall 8 4, 83736⟩, ⟨.hall 7 6, 78705⟩, ⟨.hall 6 8, 125688⟩, ⟨.hall 5 11, 1085700⟩, ⟨.hall 4 13, 5709132⟩, ⟨.assumptionRow 11, 4646160⟩]
  caps := #[0, 22913280, 10433280, 2173600, 0, 120120, 120120, 35640, 34320, 19440, 64800, 0, 280, 0, 0, 0, 0, 0, 0, 0] }

theorem case_38_19_11_checked :
    (Witness.linear .conditional case_38_19_11).check 38 19 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_19_12 : Certificate := {
  objectiveScale := 2100000
  eta := 3087564480
  rows := #[⟨.count 2, 1641800160⟩, ⟨.count 3, 482161680⟩, ⟨.count 4, 155675520⟩, ⟨.count 5, 53333280⟩, ⟨.count 6, 20386080⟩, ⟨.count 7, 8607060⟩, ⟨.count 8, 4019400⟩, ⟨.count 9, 2041200⟩, ⟨.count 10, 1655640⟩, ⟨.count 11, 1275120⟩, ⟨.count 13, 2084940⟩, ⟨.path 10, 381780⟩, ⟨.privateRow 3 16, 59819760⟩, ⟨.hall 11 1, 114840⟩, ⟨.hall 10 2, 57420⟩, ⟨.hall 9 3, 11313⟩, ⟨.hall 10 3, 35190⟩, ⟨.hall 11 3, 4059⟩, ⟨.hall 0 4, 900900⟩, ⟨.hall 9 4, 69732⟩, ⟨.hall 8 5, 47600⟩, ⟨.hall 8 6, 44820⟩, ⟨.hall 7 7, 99414⟩, ⟨.hall 6 9, 294759⟩, ⟨.hall 7 9, 129969⟩, ⟨.hall 5 11, 1174140⟩, ⟨.hall 4 12, 698544⟩, ⟨.hall 4 13, 3261258⟩, ⟨.hall 3 15, 97567470⟩, ⟨.assumptionRow 12, 1273020⟩]
  caps := #[0, 64045800, 0, 300300, 240240, 0, 0, 27720, 0, 0, 0, 18900, 0, 15060, 0, 0, 0, 0, 0, 0] }

theorem case_38_19_12_checked :
    (Witness.linear .conditional case_38_19_12).check 38 19 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_20_1_checked :
    (Witness.rising).check 38 20 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_20_2_checked :
    (Witness.rising).check 38 20 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_20_3_checked :
    (Witness.rising).check 38 20 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_20_4_checked :
    (Witness.rising).check 38 20 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_20_5_checked :
    (Witness.rising).check 38 20 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_20_6_checked :
    (Witness.rising).check 38 20 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_20_7_checked :
    (Witness.rising).check 38 20 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_20_8_checked :
    (Witness.rising).check 38 20 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_20_9 : Certificate := {
  objectiveScale := 805411767600000
  eta := 6803007144445512000
  rows := #[⟨.count 2, 1518619996045152000⟩, ⟨.count 3, 233179996014365400⟩, ⟨.count 4, 42480316105587360⟩, ⟨.count 5, 9014973914746800⟩, ⟨.count 6, 2401737890983200⟩, ⟨.count 7, 966896827003800⟩, ⟨.count 8, 803654505561600⟩, ⟨.path 9, 158955657094080⟩, ⟨.path 10, 163181305399200⟩, ⟨.privateRow 6 8, 170747294731200⟩, ⟨.privateRow 6 9, 62016706105200⟩, ⟨.privateRow 7 4, 281894118660⟩, ⟨.privateRow 7 5, 66714941416200⟩, ⟨.privateRow 7 6, 94786897399425⟩, ⟨.privateRow 7 7, 99871059182400⟩, ⟨.privateRow 8 2, 29680422080400⟩, ⟨.privateRow 8 3, 47358211934880⟩, ⟨.privateRow 8 4, 4584338697400⟩, ⟨.privateRow 9 0, 26190526297320⟩, ⟨.privateRow 10 0, 14872826888640⟩, ⟨.hall 5 9, 1642551877560⟩, ⟨.hall 4 12, 15306850643238⟩, ⟨.hall 6 13, 306861883455600⟩, ⟨.hall 3 16, 4481619026484600⟩]
  caps := #[0, 0, 712358599043520, 30409250157000, 32607243108000, 0, 8089577992320, 1690308792150, 1757262038400, 1895481128640, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_38_20_9_checked :
    (Witness.linear .positive case_38_20_9).check 38 20 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_20_10 : Certificate := {
  objectiveScale := 53482000000
  eta := 629659031601600
  rows := #[⟨.count 2, 165815935084800⟩, ⟨.count 3, 29894699835000⟩, ⟨.count 4, 6034130182080⟩, ⟨.count 5, 1392895904400⟩, ⟨.count 6, 367934767200⟩, ⟨.count 7, 122644922400⟩, ⟨.count 8, 53174721600⟩, ⟨.count 9, 54032378400⟩, ⟨.path 11, 16537023360⟩, ⟨.privateRow 6 9, 12242029800⟩, ⟨.privateRow 7 6, 1600448850⟩, ⟨.privateRow 7 7, 13477464000⟩, ⟨.privateRow 7 8, 17633015400⟩, ⟨.privateRow 8 4, 4002398400⟩, ⟨.privateRow 8 5, 7370488125⟩, ⟨.privateRow 8 6, 10536926400⟩, ⟨.privateRow 8 7, 3895191300⟩, ⟨.privateRow 9 2, 4494121632⟩, ⟨.privateRow 9 3, 2630147520⟩, ⟨.privateRow 10 0, 2417032800⟩, ⟨.privateRow 11 0, 1650989340⟩, ⟨.hall 6 7, 8246700⟩, ⟨.hall 6 8, 148777200⟩, ⟨.hall 5 10, 620780160⟩, ⟨.hall 7 12, 3447120600⟩, ⟨.hall 4 13, 7723709994⟩, ⟨.hall 3 16, 362523961800⟩]
  caps := #[0, 0, 0, 58541397200, 3568319040, 0, 0, 1414598900, 307278400, 0, 0, 27129960, 0, 0, 0, 0, 0, 0, 0] }

theorem case_38_20_10_checked :
    (Witness.linear .positive case_38_20_10).check 38 20 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_20_11 : Certificate := {
  objectiveScale := 734400000
  eta := 16831343168640
  rows := #[⟨.count 2, 4602529451520⟩, ⟨.count 3, 978371994600⟩, ⟨.count 4, 226112638752⟩, ⟨.count 5, 61959577680⟩, ⟨.count 6, 17716739040⟩, ⟨.count 7, 6003597600⟩, ⟨.count 8, 2526189120⟩, ⟨.count 9, 1459575936⟩, ⟨.count 10, 1434625920⟩, ⟨.path 11, 315344016⟩, ⟨.privateRow 7 8, 722882160⟩, ⟨.privateRow 8 5, 47268585⟩, ⟨.privateRow 8 6, 383160960⟩, ⟨.privateRow 8 7, 830367720⟩, ⟨.privateRow 9 3, 56830592⟩, ⟨.privateRow 9 4, 61595352⟩, ⟨.privateRow 9 5, 770331744⟩, ⟨.privateRow 10 1, 53018784⟩, ⟨.privateRow 10 2, 172917472⟩, ⟨.privateRow 10 3, 45611748⟩, ⟨.privateRow 11 0, 98630532⟩, ⟨.privateRow 12 0, 81681600⟩, ⟨.hall 7 8, 11182192⟩, ⟨.hall 6 9, 31850928⟩, ⟨.hall 7 9, 6087564⟩, ⟨.hall 5 11, 112195512⟩, ⟨.hall 8 11, 379448160⟩, ⟨.hall 4 14, 3066123060⟩, ⟨.hall 3 16, 27939431520⟩, ⟨.assumptionRow 11, 1473132960⟩]
  caps := #[0, 0, 0, 674748360, 0, 38250000, 5647536, 7089425, 1020816, 38531248, 0, 298656, 0, 0, 0, 0, 0, 0, 0] }

theorem case_38_20_11_checked :
    (Witness.linear .conditional case_38_20_11).check 38 20 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_20_12 : Certificate := {
  objectiveScale := 109956000000
  eta := 775606489257600
  rows := #[⟨.count 2, 198194194598400⟩, ⟨.count 3, 57581791066800⟩, ⟨.count 4, 17513694918720⟩, ⟨.count 5, 5641666430400⟩, ⟨.count 6, 1940754816000⟩, ⟨.count 7, 731152422000⟩, ⟨.count 8, 308756448000⟩, ⟨.count 9, 135852837120⟩, ⟨.count 10, 116641324800⟩, ⟨.count 11, 94342248000⟩, ⟨.count 13, 105124219200⟩, ⟨.path 10, 21085521600⟩, ⟨.privateRow 3 17, 7787952572400⟩, ⟨.privateRow 7 8, 46609563000⟩, ⟨.privateRow 8 6, 17643225600⟩, ⟨.privateRow 8 7, 103347644400⟩, ⟨.privateRow 9 3, 800479680⟩, ⟨.privateRow 9 4, 4717112400⟩, ⟨.privateRow 9 5, 51263372160⟩, ⟨.privateRow 9 6, 107378631360⟩, ⟨.privateRow 10 3, 26973306360⟩, ⟨.privateRow 10 4, 61065164160⟩, ⟨.privateRow 10 5, 24643338720⟩, ⟨.privateRow 11 1, 13722508800⟩, ⟨.privateRow 11 2, 16992325350⟩, ⟨.privateRow 12 0, 6963356400⟩, ⟨.hall 7 7, 517251350⟩, ⟨.hall 8 7, 1049113520⟩, ⟨.hall 7 8, 4715646320⟩, ⟨.hall 8 8, 2455150880⟩, ⟨.hall 6 9, 1173791520⟩, ⟨.hall 6 10, 17136306000⟩, ⟨.hall 5 11, 25064874120⟩, ⟨.hall 4 13, 111168861804⟩, ⟨.hall 3 15, 698670247275⟩, ⟨.assumptionRow 12, 95220100800⟩]
  caps := #[0, 1317174144000, 0, 133715696400, 11796977280, 3971038500, 2560852800, 0, 1555989600, 3541570560, 0, 4695738300, 0, 4831780800, 0, 0, 0, 0, 0] }

theorem case_38_20_12_checked :
    (Witness.linear .conditional case_38_20_12).check 38 20 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_21_1_checked :
    (Witness.rising).check 38 21 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_21_2_checked :
    (Witness.rising).check 38 21 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_21_3_checked :
    (Witness.rising).check 38 21 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_21_4_checked :
    (Witness.rising).check 38 21 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_21_5_checked :
    (Witness.rising).check 38 21 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_21_6_checked :
    (Witness.rising).check 38 21 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_21_7_checked :
    (Witness.rising).check 38 21 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_21_8_checked :
    (Witness.rising).check 38 21 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_21_9 : Certificate := {
  objectiveScale := 9202050000
  eta := 96153619161600
  rows := #[⟨.count 2, 17844836209200⟩, ⟨.count 3, 2685923800560⟩, ⟨.count 4, 497587970880⟩, ⟨.count 5, 105124219200⟩, ⟨.count 6, 28302674400⟩, ⟨.count 7, 11149538400⟩, ⟨.count 8, 9262693440⟩, ⟨.path 9, 1909496160⟩, ⟨.path 10, 1794541320⟩, ⟨.privateRow 5 11, 2830267440⟩, ⟨.privateRow 5 12, 11536709184⟩, ⟨.privateRow 5 13, 6603957360⟩, ⟨.privateRow 6 8, 2091814725⟩, ⟨.privateRow 6 9, 2551091400⟩, ⟨.privateRow 6 10, 4698393700⟩, ⟨.privateRow 6 11, 4200476280⟩, ⟨.privateRow 7 5, 428828400⟩, ⟨.privateRow 7 6, 2191789600⟩, ⟨.privateRow 7 7, 1156305150⟩, ⟨.privateRow 8 2, 357357000⟩, ⟨.privateRow 8 3, 541883160⟩, ⟨.privateRow 9 0, 260962240⟩, ⟨.privateRow 10 0, 150089940⟩, ⟨.hall 4 14, 240480240⟩, ⟨.hall 4 15, 669909240⟩, ⟨.hall 3 16, 6893766880⟩]
  caps := #[0, 0, 3003549120, 0, 4282838560, 374631972, 262101125, 0, 0, 205692080, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_38_21_9_checked :
    (Witness.linear .positive case_38_21_9).check 38 21 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_21_10 : Certificate := {
  objectiveScale := 37026000000
  eta := 518542731907200
  rows := #[⟨.count 2, 104309506501200⟩, ⟨.count 3, 19316575278000⟩, ⟨.count 4, 4022753454720⟩, ⟨.count 5, 943422480000⟩, ⟨.count 6, 254724069600⟩, ⟨.count 7, 84050366400⟩, ⟨.count 8, 36021585600⟩, ⟨.count 9, 36021585600⟩, ⟨.path 10, 57477420⟩, ⟨.path 11, 11177812800⟩, ⟨.privateRow 5 12, 47925861984⟩, ⟨.privateRow 5 13, 100002782880⟩, ⟨.privateRow 6 9, 11568156600⟩, ⟨.privateRow 6 10, 34330095800⟩, ⟨.privateRow 6 11, 47171124000⟩, ⟨.privateRow 6 12, 64663749150⟩, ⟨.privateRow 7 6, 1477075600⟩, ⟨.privateRow 7 7, 12007195200⟩, ⟨.privateRow 7 8, 17765748000⟩, ⟨.privateRow 7 9, 22727905200⟩, ⟨.privateRow 7 10, 15952416480⟩, ⟨.privateRow 8 4, 3331996668⟩, ⟨.privateRow 8 5, 7237670440⟩, ⟨.privateRow 8 6, 9117963855⟩, ⟨.privateRow 9 2, 3978141440⟩, ⟨.privateRow 9 3, 907210304⟩, ⟨.privateRow 10 0, 1475884410⟩, ⟨.privateRow 11 0, 1013594400⟩, ⟨.hall 5 14, 5542607070⟩, ⟨.hall 4 15, 40490860410⟩, ⟨.hall 5 15, 41274733500⟩, ⟨.hall 3 16, 63126063000⟩]
  caps := #[0, 1557417232800, 0, 35337287700, 0, 2755950120, 0, 2486243760, 1135942416, 1004414400, 211017510, 28274400, 0, 0, 0, 0, 0, 0] }

theorem case_38_21_10_checked :
    (Witness.linear .positive case_38_21_10).check 38 21 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_21_11 : Certificate := {
  objectiveScale := 21780000
  eta := 366491885760
  rows := #[⟨.count 2, 84769284600⟩, ⟨.count 3, 21787509744⟩, ⟨.count 4, 5606625024⟩, ⟨.count 5, 1434953520⟩, ⟨.count 6, 428107680⟩, ⟨.count 7, 136216080⟩, ⟨.count 8, 48432384⟩, ⟨.count 9, 22198176⟩, ⟨.count 10, 22702680⟩, ⟨.path 12, 4356198⟩, ⟨.privateRow 11 2, 400400⟩, ⟨.privateRow 12 0, 462462⟩, ⟨.privateRow 13 0, 880880⟩, ⟨.hall 13 2, 920205⟩, ⟨.hall 10 3, 8736⟩, ⟨.hall 9 5, 8008⟩, ⟨.hall 7 8, 663880⟩, ⟨.hall 6 9, 476256⟩]
  caps := #[0, 0, 0, 15261246, 0, 2591820, 990990, 0, 0, 0, 0, 2695066, 0, 10570560, 0, 0, 0, 0] }

theorem case_38_21_11_checked :
    (Witness.linear .positive case_38_21_11).check 38 21 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_21_12 : Certificate := {
  objectiveScale := 732564000000
  eta := 9227803961376000
  rows := #[⟨.count 2, 2432784680726400⟩, ⟨.count 3, 656432418161520⟩, ⟨.count 4, 183357663128640⟩, ⟨.count 5, 53698259815200⟩, ⟨.count 6, 17861009166000⟩, ⟨.count 7, 6379680106800⟩, ⟨.count 8, 2522540180160⟩, ⟨.count 9, 1231938227520⟩, ⟨.count 10, 879955876800⟩, ⟨.count 11, 806626220400⟩, ⟨.count 13, 599208049440⟩, ⟨.path 10, 162777752280⟩, ⟨.privateRow 5 13, 8054738972280⟩, ⟨.privateRow 6 10, 12803590800⟩, ⟨.privateRow 6 11, 3568360755960⟩, ⟨.privateRow 6 12, 8714443988250⟩, ⟨.privateRow 7 8, 79315750800⟩, ⟨.privateRow 7 9, 1480560681600⟩, ⟨.privateRow 7 10, 3961896578640⟩, ⟨.privateRow 7 11, 5793042855600⟩, ⟨.privateRow 8 6, 46747655955⟩, ⟨.privateRow 8 7, 684060937560⟩, ⟨.privateRow 8 8, 1827130605300⟩, ⟨.privateRow 8 9, 2931719662872⟩, ⟨.privateRow 8 10, 2493208317600⟩, ⟨.privateRow 9 4, 10139409280⟩, ⟨.privateRow 9 5, 343019837160⟩, ⟨.privateRow 9 6, 932101410240⟩, ⟨.privateRow 9 7, 1472024954400⟩, ⟨.privateRow 10 3, 172732079520⟩, ⟨.privateRow 10 4, 531640008900⟩, ⟨.privateRow 10 5, 160277677560⟩, ⟨.privateRow 11 1, 104756652000⟩, ⟨.privateRow 11 2, 117560242800⟩, ⟨.privateRow 12 0, 46092926880⟩, ⟨.hall 6 11, 2616997680⟩, ⟨.hall 6 12, 211807973520⟩, ⟨.hall 5 13, 39919767030⟩, ⟨.hall 5 14, 3838196432070⟩, ⟨.hall 4 15, 7690570958070⟩, ⟨.hall 3 16, 10068065967960⟩, ⟨.hall 2 18, 128041298985600⟩, ⟨.assumptionRow 12, 752348460600⟩]
  caps := #[0, 0, 1568084637600, 866676198960, 0, 249232800960, 0, 0, 785748249, 79880184560, 35902900080, 0, 84034509480, 133355950560, 0, 0, 0, 0] }

theorem case_38_21_12_checked :
    (Witness.linear .conditional case_38_21_12).check 38 21 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_21_13 : Certificate := {
  objectiveScale := 35079716271600000
  eta := 324741633295836556800
  rows := #[⟨.count 2, 84767117514722042400⟩, ⟨.count 3, 22922938820882580480⟩, ⟨.count 4, 6668801398039500720⟩, ⟨.count 5, 1994211710607916800⟩, ⟨.count 6, 606791392208001000⟩, ⟨.count 7, 208724311816020000⟩, ⟨.count 8, 75140752253767200⟩, ⟨.count 9, 25046917417922400⟩, ⟨.count 10, 16697944945281600⟩, ⟨.count 11, 16399767356973000⟩, ⟨.count 12, 13119813885578400⟩, ⟨.count 14, 59695153179381720⟩, ⟨.path 8, 1272939825917760⟩, ⟨.path 9, 8875168216714800⟩, ⟨.privateRow 2 19, 8208083562164986500⟩, ⟨.privateRow 5 12, 15743776662694080⟩, ⟨.privateRow 5 13, 481825164947866740⟩, ⟨.privateRow 6 10, 6651016761439050⟩, ⟨.privateRow 6 11, 176461496761029480⟩, ⟨.privateRow 6 12, 504566175682869300⟩, ⟨.privateRow 7 9, 64704536662966200⟩, ⟨.privateRow 7 10, 206815975250844960⟩, ⟨.privateRow 7 11, 370411109076358350⟩, ⟨.privateRow 8 7, 20305893763815660⟩, ⟨.privateRow 8 8, 87038038027280340⟩, ⟨.privateRow 8 9, 174076076054560680⟩, ⟨.privateRow 8 10, 235388842650516555⟩, ⟨.privateRow 9 5, 5681939599436100⟩, ⟨.privateRow 9 6, 35277721781221920⟩, ⟨.privateRow 9 7, 77769132476635600⟩, ⟨.privateRow 9 8, 148685923101651936⟩, ⟨.privateRow 10 3, 371065443228480⟩, ⟨.privateRow 10 4, 14454158593259385⟩, ⟨.privateRow 10 5, 43653198928379040⟩, ⟨.privateRow 10 6, 41640500207295990⟩, ⟨.privateRow 11 2, 3180560941958400⟩, ⟨.privateRow 11 3, 23816934866149425⟩, ⟨.privateRow 11 4, 6133938959491200⟩, ⟨.privateRow 12 1, 9293201502284700⟩, ⟨.privateRow 13 0, 2186635647596400⟩, ⟨.hall 6 12, 451744507415520⟩, ⟨.hall 6 13, 135321508934108640⟩, ⟨.hall 7 13, 404776076128924500⟩, ⟨.hall 5 14, 304215684471849150⟩, ⟨.hall 4 15, 525154314997186875⟩, ⟨.hall 3 16, 730192674347796660⟩, ⟨.hall 2 18, 11860484381692947000⟩, ⟨.assumptionRow 13, 16053631135579800⟩]
  caps := #[0, 0, 49052351665131360, 11158183935858960, 2909299885957080, 0, 2103411865204650, 935364647843640, 0, 183351982557128, 0, 2769990711244650, 2933817250001400, 0, 0, 0, 0, 0] }

theorem case_38_21_13_checked :
    (Witness.linear .conditional case_38_21_13).check 38 21 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_22_1_checked :
    (Witness.rising).check 38 22 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_22_2_checked :
    (Witness.rising).check 38 22 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_22_3_checked :
    (Witness.rising).check 38 22 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_22_4_checked :
    (Witness.rising).check 38 22 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_22_5_checked :
    (Witness.rising).check 38 22 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_22_6_checked :
    (Witness.rising).check 38 22 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_22_7_checked :
    (Witness.rising).check 38 22 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_22_8_checked :
    (Witness.rising).check 38 22 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_22_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_38_22_9_checked :
    (Witness.linear .positive case_38_22_9).check 38 22 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_22_10 : Certificate := {
  objectiveScale := 943800000
  eta := 25648119396900
  rows := #[⟨.count 2, 5251246760760⟩, ⟨.count 3, 1079275317120⟩, ⟨.count 4, 243402999840⟩, ⟨.count 5, 55426070700⟩, ⟨.count 6, 13293680400⟩, ⟨.count 7, 3752248500⟩, ⟨.count 8, 1334132800⟩, ⟨.count 9, 900539640⟩, ⟨.path 10, 377541780⟩, ⟨.privateRow 7 13, 4945820880⟩, ⟨.privateRow 8 11, 1596790195⟩, ⟨.hall 8 5, 13178060⟩, ⟨.hall 7 6, 5474476⟩, ⟨.hall 6 10, 3213000⟩]
  caps := #[0, 0, 5917248480, 681046080, 0, 74857860, 0, 61678617, 0, 43260360, 0, 0, 0, 0, 0, 0, 0] }

theorem case_38_22_10_checked :
    (Witness.linear .positive case_38_22_10).check 38 22 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_22_11 : Certificate := {
  objectiveScale := 272250000
  eta := 6622825809600
  rows := #[⟨.count 2, 1618912975680⟩, ⟨.count 3, 388959611040⟩, ⟨.count 4, 103911247440⟩, ⟨.count 5, 27965737800⟩, ⟨.count 6, 7627019400⟩, ⟨.count 7, 2251349100⟩, ⟨.count 8, 800479680⟩, ⟨.count 9, 321621300⟩, ⟨.count 10, 275675400⟩, ⟨.path 11, 60501210⟩, ⟨.hall 11 2, 3675672⟩, ⟨.hall 12 2, 11231220⟩, ⟨.hall 10 3, 487305⟩, ⟨.hall 9 4, 5295024⟩, ⟨.hall 8 7, 1109080⟩, ⟨.hall 6 10, 9095850⟩, ⟨.hall 9 11, 25564770⟩]
  caps := #[0, 0, 0, 373461660, 0, 0, 0, 17419050, 0, 62290800, 0, 2665410, 36756720, 0, 0, 0, 0] }

theorem case_38_22_11_checked :
    (Witness.linear .positive case_38_22_11).check 38 22 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_22_12 : Certificate := {
  objectiveScale := 122094000000
  eta := 3082925414368800
  rows := #[⟨.count 2, 699076057680000⟩, ⟨.count 3, 180960830930880⟩, ⟨.count 4, 47567900540160⟩, ⟨.count 5, 12829197981600⟩, ⟨.count 6, 3855044793600⟩, ⟨.count 7, 1290601952640⟩, ⟨.count 8, 469309800960⟩, ⟨.count 9, 175991175360⟩, ⟨.count 10, 125707982400⟩, ⟨.count 11, 76821544800⟩, ⟨.path 9, 47965048560⟩, ⟨.privateRow 2 20, 33555650768640⟩, ⟨.privateRow 4 15, 2350739270880⟩, ⟨.privateRow 4 16, 9233949684960⟩, ⟨.privateRow 5 13, 1702365432768⟩, ⟨.privateRow 5 14, 3883329089640⟩, ⟨.privateRow 5 15, 7303168192320⟩, ⟨.privateRow 6 11, 900907207200⟩, ⟨.privateRow 6 12, 1780863084000⟩, ⟨.privateRow 6 13, 3160159002000⟩, ⟨.privateRow 6 14, 3631563936000⟩, ⟨.privateRow 7 8, 26189163000⟩, ⟨.privateRow 7 9, 404061372000⟩, ⟨.privateRow 7 10, 861798057120⟩, ⟨.privateRow 7 11, 1222719642144⟩, ⟨.privateRow 7 12, 2287885279680⟩, ⟨.privateRow 8 6, 23900036160⟩, ⟨.privateRow 8 7, 191064493620⟩, ⟨.privateRow 8 8, 420888948480⟩, ⟨.privateRow 8 9, 782726184240⟩, ⟨.privateRow 8 10, 338294148192⟩, ⟨.privateRow 9 4, 13362292944⟩, ⟨.privateRow 9 5, 101756214560⟩, ⟨.privateRow 9 6, 224470225980⟩, ⟨.privateRow 9 7, 244897773120⟩, ⟨.privateRow 10 2, 2666532960⟩, ⟨.privateRow 10 3, 62015937984⟩, ⟨.privateRow 10 4, 103825481760⟩, ⟨.privateRow 11 1, 34918884000⟩, ⟨.privateRow 11 2, 5587021440⟩, ⟨.privateRow 12 0, 8380532160⟩, ⟨.hall 5 16, 4170957991200⟩, ⟨.hall 4 17, 17382154870080⟩, ⟨.hall 3 18, 40115402046720⟩, ⟨.hall 2 19, 62217769133520⟩, ⟨.assumptionRow 12, 129668945175⟩]
  caps := #[0, 10424295893700, 1363811433660, 409074726060, 0, 3538446912, 46935088200, 0, 0, 7219655872, 32466231, 24856004250, 0, 122094000000, 0, 0, 0] }

theorem case_38_22_12_checked :
    (Witness.linear .conditional case_38_22_12).check 38 22 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_22_13 : Certificate := {
  objectiveScale := 191389364469759960000
  eta := 7064266610846029166782200
  rows := #[⟨.count 2, 1463731696651753411842960⟩, ⟨.count 3, 338257324856497637190600⟩, ⟨.count 4, 77242232096919231582240⟩, ⟨.count 5, 17561569101471057663000⟩, ⟨.count 6, 4105301867876351142000⟩, ⟨.count 7, 1040009806528675622640⟩, ⟨.count 8, 316260292043807791680⟩, ⟨.count 9, 109474716476702697120⟩, ⟨.count 10, 117294339082181461200⟩, ⟨.count 11, 143359747767110674800⟩, ⟨.count 12, 172031697320532809760⟩, ⟨.path 7, 166087250028827127000⟩, ⟨.path 8, 67178447637269928960⟩, ⟨.privateRow 2 20, 65228685234035357034000⟩, ⟨.privateRow 4 15, 4333048376260920145830⟩, ⟨.privateRow 4 16, 17360865454597102718280⟩, ⟨.privateRow 5 13, 2815585446146053653072⟩, ⟨.privateRow 5 14, 6949363773010689960930⟩, ⟨.privateRow 5 15, 14469777207960370776480⟩, ⟨.privateRow 6 11, 1285893495123174537600⟩, ⟨.privateRow 6 12, 2981882753555902035840⟩, ⟨.privateRow 6 13, 6073240223588506768800⟩, ⟨.privateRow 6 14, 8138923861869146946600⟩, ⟨.privateRow 7 9, 501572935694280724560⟩, ⟨.privateRow 7 10, 1311090056851939444080⟩, ⟨.privateRow 7 11, 2756416968431264338200⟩, ⟨.privateRow 7 12, 3896126963179794202860⟩, ⟨.privateRow 7 13, 3830311806250347938520⟩, ⟨.privateRow 8 7, 172574726668135501710⟩, ⟨.privateRow 8 8, 576479955415017774120⟩, ⟨.privateRow 8 9, 924959988749918621500⟩, ⟨.privateRow 8 10, 2893781672200841293872⟩, ⟨.privateRow 8 11, 361114516155790146750⟩, ⟨.privateRow 9 5, 47641774763009507080⟩, ⟨.privateRow 9 6, 248978955875834259075⟩, ⟨.privateRow 9 7, 693774294497199235320⟩, ⟨.privateRow 9 8, 888975243982113568280⟩, ⟨.privateRow 10 3, 2345886781643629224⟩, ⟨.privateRow 10 4, 102089517349306086600⟩, ⟨.privateRow 10 5, 370943347347398871045⟩, ⟨.privateRow 10 6, 195490565136969102000⟩, ⟨.privateRow 11 2, 16942515645203988840⟩, ⟨.privateRow 11 3, 192594408616421411600⟩, ⟨.privateRow 12 1, 55910301629173163172⟩, ⟨.privateRow 13 0, 12902377299039960732⟩, ⟨.hall 5 15, 355237022040561010350⟩, ⟨.hall 6 15, 58647169541090730600⟩, ⟨.hall 5 16, 8491956823616497030800⟩, ⟨.hall 4 17, 40886200063179964452960⟩, ⟨.hall 3 18, 84336276036426466132080⟩, ⟨.hall 2 19, 125630447760752097647484⟩, ⟨.assumptionRow 13, 111586834820315405250⟩]
  caps := #[0, 0, 274991753568233749320, 110678250314567808600, 226379116920555348750, 17905593289469709978, 0, 52485937409403283500, 7663950103224968700, 2675856222979456118, 2428594328432346921, 0, 0, 0, 191389364469759960000, 0, 0] }

theorem case_38_22_13_checked :
    (Witness.linear .conditional case_38_22_13).check 38 22 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_22_14 : Certificate := {
  objectiveScale := 1170400000
  eta := 21607805419200
  rows := #[⟨.count 2, 5507871969600⟩, ⟨.count 3, 1538875217880⟩, ⟨.count 4, 439977938400⟩, ⟨.count 5, 128617889400⟩, ⟨.count 6, 38410772400⟩, ⟨.count 7, 11554976160⟩, ⟨.count 8, 3555377280⟩, ⟨.count 9, 1111055400⟩, ⟨.count 10, 317444400⟩, ⟨.path 9, 228880080⟩, ⟨.path 10, 226698120⟩, ⟨.privateRow 2 20, 688483996200⟩, ⟨.privateRow 4 15, 7332965640⟩, ⟨.privateRow 4 16, 103825481760⟩, ⟨.privateRow 5 13, 4492896408⟩, ⟨.privateRow 5 14, 38032484490⟩, ⟨.privateRow 5 15, 97734076440⟩, ⟨.privateRow 6 11, 1878212700⟩, ⟨.privateRow 6 12, 14232090600⟩, ⟨.privateRow 6 13, 39521827800⟩, ⟨.privateRow 6 14, 64776293400⟩, ⟨.privateRow 7 9, 621284040⟩, ⟨.privateRow 7 10, 5348938140⟩, ⟨.privateRow 7 11, 16405526592⟩, ⟨.privateRow 7 12, 29760412500⟩, ⟨.privateRow 7 13, 37066924440⟩, ⟨.privateRow 8 7, 141968190⟩, ⟨.privateRow 8 8, 1961100960⟩, ⟨.privateRow 8 9, 6979073920⟩, ⟨.privateRow 8 10, 11046359688⟩, ⟨.privateRow 8 11, 26788780200⟩, ⟨.privateRow 8 12, 2839363800⟩, ⟨.privateRow 9 6, 657374445⟩, ⟨.privateRow 9 7, 3005140320⟩, ⟨.privateRow 9 8, 7254780260⟩, ⟨.privateRow 9 9, 9797039616⟩, ⟨.privateRow 10 4, 134032080⟩, ⟨.privateRow 10 5, 1253905380⟩, ⟨.privateRow 10 6, 3841077240⟩, ⟨.privateRow 10 7, 3153281040⟩, ⟨.privateRow 11 3, 399744800⟩, ⟨.privateRow 11 4, 2063388600⟩, ⟨.privateRow 11 5, 642447000⟩, ⟨.privateRow 12 2, 944103160⟩, ⟨.privateRow 12 3, 87297210⟩, ⟨.privateRow 13 1, 310390080⟩, ⟨.privateRow 14 0, 168127960⟩, ⟨.hall 6 15, 37002112875⟩, ⟨.hall 5 16, 150014264400⟩, ⟨.hall 4 17, 336850834320⟩, ⟨.hall 3 18, 602791829640⟩, ⟨.hall 2 19, 830417620032⟩]
  caps := #[0, 0, 6062412840, 572308880, 161498480, 149468440, 722203300, 15539720, 4208386, 24617160, 122774580, 0, 0, 3549296520, 0, 1170400000, 0] }

theorem case_38_22_14_checked :
    (Witness.linear .negative case_38_22_14).check 38 22 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_23_1_checked :
    (Witness.rising).check 38 23 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_23_2_checked :
    (Witness.rising).check 38 23 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_23_3_checked :
    (Witness.rising).check 38 23 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_23_4_checked :
    (Witness.rising).check 38 23 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_23_5_checked :
    (Witness.rising).check 38 23 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_23_6_checked :
    (Witness.rising).check 38 23 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_23_7_checked :
    (Witness.rising).check 38 23 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_23_8_checked :
    (Witness.rising).check 38 23 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_23_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_38_23_9_checked :
    (Witness.linear .positive case_38_23_9).check 38 23 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_23_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_38_23_10_checked :
    (Witness.linear .positive case_38_23_10).check 38 23 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_23_11 : Certificate := {
  objectiveScale := 550000
  eta := 34802487720
  rows := #[⟨.count 2, 7831806840⟩, ⟨.count 3, 1857224160⟩, ⟨.count 4, 424654560⟩, ⟨.count 5, 108721800⟩, ⟨.count 6, 27558360⟩, ⟨.count 7, 7596960⟩, ⟨.count 8, 2441880⟩, ⟨.count 9, 1046520⟩, ⟨.count 10, 581400⟩, ⟨.path 9, 329967⟩]
  caps := #[0, 10197110, 0, 0, 12969, 167310, 158868, 102545, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_38_23_11_checked :
    (Witness.linear .positive case_38_23_11).check 38 23 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_23_12 : Certificate := {
  objectiveScale := 7215916862000000
  eta := 455140575557918490240
  rows := #[⟨.count 2, 93343224099811205520⟩, ⟨.count 3, 19778836200568885440⟩, ⟨.count 4, 4736311350710940000⟩, ⟨.count 5, 1119491773804404000⟩, ⟨.count 6, 294512451262389360⟩, ⟨.count 7, 80373768375700800⟩, ⟨.count 8, 24112130512710240⟩, ⟨.count 9, 10333770219732960⟩, ⟨.count 10, 8611475183110800⟩, ⟨.path 8, 7560507563809200⟩, ⟨.privateRow 2 21, 4556331519383924280⟩, ⟨.privateRow 3 18, 726234407109010800⟩, ⟨.privateRow 3 19, 2680752224502392040⟩, ⟨.privateRow 4 16, 732944181522517965⟩, ⟨.privateRow 4 17, 1150923658222758420⟩, ⟨.privateRow 4 18, 1731121798684848570⟩, ⟨.privateRow 5 13, 84966555140026560⟩, ⟨.privateRow 5 14, 326891597950885968⟩, ⟨.privateRow 5 15, 521855396096514480⟩, ⟨.privateRow 5 16, 768717684679024080⟩, ⟨.privateRow 5 17, 620026213183977600⟩, ⟨.privateRow 6 11, 70614096501508560⟩, ⟨.privateRow 6 12, 147686799390350220⟩, ⟨.privateRow 6 13, 232854288951316032⟩, ⟨.privateRow 6 14, 349841179313876250⟩, ⟨.privateRow 6 15, 237676715053858080⟩, ⟨.privateRow 7 8, 3189435253004000⟩, ⟨.privateRow 7 9, 38608113737613420⟩, ⟨.privateRow 7 10, 76683136154367600⟩, ⟨.privateRow 7 11, 111566445150079920⟩, ⟨.privateRow 7 12, 153399077928480384⟩, ⟨.privateRow 8 6, 3365651550732471⟩, ⟨.privateRow 8 7, 20372517678563050⟩, ⟨.privateRow 8 8, 42949732475765115⟩, ⟨.privateRow 8 9, 63509629475442150⟩, ⟨.privateRow 8 10, 920949429304905⟩, ⟨.privateRow 9 4, 2244202623477360⟩, ⟨.privateRow 9 5, 12113475090909192⟩, ⟨.privateRow 9 6, 26472312599933200⟩, ⟨.privateRow 9 7, 71762293192590⟩, ⟨.privateRow 10 2, 1004672104696260⟩, ⟨.privateRow 10 3, 8454902907054240⟩, ⟨.privateRow 10 4, 1894524540284376⟩, ⟨.privateRow 11 0, 264968467172640⟩, ⟨.privateRow 11 1, 2439917968548060⟩, ⟨.privateRow 12 0, 789385225118490⟩, ⟨.hall 4 18, 276201735609880080⟩, ⟨.hall 3 19, 1301538359175366312⟩, ⟨.hall 2 20, 2990642310020336400⟩, ⟨.assumptionRow 12, 8050365487921680⟩]
  caps := #[0, 603593453236774000, 36163485909991440, 16651928259812560, 2058979973587537, 7044833017574352, 0, 5257929427792184, 2037109257500317, 0, 0, 6085182689724600, 0, 7215916862000000, 0, 0] }

theorem case_38_23_12_checked :
    (Witness.linear .conditional case_38_23_12).check 38 23 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_23_13 : Certificate := {
  objectiveScale := 117962422200000
  eta := 8286275246811602040
  rows := #[⟨.count 2, 1645772912761657680⟩, ⟨.count 3, 326799272480400720⟩, ⟨.count 4, 70869597700061160⟩, ⟨.count 5, 14911865715146400⟩, ⟨.count 6, 3097079802376560⟩, ⟨.count 7, 713730324827520⟩, ⟨.count 8, 223040726508600⟩, ⟨.count 9, 57353329673640⟩, ⟨.count 10, 95588882789400⟩, ⟨.path 7, 259945913026800⟩, ⟨.privateRow 2 21, 117555208054404120⟩, ⟨.privateRow 3 18, 16262855258569920⟩, ⟨.privateRow 3 19, 53520215473785060⟩, ⟨.privateRow 4 16, 13143471383542500⟩, ⟨.privateRow 4 17, 22641820036715880⟩, ⟨.privateRow 4 18, 36749145988384830⟩, ⟨.privateRow 5 13, 1076968079427240⟩, ⟨.privateRow 5 14, 5486801872111560⟩, ⟨.privateRow 5 15, 9874331592145020⟩, ⟨.privateRow 5 16, 16536876722566200⟩, ⟨.privateRow 5 17, 15791283436808880⟩, ⟨.privateRow 6 11, 787925505278340⟩, ⟨.privateRow 6 12, 2295726334992090⟩, ⟨.privateRow 6 13, 4265175950063028⟩, ⟨.privateRow 6 14, 5453345763135270⟩, ⟨.privateRow 6 15, 12139788114253800⟩, ⟨.privateRow 6 16, 1209199367285910⟩, ⟨.privateRow 7 9, 390321271390050⟩, ⟨.privateRow 7 10, 1067864376304440⟩, ⟨.privateRow 7 11, 1955323702392060⟩, ⟨.privateRow 7 12, 3578847771635136⟩, ⟨.privateRow 7 13, 3414116263628070⟩, ⟨.privateRow 8 7, 159845853997830⟩, ⟨.privateRow 8 8, 535297743620640⟩, ⟨.privateRow 8 9, 606989405712690⟩, ⟨.privateRow 8 10, 2721096863404920⟩, ⟨.privateRow 9 5, 54167033580660⟩, ⟨.privateRow 9 6, 274729529794720⟩, ⟨.privateRow 9 7, 602209961573220⟩, ⟨.privateRow 9 8, 539849595182040⟩, ⟨.privateRow 10 3, 10427878122480⟩, ⟨.privateRow 10 4, 139559768872524⟩, ⟨.privateRow 10 5, 337747385855880⟩, ⟨.privateRow 11 2, 53877370299480⟩, ⟨.privateRow 11 3, 93677105133612⟩, ⟨.privateRow 12 0, 8762314255695⟩, ⟨.privateRow 12 1, 28676664836820⟩, ⟨.hall 4 18, 9883890480423960⟩, ⟨.hall 3 19, 31544331320502000⟩, ⟨.hall 2 20, 65742392101300200⟩, ⟨.assumptionRow 13, 82428791083100⟩]
  caps := #[0, 0, 967144465680120, 578110685555000, 223126295982590, 70475374569600, 14029987453440, 1434065082736, 0, 85958592917340, 0, 63600677806400, 0, 979233008716900, 117962422200000, 0] }

theorem case_38_23_13_checked :
    (Witness.linear .conditional case_38_23_13).check 38 23 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_23_14 : Certificate := {
  objectiveScale := 45971830951200000
  eta := 10434352709641655995200
  rows := #[⟨.count 2, 1341057741229557711360⟩, ⟨.count 3, 155664003127521208320⟩, ⟨.count 4, 14130214569611300160⟩, ⟨.count 5, 561558452840985600⟩, ⟨.path 4, 8263668077763658560⟩, ⟨.path 5, 576524211626563200⟩, ⟨.privateRow 2 21, 118446716665484887680⟩, ⟨.privateRow 3 17, 5038232244082717680⟩, ⟨.privateRow 3 18, 23627571903284469120⟩, ⟨.privateRow 3 19, 37255893605669138400⟩, ⟨.privateRow 4 14, 1077782759749495800⟩, ⟨.privateRow 4 15, 4628996521574849424⟩, ⟨.privateRow 4 16, 9589049299801111140⟩, ⟨.privateRow 4 17, 15069655064676532320⟩, ⟨.privateRow 4 18, 23116027250149633800⟩, ⟨.privateRow 5 11, 131615262384606000⟩, ⟨.privateRow 5 12, 754092779529323520⟩, ⟨.privateRow 5 13, 1991192680698661440⟩, ⟨.privateRow 5 14, 3682419554504763072⟩, ⟨.privateRow 5 15, 5926196547637526160⟩, ⟨.privateRow 5 16, 10086993709156203840⟩, ⟨.privateRow 5 17, 9627217725892646880⟩, ⟨.privateRow 6 8, 4562662429333008⟩, ⟨.privateRow 6 9, 84623739073954080⟩, ⟨.privateRow 6 10, 350535315484333980⟩, ⟨.privateRow 6 11, 818270888425436160⟩, ⟨.privateRow 6 12, 1524982173496301520⟩, ⟨.privateRow 6 13, 2470155244434285408⟩, ⟨.privateRow 6 14, 3574670526365898960⟩, ⟨.privateRow 6 15, 6533966581493551200⟩, ⟨.privateRow 6 16, 1360024377974262000⟩, ⟨.privateRow 7 6, 2552538422004480⟩, ⟨.privateRow 7 7, 42818832029125152⟩, ⟨.privateRow 7 8, 156768401418108480⟩, ⟨.privateRow 7 9, 361795732377239160⟩, ⟨.privateRow 7 10, 687240582762539520⟩, ⟨.privateRow 7 11, 1137545838150802080⟩, ⟨.privateRow 7 12, 2046412595228025024⟩, ⟨.privateRow 7 13, 2263197556293513840⟩, ⟨.privateRow 8 4, 1535511394487070⟩, ⟨.privateRow 8 5, 21776343412725720⟩, ⟨.privateRow 8 6, 75342425756165568⟩, ⟨.privateRow 8 7, 178119321760500120⟩, ⟨.privateRow 8 8, 347281493719825665⟩, ⟨.privateRow 8 9, 590513810565598920⟩, ⟨.privateRow 8 10, 1094307787137785220⟩, ⟨.privateRow 8 11, 378350007601614048⟩, ⟨.privateRow 9 2, 1079920101617280⟩, ⟨.privateRow 9 3, 12869047877605920⟩, ⟨.privateRow 9 4, 41478749357572800⟩, ⟨.privateRow 9 5, 100378573445326176⟩, ⟨.privateRow 9 6, 203044977624448960⟩, ⟨.privateRow 9 7, 356823600242709600⟩, ⟨.privateRow 9 8, 308857149062542080⟩, ⟨.privateRow 10 2, 50598756427859640⟩, ⟨.privateRow 10 3, 57113047192350240⟩, ⟨.privateRow 10 4, 141793509342348864⟩, ⟨.privateRow 10 5, 113481604011615840⟩, ⟨.privateRow 11 0, 30237762845283840⟩, ⟨.privateRow 11 1, 83648811204438480⟩, ⟨.privateRow 11 2, 3828807633006720⟩, ⟨.privateRow 12 0, 41824405602219240⟩, ⟨.privateRow 13 0, 14038961321024640⟩, ⟨.hall 4 18, 6071481324992603520⟩, ⟨.hall 3 19, 20025525402342572112⟩, ⟨.hall 2 20, 45839548540032287040⟩]
  caps := #[0, 329002998796422720, 0, 0, 34368183377671572, 14965758785577600, 1221768317860608, 24466168267937136, 0, 9629263369647488, 10755976097104056, 0, 0, 0, 367774647609600000, 45971830951200000] }

theorem case_38_23_14_checked :
    (Witness.linear .negative case_38_23_14).check 38 23 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_24_1_checked :
    (Witness.rising).check 38 24 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_24_2_checked :
    (Witness.rising).check 38 24 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_24_3_checked :
    (Witness.rising).check 38 24 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_24_4_checked :
    (Witness.rising).check 38 24 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_24_5_checked :
    (Witness.rising).check 38 24 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_24_6_checked :
    (Witness.rising).check 38 24 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_24_7_checked :
    (Witness.rising).check 38 24 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_24_8_checked :
    (Witness.rising).check 38 24 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_24_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_38_24_9_checked :
    (Witness.linear .positive case_38_24_9).check 38 24 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_24_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_38_24_10_checked :
    (Witness.linear .positive case_38_24_10).check 38 24 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_24_11 : Certificate := {
  objectiveScale := 13
  eta := 151164
  rows := #[⟨.assumptionRow 11, 50⟩]
  caps := #[0, 0, 45474, 14014, 4455, 1476, 518, 198, 87, 50, 351, 106, 13, 0, 0] }

theorem case_38_24_11_checked :
    (Witness.linear .conditional case_38_24_11).check 38 24 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_24_12 : Certificate := {
  objectiveScale := 116260452000000
  eta := 13110205738148719200
  rows := #[⟨.count 2, 2442255087126254400⟩, ⟨.count 3, 489739806389433600⟩, ⟨.count 4, 102517303969080000⟩, ⟨.count 5, 21675087124891200⟩, ⟨.count 6, 5077047434659200⟩, ⟨.count 7, 1196035212972600⟩, ⟨.count 8, 390542110358400⟩, ⟨.path 7, 256327887816000⟩, ⟨.path 8, 52092433192800⟩, ⟨.privateRow 2 22, 225538068731976000⟩, ⟨.privateRow 3 19, 58174501855470000⟩, ⟨.privateRow 3 20, 80817807962291400⟩, ⟨.privateRow 4 16, 11247612778321920⟩, ⟨.privateRow 4 17, 27386765488882800⟩, ⟨.privateRow 4 18, 35441696515024800⟩, ⟨.privateRow 4 19, 44228893998088800⟩, ⟨.privateRow 5 13, 1498007951874720⟩, ⟨.privateRow 5 14, 7371482333014800⟩, ⟨.privateRow 5 15, 11727979574062752⟩, ⟨.privateRow 5 16, 8435709583741440⟩, ⟨.privateRow 5 17, 33215606485981920⟩, ⟨.privateRow 6 11, 1574372882382300⟩, ⟨.privateRow 6 12, 3719448670080000⟩, ⟨.privateRow 6 13, 5652012208242400⟩, ⟨.privateRow 6 14, 6958158599552160⟩, ⟨.privateRow 6 15, 5491998426915000⟩, ⟨.privateRow 7 8, 82990198451160⟩, ⟨.privateRow 7 9, 1025173039690800⟩, ⟨.privateRow 7 10, 2035090528195725⟩, ⟨.privateRow 7 11, 3023214372149400⟩, ⟨.privateRow 7 12, 2009664609552600⟩, ⟨.privateRow 8 6, 90978559799400⟩, ⟨.privateRow 8 7, 644394482091360⟩, ⟨.privateRow 8 8, 1293670740562200⟩, ⟨.privateRow 8 9, 634630929332400⟩, ⟨.privateRow 9 4, 73226645692200⟩, ⟨.privateRow 9 5, 452673809733600⟩, ⟨.privateRow 9 6, 266870442078240⟩, ⟨.privateRow 10 2, 54075061434240⟩, ⟨.privateRow 10 3, 151335067763880⟩, ⟨.privateRow 11 0, 20921898769200⟩, ⟨.privateRow 11 1, 22531275597600⟩, ⟨.hall 3 20, 19561975349202000⟩, ⟨.hall 2 21, 71176299612818400⟩, ⟨.assumptionRow 12, 136762285147488⟩]
  caps := #[0, 25044255947142432, 0, 3145263692450880, 208603463420352, 147144186446400, 0, 22405580327592, 61097545039440, 136762285147488, 210385146460104, 0, 1142102686852512, 116260452000000, 0] }

theorem case_38_24_12_checked :
    (Witness.linear .conditional case_38_24_12).check 38 24 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_24_13 : Certificate := {
  objectiveScale := 1472632392000000
  eta := 223543667809903240800
  rows := #[⟨.count 2, 37871063712509227200⟩, ⟨.count 3, 6698480641339687200⟩, ⟨.count 4, 1170454704744124800⟩, ⟨.count 5, 195075784124020800⟩, ⟨.count 6, 33391350435643200⟩, ⟨.count 7, 7688797797681000⟩, ⟨.count 8, 3514878993225600⟩, ⟨.path 6, 13110281676892400⟩, ⟨.path 7, 398473352877600⟩, ⟨.privateRow 2 22, 3740709968540344800⟩, ⟨.privateRow 3 19, 873154523233792800⟩, ⟨.privateRow 3 20, 1304898826235004000⟩, ⟨.privateRow 4 16, 144988758470556000⟩, ⟨.privateRow 4 17, 398719085794029000⟩, ⟨.privateRow 4 18, 568531677154240800⟩, ⟨.privateRow 4 19, 783598335552232200⟩, ⟨.privateRow 5 13, 14159941086994560⟩, ⟨.privateRow 5 14, 90332390125897920⟩, ⟨.privateRow 5 15, 165550800580925760⟩, ⟨.privateRow 5 16, 244240154041763880⟩, ⟨.privateRow 5 17, 357463193611043520⟩, ⟨.privateRow 5 18, 259925301549033120⟩, ⟨.privateRow 6 11, 12704823027596700⟩, ⟨.privateRow 6 12, 43182799059628800⟩, ⟨.privateRow 6 13, 77083249031989200⟩, ⟨.privateRow 6 14, 110601525653498880⟩, ⟨.privateRow 6 15, 167689018635138000⟩, ⟨.privateRow 6 16, 51551558567308800⟩, ⟨.privateRow 7 9, 7444708978707000⟩, ⟨.privateRow 7 10, 21720853778448825⟩, ⟨.privateRow 7 11, 39667920066403200⟩, ⟨.privateRow 7 12, 57739210128299700⟩, ⟨.privateRow 7 13, 52635312923553360⟩, ⟨.privateRow 8 7, 3800462911425180⟩, ⟨.privateRow 8 8, 12326485358187000⟩, ⟨.privateRow 8 9, 23340993314388750⟩, ⟨.privateRow 8 10, 25796701182423600⟩, ⟨.privateRow 9 5, 1917206723577600⟩, ⟨.privateRow 9 6, 7879187076480720⟩, ⟨.privateRow 9 7, 12627528234921600⟩, ⟨.privateRow 10 3, 966591723137040⟩, ⟨.privateRow 10 4, 5655759834553920⟩, ⟨.privateRow 10 5, 421785479187072⟩, ⟨.privateRow 11 1, 405562960756800⟩, ⟨.privateRow 11 2, 1537759559536200⟩, ⟨.privateRow 12 0, 371766047360400⟩, ⟨.hall 4 19, 16871419167482880⟩, ⟨.hall 3 20, 421157822223996000⟩, ⟨.hall 2 21, 1246903322846781600⟩, ⟨.assumptionRow 13, 1163639238022800⟩]
  caps := #[0, 132910355104696400, 20820372169396800, 9126913106968800, 0, 1064259883825600, 930504480748700, 164830535515800, 0, 1163639238022800, 0, 3623322867502800, 12816040682491200, 13562684681977200, 1472632392000000] }

theorem case_38_24_13_checked :
    (Witness.linear .conditional case_38_24_13).check 38 24 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_24_14 : Certificate := {
  objectiveScale := 2763882000000
  eta := 552976152385456800
  rows := #[⟨.count 2, 89492644042401600⟩, ⟨.count 3, 14704219836306000⟩, ⟨.count 4, 2298319042219200⟩, ⟨.count 5, 310184446572000⟩, ⟨.count 6, 31510800921600⟩, ⟨.path 5, 23731792484400⟩, ⟨.path 6, 28368230690800⟩, ⟨.privateRow 2 22, 9228725819913600⟩, ⟨.privateRow 3 19, 2016527140227600⟩, ⟨.privateRow 3 20, 3160188683051400⟩, ⟨.privateRow 4 16, 312547756641120⟩, ⟨.privateRow 4 17, 894734421480900⟩, ⟨.privateRow 4 18, 1358903289744000⟩, ⟨.privateRow 4 19, 2003643817975800⟩, ⟨.privateRow 5 13, 31989089864160⟩, ⟨.privateRow 5 14, 182270289080880⟩, ⟨.privateRow 5 15, 359104965002784⟩, ⟨.privateRow 5 16, 571330209209760⟩, ⟨.privateRow 5 17, 918342904358880⟩, ⟨.privateRow 5 18, 782255632878720⟩, ⟨.privateRow 6 10, 692945853600⟩, ⟨.privateRow 6 11, 25438406994000⟩, ⟨.privateRow 6 12, 82622070273600⟩, ⟨.privateRow 6 13, 159468723414000⟩, ⟨.privateRow 6 14, 251429932353600⟩, ⟨.privateRow 6 15, 425067574932000⟩, ⟨.privateRow 6 16, 348916472704800⟩, ⟨.privateRow 7 8, 713916583380⟩, ⟨.privateRow 7 9, 13649209774200⟩, ⟨.privateRow 7 10, 39265412085900⟩, ⟨.privateRow 7 11, 77651616556800⟩, ⟨.privateRow 7 12, 66345006627900⟩, ⟨.privateRow 7 13, 334457610406920⟩, ⟨.privateRow 8 6, 201418471800⟩, ⟨.privateRow 8 7, 6966841141260⟩, ⟨.privateRow 8 8, 20925141237000⟩, ⟨.privateRow 8 9, 42927311802375⟩, ⟨.privateRow 8 10, 72059856125400⟩, ⟨.privateRow 8 11, 68232372308100⟩, ⟨.privateRow 9 5, 3640452379200⟩, ⟨.privateRow 9 6, 12768439123440⟩, ⟨.privateRow 9 7, 28046071653600⟩, ⟨.privateRow 9 8, 34670086951500⟩, ⟨.privateRow 10 3, 2018660684040⟩, ⟨.privateRow 10 4, 8969835944160⟩, ⟨.privateRow 10 5, 17074915249392⟩, ⟨.privateRow 11 1, 1249827440400⟩, ⟨.privateRow 11 2, 7877700230400⟩, ⟨.privateRow 12 0, 2916264027600⟩, ⟨.hall 4 19, 179020737735840⟩, ⟨.hall 3 20, 1203881403067200⟩, ⟨.hall 2 21, 3181606180552800⟩, ⟨.assumptionRow 14, 826947290400⟩]
  caps := #[0, 273167376196000, 17436593367600, 0, 5703022099060, 1423058498576, 3961564406800, 826947290400, 237666899145, 2416512527520, 172767638400, 128160991200, 0, 113341335096000, 24047990709600] }

theorem case_38_24_14_checked :
    (Witness.linear .conditional case_38_24_14).check 38 24 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_24_15 : Certificate := {
  objectiveScale := 535309625188800000
  eta := 209090482753600328680800
  rows := #[⟨.count 2, 23934202956954427737600⟩, ⟨.count 3, 2868148288230076051200⟩, ⟨.count 4, 397854425561695502400⟩, ⟨.count 5, 74176248833536449600⟩, ⟨.count 6, 11988080619561446400⟩, ⟨.count 7, 1311196317764533200⟩, ⟨.path 3, 743260705506226908000⟩, ⟨.path 6, 783942771996784400⟩, ⟨.path 7, 1297216601335254600⟩, ⟨.privateRow 6 11, 952178278376625300⟩, ⟨.privateRow 6 12, 6404346640509760800⟩, ⟨.privateRow 7 10, 4928693301597039975⟩, ⟨.privateRow 8 7, 65559815888226660⟩, ⟨.privateRow 8 8, 1810699676912926800⟩, ⟨.privateRow 8 14, 84509724575918842200⟩, ⟨.privateRow 9 5, 34057047214663200⟩, ⟨.privateRow 9 6, 711792286786460880⟩, ⟨.privateRow 10 4, 20434228328797920⟩, ⟨.hall 11 3, 36021876861663000⟩, ⟨.hall 9 4, 20583929635236000⟩, ⟨.hall 10 5, 27788305007568600⟩, ⟨.hall 9 6, 18368350299952416⟩, ⟨.hall 8 7, 22530046618931040⟩, ⟨.hall 12 7, 31218959946774600⟩, ⟨.hall 7 8, 7743740373469800⟩, ⟨.hall 11 8, 14408750744665200⟩, ⟨.hall 6 10, 15020887214209800⟩, ⟨.hall 5 14, 276311958810647760⟩, ⟨.hall 6 14, 193373910729139140⟩, ⟨.hall 4 15, 397679290095987900⟩, ⟨.hall 3 17, 2100989058613499340⟩, ⟨.hall 2 20, 135936271311098544000⟩]
  caps := #[0, 154197323104890126600, 17778351838844088800, 1888131556266817400, 0, 1265555577693407000, 0, 0, 468294064514296020, 476123846447471040, 0, 108065630584989000, 15975245144509358400, 11741897670821841600, 18735836881608000000] }

theorem case_38_24_15_checked :
    (Witness.linear .negative case_38_24_15).check 38 24 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_25_1_checked :
    (Witness.rising).check 38 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_25_2_checked :
    (Witness.rising).check 38 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_25_3_checked :
    (Witness.rising).check 38 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_25_4_checked :
    (Witness.rising).check 38 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_25_5_checked :
    (Witness.rising).check 38 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_25_6_checked :
    (Witness.rising).check 38 25 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_25_7_checked :
    (Witness.rising).check 38 25 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_25_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_38_25_8_checked :
    (Witness.linear .positive case_38_25_8).check 38 25 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_25_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_38_25_9_checked :
    (Witness.linear .positive case_38_25_9).check 38 25 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_25_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_38_25_10_checked :
    (Witness.linear .positive case_38_25_10).check 38 25 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_25_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_38_25_11_checked :
    (Witness.linear .positive case_38_25_11).check 38 25 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_25_12 : Certificate := {
  objectiveScale := 967
  eta := 12978888
  rows := #[⟨.assumptionRow 12, 2162⟩]
  caps := #[0, 0, 3900104, 1196195, 376189, 125829, 44388, 16730, 6942, 267140, 143870, 46353, 9442, 967] }

theorem case_38_25_12_checked :
    (Witness.linear .conditional case_38_25_12).check 38 25 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_25_13 : Certificate := {
  objectiveScale := 3585866961600000
  eta := 1107551821980432628800
  rows := #[⟨.count 2, 176144962266515642400⟩, ⟨.count 3, 28390077903450463200⟩, ⟨.count 4, 4471945445412244800⟩, ⟨.count 5, 707681602472644800⟩, ⟨.count 6, 112927915288188000⟩, ⟨.count 7, 22585583057637600⟩, ⟨.count 8, 15057055371758400⟩, ⟨.path 5, 13083879250041600⟩, ⟨.path 6, 51670649053623600⟩, ⟨.privateRow 2 23, 15154926231674829600⟩, ⟨.privateRow 3 19, 722738657844403200⟩, ⟨.privateRow 3 20, 4035290839631251200⟩, ⟨.privateRow 3 21, 5420539933833024000⟩, ⟨.privateRow 4 16, 134384219192943720⟩, ⟨.privateRow 4 17, 1028547452444816304⟩, ⟨.privateRow 4 18, 1863310602255102000⟩, ⟨.privateRow 4 19, 2366969104440420480⟩, ⟨.privateRow 4 20, 2913540214435250400⟩, ⟨.privateRow 5 14, 209938372040517120⟩, ⟨.privateRow 5 15, 545567306303379360⟩, ⟨.privateRow 5 16, 821512941083138304⟩, ⟨.privateRow 5 17, 1053241023254500080⟩, ⟨.privateRow 5 18, 1345096946543750400⟩, ⟨.privateRow 6 11, 14847929602706200⟩, ⟨.privateRow 6 12, 137866163247662850⟩, ⟨.privateRow 6 13, 274253508557028000⟩, ⟨.privateRow 6 14, 409991070226838100⟩, ⟨.privateRow 6 15, 514198440945549360⟩, ⟨.privateRow 6 16, 234325424222990100⟩, ⟨.privateRow 7 9, 14035326614389080⟩, ⟨.privateRow 7 10, 82813804544671200⟩, ⟨.privateRow 7 11, 158502395386635300⟩, ⟨.privateRow 7 12, 236226761572230000⟩, ⟨.privateRow 7 13, 94644348051052800⟩, ⟨.privateRow 8 7, 10266174117108000⟩, ⟨.privateRow 8 8, 54393612530477220⟩, ⟨.privateRow 8 9, 110000154521457200⟩, ⟨.privateRow 8 10, 31760976174802875⟩, ⟨.privateRow 9 5, 8030429531604480⟩, ⟨.privateRow 9 6, 42433519684046400⟩, ⟨.privateRow 9 7, 18369607553545248⟩, ⟨.privateRow 10 3, 7296880680159840⟩, ⟨.privateRow 10 4, 13551349834582560⟩, ⟨.privateRow 11 1, 4839767798065200⟩, ⟨.hall 3 21, 714525718550716800⟩, ⟨.hall 2 22, 3867044612216385600⟩, ⟨.assumptionRow 13, 3185256465983592⟩]
  caps := #[0, 1070934667306723296, 47505857008497888, 0, 12246821856060792, 4901367478549080, 10760569858336298, 492805696532688, 16301308670539529, 3185256465983592, 0, 36750369714674616, 194858274912196896, 36259280111616408] }

theorem case_38_25_13_checked :
    (Witness.linear .conditional case_38_25_13).check 38 25 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_25_14 : Certificate := {
  objectiveScale := 6723500553000000
  eta := 3149740242052024420800
  rows := #[⟨.count 2, 436760005168595908800⟩, ⟨.count 3, 58135290790359182400⟩, ⟨.count 4, 6884085715967940480⟩, ⟨.count 5, 587225159498577600⟩, ⟨.count 6, 33878374586456400⟩, ⟨.count 7, 11292791528818800⟩, ⟨.path 5, 523183013695742400⟩, ⟨.path 6, 2020174509553200⟩, ⟨.privateRow 2 23, 37887315579187074000⟩, ⟨.privateRow 3 19, 2337607846465491600⟩, ⟨.privateRow 3 20, 9327845802804328800⟩, ⟨.privateRow 3 21, 13122223756487445600⟩, ⟨.privateRow 4 16, 518339131172782920⟩, ⟨.privateRow 4 17, 2275271637226411824⟩, ⟨.privateRow 4 18, 4146713049382263360⟩, ⟨.privateRow 4 19, 5657688555938218800⟩, ⟨.privateRow 4 20, 7558265370238422840⟩, ⟨.privateRow 5 13, 61733927024209440⟩, ⟨.privateRow 5 14, 451711661152752000⟩, ⟨.privateRow 5 15, 1104685962441341280⟩, ⟨.privateRow 5 16, 1781550791586453888⟩, ⟨.privateRow 5 17, 1809858055685359680⟩, ⟨.privateRow 5 18, 4914622873341941760⟩, ⟨.privateRow 5 19, 520974115862840640⟩, ⟨.privateRow 6 11, 58973466872720400⟩, ⟨.privateRow 6 12, 256675740790443975⟩, ⟨.privateRow 6 13, 531030077843265000⟩, ⟨.privateRow 6 14, 859506910804542000⟩, ⟨.privateRow 6 15, 1195530196517616960⟩, ⟨.privateRow 6 16, 1461004904040932250⟩, ⟨.privateRow 7 9, 38234165604715080⟩, ⟨.privateRow 7 10, 145910036578706400⟩, ⟨.privateRow 7 11, 292805951782944600⟩, ⟨.privateRow 7 12, 477062825809284000⟩, ⟨.privateRow 7 13, 676491987774002400⟩, ⟨.privateRow 7 14, 93246192909389520⟩, ⟨.privateRow 8 7, 24981023684962800⟩, ⟨.privateRow 8 8, 94106596073490000⟩, ⟨.privateRow 8 9, 194696090987598200⟩, ⟨.privateRow 8 10, 321844558571335800⟩, ⟨.privateRow 8 11, 18014691248353800⟩, ⟨.privateRow 9 5, 18821319214698000⟩, ⟨.privateRow 9 6, 73642689000054720⟩, ⟨.privateRow 9 7, 145752295998621312⟩, ⟨.privateRow 10 3, 18242201700399600⟩, ⟨.privateRow 10 4, 63804272137826220⟩, ⟨.privateRow 11 1, 24198838990326000⟩, ⟨.privateRow 11 2, 1737352542895200⟩, ⟨.privateRow 12 0, 8872907629786200⟩, ⟨.hall 3 21, 2349927255406021200⟩, ⟨.hall 2 22, 9970061947138893600⟩, ⟨.assumptionRow 14, 3110739589188000⟩]
  caps := #[0, 867145416338678400, 44775851041152000, 3296981792154960, 29561284961836992, 20729467550343552, 0, 16735003271672400, 3110739589188000, 23272198343686656, 0, 0, 0, 328850894380932000] }

theorem case_38_25_14_checked :
    (Witness.linear .conditional case_38_25_14).check 38 25 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_25_15 : Certificate := {
  objectiveScale := 56404296000000
  eta := 31609154763224438400
  rows := #[⟨.count 2, 4777482090750969600⟩, ⟨.count 3, 701135056658836800⟩, ⟨.count 4, 97637054708793600⟩, ⟨.count 5, 11596738298745600⟩, ⟨.count 6, 841698747489600⟩, ⟨.path 5, 2230546920201600⟩, ⟨.path 6, 900327501216000⟩, ⟨.privateRow 5 14, 2335380016844160⟩, ⟨.privateRow 5 15, 6085170204072960⟩, ⟨.privateRow 5 16, 11776300698210048⟩, ⟨.privateRow 5 18, 14140538957825280⟩, ⟨.privateRow 6 11, 197435508670400⟩, ⟨.privateRow 6 12, 1651249278929250⟩, ⟨.privateRow 6 14, 6838802323353000⟩, ⟨.privateRow 6 17, 77607741921309600⟩, ⟨.privateRow 7 8, 7287435043200⟩, ⟨.privateRow 7 9, 36072803463840⟩, ⟨.privateRow 7 10, 42307609000800⟩, ⟨.privateRow 7 14, 19815993369469440⟩, ⟨.privateRow 8 6, 1948376730300⟩, ⟨.privateRow 8 7, 14878513213200⟩, ⟨.privateRow 8 8, 23380520763600⟩, ⟨.privateRow 8 9, 38967534606000⟩, ⟨.privateRow 8 10, 84754387768050⟩, ⟨.hall 8 5, 2720422584000⟩, ⟨.hall 10 5, 3176574249600⟩, ⟨.hall 8 6, 2460471092640⟩, ⟨.hall 9 6, 2837895377400⟩, ⟨.hall 11 6, 2569287996000⟩, ⟨.hall 7 7, 3215703223425⟩, ⟨.hall 6 9, 931321702800⟩, ⟨.hall 4 15, 9526967615880⟩, ⟨.hall 3 18, 246612555100080⟩]
  caps := #[0, 247644281913600, 0, 0, 122031976684800, 27452528318592, 67193046242920, 87040101358080, 18806572263300, 206683389918720, 0, 1937325875284800, 0, 8686261584000000] }

theorem case_38_25_15_checked :
    (Witness.linear .negative case_38_25_15).check 38 25 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_25_16 : Certificate := {
  objectiveScale := 949
  eta := 303297
  rows := #[⟨.assumptionRow 16, 395⟩]
  caps := #[0, 0, 155244, 80140, 34762, 20475, 9584, 5284, 3073, 1430, 566280, 554554, 373373, 200145] }

theorem case_38_25_16_checked :
    (Witness.linear .conditional case_38_25_16).check 38 25 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_26_1_checked :
    (Witness.rising).check 38 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_26_2_checked :
    (Witness.rising).check 38 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_26_3_checked :
    (Witness.rising).check 38 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_26_4_checked :
    (Witness.rising).check 38 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_26_5_checked :
    (Witness.rising).check 38 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_26_6_checked :
    (Witness.rising).check 38 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_26_7_checked :
    (Witness.rising).check 38 26 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_26_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_38_26_8_checked :
    (Witness.linear .positive case_38_26_8).check 38 26 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_26_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_38_26_9_checked :
    (Witness.linear .positive case_38_26_9).check 38 26 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_26_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_38_26_10_checked :
    (Witness.linear .positive case_38_26_10).check 38 26 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_26_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_38_26_11_checked :
    (Witness.linear .positive case_38_26_11).check 38 26 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_26_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_38_26_12_checked :
    (Witness.linear .positive case_38_26_12).check 38 26 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_26_13 : Certificate := {
  objectiveScale := 958776000000
  eta := 634445131770450000
  rows := #[⟨.count 2, 82518106779108000⟩, ⟨.count 3, 10977376233423600⟩, ⟨.count 4, 1344898489334400⟩, ⟨.count 5, 134132163165000⟩, ⟨.count 6, 15329390076000⟩, ⟨.count 7, 8942144211000⟩, ⟨.path 5, 94161945150000⟩, ⟨.privateRow 2 23, 2253420341172000⟩, ⟨.privateRow 2 24, 7082178215112000⟩, ⟨.privateRow 3 20, 1368148064283000⟩, ⟨.privateRow 3 21, 2296342633384800⟩, ⟨.privateRow 3 22, 2382187217810400⟩, ⟨.privateRow 4 16, 51608946589200⟩, ⟨.privateRow 4 17, 287937043594200⟩, ⟨.privateRow 4 18, 791200919789280⟩, ⟨.privateRow 4 19, 947867286366000⟩, ⟨.privateRow 4 20, 1033711870791600⟩, ⟨.privateRow 4 21, 836984698149600⟩, ⟨.privateRow 5 13, 13910002106000⟩, ⟨.privateRow 5 14, 64383438319200⟩, ⟨.privateRow 5 15, 208990684702800⟩, ⟨.privateRow 5 16, 362454912019200⟩, ⟨.privateRow 5 17, 441026552486520⟩, ⟨.privateRow 5 18, 455602247550450⟩, ⟨.privateRow 6 10, 464526972000⟩, ⟨.privateRow 6 11, 12774491730000⟩, ⟨.privateRow 6 12, 54930314439000⟩, ⟨.privateRow 6 13, 125030337807375⟩, ⟨.privateRow 6 14, 189792448560000⟩, ⟨.privateRow 6 15, 198004621815000⟩, ⟨.privateRow 7 9, 12193833015000⟩, ⟨.privateRow 7 10, 43305526964700⟩, ⟨.privateRow 7 11, 84737461809000⟩, ⟨.privateRow 7 12, 67385443875750⟩, ⟨.privateRow 8 7, 12220930421700⟩, ⟨.privateRow 8 8, 39833187849000⟩, ⟨.privateRow 8 9, 18063131306220⟩, ⟨.privateRow 9 5, 15132859434000⟩, ⟨.privateRow 9 6, 7153715368800⟩, ⟨.privateRow 10 3, 6131756030400⟩, ⟨.hall 2 23, 1162478747430000⟩, ⟨.assumptionRow 13, 921103773408⟩]
  caps := #[0, 0, 132224994597696, 0, 12672412192440, 8740596410000, 209477215584, 0, 8012731684776, 921103773408, 0, 252672260393280, 61851402945696] }

theorem case_38_26_13_checked :
    (Witness.linear .conditional case_38_26_13).check 38 26 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_26_14 : Certificate := {
  objectiveScale := 999603000000
  eta := 582138186953122800
  rows := #[⟨.count 2, 77637228978909600⟩, ⟨.count 3, 10259960777866800⟩, ⟨.count 4, 1203459316899840⟩, ⟨.count 5, 117525323916000⟩, ⟨.path 5, 88600319262000⟩, ⟨.privateRow 2 23, 4636374028486200⟩, ⟨.privateRow 2 24, 9272748056972400⟩, ⟨.privateRow 3 20, 1510788038940180⟩, ⟨.privateRow 3 21, 2968689682118160⟩, ⟨.privateRow 3 22, 3155554947144600⟩, ⟨.privateRow 4 16, 19139838466320⟩, ⟨.privateRow 4 17, 276576262282320⟩, ⟨.privateRow 4 18, 865926586613088⟩, ⟨.privateRow 4 19, 1182892385214540⟩, ⟨.privateRow 4 20, 1434592453934640⟩, ⟨.privateRow 4 21, 1611272190888360⟩, ⟨.privateRow 5 13, 2219922785080⟩, ⟨.privateRow 5 14, 44218903123395⟩, ⟨.privateRow 5 15, 196770970899360⟩, ⟨.privateRow 5 16, 395080963897620⟩, ⟨.privateRow 5 17, 541556692604928⟩, ⟨.privateRow 5 18, 658729440549180⟩, ⟨.privateRow 5 19, 471668299982880⟩, ⟨.privateRow 6 10, 992096890200⟩, ⟨.privateRow 6 11, 1930773178620⟩, ⟨.privateRow 6 12, 37589448839800⟩, ⟨.privateRow 6 13, 115426657417500⟩, ⟨.privateRow 6 14, 202311450455400⟩, ⟨.privateRow 6 15, 288076954694100⟩, ⟨.privateRow 6 16, 268125631848360⟩, ⟨.privateRow 7 9, 2136824071200⟩, ⟨.privateRow 7 10, 28877651019360⟩, ⟨.privateRow 7 11, 74805801413200⟩, ⟨.privateRow 7 12, 127913723083575⟩, ⟨.privateRow 7 13, 119204257114800⟩, ⟨.privateRow 8 7, 1664942088810⟩, ⟨.privateRow 8 8, 24680318022360⟩, ⟨.privateRow 8 9, 60290491168908⟩, ⟨.privateRow 8 10, 44920790474560⟩, ⟨.privateRow 9 5, 1627273715760⟩, ⟨.privateRow 9 6, 25659695721660⟩, ⟨.privateRow 9 7, 19445099047920⟩, ⟨.privateRow 10 3, 2518399798200⟩, ⟨.privateRow 10 4, 13018189726080⟩, ⟨.privateRow 11 1, 4701012956640⟩, ⟨.hall 3 22, 14716214472960⟩, ⟨.hall 2 23, 1712931596075700⟩, ⟨.assumptionRow 14, 597290054400⟩]
  caps := #[0, 51240264570000, 48698302955400, 29817335571660, 249538659084, 0, 3277311521900, 2715983750460, 597290054400, 11698607141760, 30322033735320, 0, 226900284811200] }

theorem case_38_26_14_checked :
    (Witness.linear .conditional case_38_26_14).check 38 26 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_26_15 : Certificate := {
  objectiveScale := 338995800000
  eta := 297468347363787600
  rows := #[⟨.count 2, 39417993641426400⟩, ⟨.count 3, 5105300070911040⟩, ⟨.count 4, 576657589347840⟩, ⟨.count 5, 47010129566400⟩, ⟨.path 5, 46099910656800⟩, ⟨.privateRow 2 23, 2650196054305800⟩, ⟨.privateRow 3 20, 766265111932320⟩, ⟨.privateRow 3 21, 1512159167719200⟩, ⟨.privateRow 3 22, 1882755689134320⟩, ⟨.privateRow 4 18, 737588932896816⟩, ⟨.privateRow 4 19, 452472497076600⟩, ⟨.privateRow 4 20, 795515859218080⟩, ⟨.privateRow 4 21, 1046367133932120⟩, ⟨.privateRow 5 14, 24288566942640⟩, ⟨.privateRow 5 15, 14438825509680⟩, ⟨.privateRow 5 17, 907530551279352⟩, ⟨.privateRow 5 19, 504314223292880⟩, ⟨.privateRow 6 9, 46637033300⟩, ⟨.privateRow 6 10, 381575727000⟩, ⟨.privateRow 6 11, 503679959640⟩, ⟨.privateRow 6 12, 186548133200⟩, ⟨.privateRow 6 13, 61106172881325⟩, ⟨.privateRow 6 15, 194849525127400⟩, ⟨.privateRow 6 16, 406861478509200⟩, ⟨.privateRow 7 8, 46637033300⟩, ⟨.privateRow 7 9, 76315145400⟩, ⟨.privateRow 7 11, 31526634510800⟩, ⟨.privateRow 7 17, 299689575985800⟩, ⟨.privateRow 8 8, 213682407120⟩, ⟨.privateRow 8 13, 62157837982240⟩, ⟨.hall 10 5, 18834186525⟩, ⟨.hall 7 6, 13962232570⟩, ⟨.hall 8 6, 27940014520⟩, ⟨.hall 9 6, 9116379360⟩, ⟨.hall 6 7, 13124787390⟩, ⟨.hall 7 7, 5815468120⟩, ⟨.hall 9 8, 5124510216⟩, ⟨.hall 2 22, 39302852889300⟩, ⟨.hall 3 22, 115583601173040⟩]
  caps := #[0, 0, 0, 4587646859796, 2224913414152, 0, 938132496925, 280987955520, 379220105680, 0, 8916041534400, 0, 215940324600000] }

theorem case_38_26_15_checked :
    (Witness.linear .negative case_38_26_15).check 38 26 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_26_16 : Certificate := {
  objectiveScale := 447
  eta := 112047
  rows := #[⟨.assumptionRow 16, 182⟩]
  caps := #[0, 0, 66232, 32640, 15267, 8801, 3890, 2347, 1338, 886210, 871624, 596778, 331513] }

theorem case_38_26_16_checked :
    (Witness.linear .conditional case_38_26_16).check 38 26 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_27_1_checked :
    (Witness.rising).check 38 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_27_2_checked :
    (Witness.rising).check 38 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_27_3_checked :
    (Witness.rising).check 38 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_27_4_checked :
    (Witness.rising).check 38 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_27_5_checked :
    (Witness.rising).check 38 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_27_6_checked :
    (Witness.rising).check 38 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_27_7_checked :
    (Witness.rising).check 38 27 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_27_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_38_27_8_checked :
    (Witness.linear .positive case_38_27_8).check 38 27 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_27_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_38_27_9_checked :
    (Witness.linear .positive case_38_27_9).check 38 27 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_27_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_38_27_10_checked :
    (Witness.linear .positive case_38_27_10).check 38 27 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_27_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_38_27_11_checked :
    (Witness.linear .positive case_38_27_11).check 38 27 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_27_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_38_27_12_checked :
    (Witness.linear .positive case_38_27_12).check 38 27 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_27_13 : Certificate := {
  objectiveScale := 11
  eta := 600780
  rows := #[⟨.assumptionRow 13, 27⟩]
  caps := #[0, 0, 176358, 53482, 16588, 5291, 1749, 606, 224, 91, 4012, 2032] }

theorem case_38_27_13_checked :
    (Witness.linear .conditional case_38_27_13).check 38 27 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_27_14 : Certificate := {
  objectiveScale := 518
  eta := 13339900
  rows := #[⟨.assumptionRow 14, 647⟩]
  caps := #[0, 0, 4253910, 1370200, 446810, 147862, 49775, 19380, 2015520, 1614252, 872644, 368000] }

theorem case_38_27_14_checked :
    (Witness.linear .conditional case_38_27_14).check 38 27 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_27_15 : Certificate := {
  objectiveScale := 35531001874368000
  eta := 75994030141015335148800
  rows := #[⟨.count 2, 7076762584510667368320⟩, ⟨.count 3, 559594803400321328640⟩, ⟨.count 4, 27715780357091386560⟩, ⟨.path 3, 143559068837137873920⟩, ⟨.path 4, 27830281741037455680⟩, ⟨.privateRow 2 24, 660559431844011379680⟩, ⟨.privateRow 2 25, 785280443450922619200⟩, ⟨.privateRow 3 20, 84995059761746918784⟩, ⟨.privateRow 3 21, 151263637239892937760⟩, ⟨.privateRow 3 22, 302380630139272164480⟩, ⟨.privateRow 3 23, 259120549687727407680⟩, ⟨.privateRow 4 16, 5059229747723030880⟩, ⟨.privateRow 4 17, 24164892397509383520⟩, ⟨.privateRow 4 18, 38310833959207009200⟩, ⟨.privateRow 4 19, 87106738265144357760⟩, ⟨.privateRow 4 20, 112402887003759512160⟩, ⟨.privateRow 4 21, 125234266798709228160⟩, ⟨.privateRow 4 22, 52681979329550691120⟩, ⟨.privateRow 5 11, 10474595750979360⟩, ⟨.privateRow 5 12, 125695149011752320⟩, ⟨.privateRow 5 13, 1985983354385686656⟩, ⟨.privateRow 5 14, 5851807492880469120⟩, ⟨.privateRow 5 15, 11108308793913611280⟩, ⟨.privateRow 5 16, 25336550750797503360⟩, ⟨.privateRow 5 17, 41060415343839091200⟩, ⟨.privateRow 5 18, 53181617546872406592⟩, ⟨.privateRow 5 19, 42532096046851691280⟩, ⟨.privateRow 6 9, 76545122795618400⟩, ⟨.privateRow 6 10, 693941968502382600⟩, ⟨.privateRow 6 11, 1766397738006064800⟩, ⟨.privateRow 6 12, 3409480916943781680⟩, ⟨.privateRow 6 13, 8734649012344455200⟩, ⟨.privateRow 6 14, 15620240913647970600⟩, ⟨.privateRow 6 15, 23403239649331027200⟩, ⟨.privateRow 6 16, 17510032563720496800⟩, ⟨.privateRow 7 6, 46088221304309184⟩, ⟨.privateRow 7 7, 309748760064675360⟩, ⟨.privateRow 7 8, 773508609303091200⟩, ⟨.privateRow 7 9, 1440256915759662000⟩, ⟨.privateRow 7 10, 3542317835785747200⟩, ⟨.privateRow 7 11, 6234479390982915072⟩, ⟨.privateRow 7 12, 14482874391687461760⟩, ⟨.privateRow 8 4, 254336278078467585⟩, ⟨.privateRow 8 5, 469261889643875328⟩, ⟨.privateRow 8 6, 966281458027845960⟩, ⟨.privateRow 8 7, 659899532311699680⟩, ⟨.privateRow 8 8, 7460530823635049160⟩, ⟨.privateRow 9 1, 179231971738980160⟩, ⟨.privateRow 9 2, 586577362054844160⟩, ⟨.privateRow 9 3, 934857670774907880⟩, ⟨.privateRow 9 4, 1701074349959048064⟩, ⟨.privateRow 10 0, 1173154724109688320⟩, ⟨.privateRow 11 0, 776352390954940800⟩, ⟨.hall 2 24, 88162577516843077248⟩, ⟨.assumptionRow 15, 6110988072321600⟩]
  caps := #[0, 0, 1785508855053592032, 291618177582199104, 140080262794917120, 125599728263710272, 408361725418314400, 0, 808074289040424471, 0, 9183729842665822080, 0] }

theorem case_38_27_15_checked :
    (Witness.linear .conditional case_38_27_15).check 38 27 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_27_16 : Certificate := {
  objectiveScale := 27
  eta := 6783
  rows := #[⟨.assumptionRow 16, 11⟩]
  caps := #[0, 0, 4012, 1980, 924, 533, 236, 142, 176358, 176358, 122876, 70252] }

theorem case_38_27_16_checked :
    (Witness.linear .conditional case_38_27_16).check 38 27 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_27_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 4862, 4862, 3432] }

theorem case_38_27_17_checked :
    (Witness.linear .negative case_38_27_17).check 38 27 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_28_1_checked :
    (Witness.rising).check 38 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_28_2_checked :
    (Witness.rising).check 38 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_28_3_checked :
    (Witness.rising).check 38 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_28_4_checked :
    (Witness.rising).check 38 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_28_5_checked :
    (Witness.rising).check 38 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_28_6_checked :
    (Witness.rising).check 38 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_28_7_checked :
    (Witness.rising).check 38 28 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_28_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_38_28_8_checked :
    (Witness.linear .positive case_38_28_8).check 38 28 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_28_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_38_28_9_checked :
    (Witness.linear .positive case_38_28_9).check 38 28 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_28_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_38_28_10_checked :
    (Witness.linear .positive case_38_28_10).check 38 28 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_28_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_38_28_11_checked :
    (Witness.linear .positive case_38_28_11).check 38 28 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_28_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_38_28_12_checked :
    (Witness.linear .positive case_38_28_12).check 38 28 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_28_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_38_28_13_checked :
    (Witness.linear .positive case_38_28_13).check 38 28 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_28_14 : Certificate := {
  objectiveScale := 994
  eta := 39657940
  rows := #[⟨.assumptionRow 14, 1397⟩]
  caps := #[0, 0, 12079554, 3728712, 1176344, 403403, 141559, 51180, 6038808, 4581432, 2340084] }

theorem case_38_28_14_checked :
    (Witness.linear .conditional case_38_28_14).check 38 28 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_28_15 : Certificate := {
  objectiveScale := 633
  eta := 22078342
  rows := #[⟨.assumptionRow 15, 656⟩]
  caps := #[0, 0, 7248120, 2371092, 774956, 276458, 103675, 38760, 5242290, 4550424, 2714220] }

theorem case_38_28_15_checked :
    (Witness.linear .conditional case_38_28_15).check 38 28 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_28_16 : Certificate := {
  objectiveScale := 491
  eta := 3130839
  rows := #[⟨.assumptionRow 16, 319⟩]
  caps := #[0, 0, 1139544, 484296, 194152, 75712, 34723, 13566, 5161540, 4951590, 3321936] }

theorem case_38_28_16_checked :
    (Witness.linear .conditional case_38_28_16).check 38 28 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_28_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 16796, 16796, 11934] }

theorem case_38_28_17_checked :
    (Witness.linear .negative case_38_28_17).check 38 28 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_28_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4862] }

theorem case_38_28_18_checked :
    (Witness.linear .negative case_38_28_18).check 38 28 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_29_1_checked :
    (Witness.rising).check 38 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_29_2_checked :
    (Witness.rising).check 38 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_29_3_checked :
    (Witness.rising).check 38 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_29_4_checked :
    (Witness.rising).check 38 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_29_5_checked :
    (Witness.rising).check 38 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_29_6_checked :
    (Witness.rising).check 38 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_29_7_checked :
    (Witness.rising).check 38 29 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_29_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_38_29_8_checked :
    (Witness.linear .positive case_38_29_8).check 38 29 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_29_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_38_29_9_checked :
    (Witness.linear .positive case_38_29_9).check 38 29 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_29_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_38_29_10_checked :
    (Witness.linear .positive case_38_29_10).check 38 29 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_29_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_38_29_11_checked :
    (Witness.linear .positive case_38_29_11).check 38 29 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_29_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_38_29_12_checked :
    (Witness.linear .positive case_38_29_12).check 38 29 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_29_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_38_29_13_checked :
    (Witness.linear .positive case_38_29_13).check 38 29 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_29_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_38_29_14_checked :
    (Witness.linear .positive case_38_29_14).check 38 29 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_29_15 : Certificate := {
  objectiveScale := 9
  eta := 433466
  rows := #[⟨.assumptionRow 15, 10⟩]
  caps := #[0, 0, 135660, 42636, 15028, 5278, 1859, 106590, 164730, 116280] }

theorem case_38_29_15_checked :
    (Witness.linear .conditional case_38_29_15).check 38 29 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_29_16 : Certificate := {
  objectiveScale := 459
  eta := 2541687
  rows := #[⟨.assumptionRow 16, 292⟩]
  caps := #[0, 0, 969000, 390660, 165676, 60697, 29796, 16620934, 16046640, 10920630] }

theorem case_38_29_16_checked :
    (Witness.linear .conditional case_38_29_16).check 38 29 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_29_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 58786, 58786, 41990] }

theorem case_38_29_17_checked :
    (Witness.linear .negative case_38_29_17).check 38 29 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_29_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 16796] }

theorem case_38_29_18_checked :
    (Witness.linear .negative case_38_29_18).check 38 29 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_30_1_checked :
    (Witness.rising).check 38 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_30_2_checked :
    (Witness.rising).check 38 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_30_3_checked :
    (Witness.rising).check 38 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_30_4_checked :
    (Witness.rising).check 38 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_30_5_checked :
    (Witness.rising).check 38 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_30_6_checked :
    (Witness.rising).check 38 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_30_7_checked :
    (Witness.rising).check 38 30 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_30_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0] }

theorem case_38_30_8_checked :
    (Witness.linear .positive case_38_30_8).check 38 30 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_30_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1] }

theorem case_38_30_9_checked :
    (Witness.linear .positive case_38_30_9).check 38 30 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_30_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_38_30_10_checked :
    (Witness.linear .positive case_38_30_10).check 38 30 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_38_30_11_checked :
    (Witness.linear .positive case_38_30_11).check 38 30 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_30_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_38_30_12_checked :
    (Witness.linear .positive case_38_30_12).check 38 30 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_30_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_38_30_13_checked :
    (Witness.linear .positive case_38_30_13).check 38 30 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_30_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_38_30_14_checked :
    (Witness.linear .positive case_38_30_14).check 38 30 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_30_15 : Certificate := {
  objectiveScale := 13
  eta := 2288132
  rows := #[⟨.assumptionRow 15, 20⟩]
  caps := #[0, 0, 675070, 209950, 66300, 21320, 7007, 2365, 21318] }

theorem case_38_30_15_checked :
    (Witness.linear .conditional case_38_30_15).check 38 30 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_30_16 : Certificate := {
  objectiveScale := 983
  eta := 25677531
  rows := #[⟨.assumptionRow 16, 804⟩]
  caps := #[0, 0, 9155112, 3457392, 1231888, 422422, 178633, 58510804, 54652246] }

theorem case_38_30_16_checked :
    (Witness.linear .conditional case_38_30_16).check 38 30 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_30_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 208012, 208012, 149226] }

theorem case_38_30_17_checked :
    (Witness.linear .negative case_38_30_17).check 38 30 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_30_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 58786] }

theorem case_38_30_18_checked :
    (Witness.linear .negative case_38_30_18).check 38 30 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_30_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_38_30_19_checked :
    (Witness.linear .negative case_38_30_19).check 38 30 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_31_1_checked :
    (Witness.rising).check 38 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_31_2_checked :
    (Witness.rising).check 38 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_31_3_checked :
    (Witness.rising).check 38 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_31_4_checked :
    (Witness.rising).check 38 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_31_5_checked :
    (Witness.rising).check 38 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_31_6_checked :
    (Witness.rising).check 38 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_31_7_checked :
    (Witness.rising).check 38 31 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_31_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1] }

theorem case_38_31_8_checked :
    (Witness.linear .positive case_38_31_8).check 38 31 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_31_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_38_31_9_checked :
    (Witness.linear .positive case_38_31_9).check 38 31 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_31_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_38_31_10_checked :
    (Witness.linear .positive case_38_31_10).check 38 31 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_38_31_11_checked :
    (Witness.linear .positive case_38_31_11).check 38 31 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_38_31_12_checked :
    (Witness.linear .positive case_38_31_12).check 38 31 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_31_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42] }

theorem case_38_31_13_checked :
    (Witness.linear .positive case_38_31_13).check 38 31 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_31_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_38_31_14_checked :
    (Witness.linear .positive case_38_31_14).check 38 31 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_31_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_38_31_15_checked :
    (Witness.linear .positive case_38_31_15).check 38 31 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_31_16 : Certificate := {
  objectiveScale := 556
  eta := 39878872
  rows := #[⟨.assumptionRow 16, 539⟩]
  caps := #[0, 0, 12783694, 4563990, 1589364, 545272, 185725, 55160325] }

theorem case_38_31_16_checked :
    (Witness.linear .conditional case_38_31_16).check 38 31 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_31_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 742900, 742900, 534888] }

theorem case_38_31_17_checked :
    (Witness.linear .negative case_38_31_17).check 38 31 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_31_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 208012] }

theorem case_38_31_18_checked :
    (Witness.linear .negative case_38_31_18).check 38 31 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_31_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_38_31_19_checked :
    (Witness.linear .negative case_38_31_19).check 38 31 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_31_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_38_31_20_checked :
    (Witness.linear .negative case_38_31_20).check 38 31 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_32_1_checked :
    (Witness.rising).check 38 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_32_2_checked :
    (Witness.rising).check 38 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_32_3_checked :
    (Witness.rising).check 38 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_32_4_checked :
    (Witness.rising).check 38 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_32_5_checked :
    (Witness.rising).check 38 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_32_6_checked :
    (Witness.rising).check 38 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_32_7_checked :
    (Witness.rising).check 38 32 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_32_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1] }

theorem case_38_32_8_checked :
    (Witness.linear .positive case_38_32_8).check 38 32 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_32_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_38_32_9_checked :
    (Witness.linear .positive case_38_32_9).check 38 32 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_32_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_38_32_10_checked :
    (Witness.linear .positive case_38_32_10).check 38 32 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_38_32_11_checked :
    (Witness.linear .positive case_38_32_11).check 38 32 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_38_32_12_checked :
    (Witness.linear .positive case_38_32_12).check 38 32 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_32_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_38_32_13_checked :
    (Witness.linear .positive case_38_32_13).check 38 32 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_32_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429] }

theorem case_38_32_14_checked :
    (Witness.linear .positive case_38_32_14).check 38 32 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_32_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430] }

theorem case_38_32_15_checked :
    (Witness.linear .positive case_38_32_15).check 38 32 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_32_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862] }

theorem case_38_32_16_checked :
    (Witness.linear .positive case_38_32_16).check 38 32 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_32_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 2674440, 2674440, 1931540] }

theorem case_38_32_17_checked :
    (Witness.linear .negative case_38_32_17).check 38 32 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_32_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 742900] }

theorem case_38_32_18_checked :
    (Witness.linear .negative case_38_32_18).check 38 32 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_32_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_38_32_19_checked :
    (Witness.linear .negative case_38_32_19).check 38 32 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_32_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_38_32_20_checked :
    (Witness.linear .negative case_38_32_20).check 38 32 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_33_1_checked :
    (Witness.rising).check 38 33 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_33_2_checked :
    (Witness.rising).check 38 33 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_33_3_checked :
    (Witness.rising).check 38 33 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_33_4_checked :
    (Witness.rising).check 38 33 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_33_5_checked :
    (Witness.rising).check 38 33 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_33_6_checked :
    (Witness.rising).check 38 33 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_33_7_checked :
    (Witness.rising).check 38 33 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_33_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2] }

theorem case_38_33_8_checked :
    (Witness.linear .positive case_38_33_8).check 38 33 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_33_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_38_33_9_checked :
    (Witness.linear .positive case_38_33_9).check 38 33 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_33_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_38_33_10_checked :
    (Witness.linear .positive case_38_33_10).check 38 33 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_33_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_38_33_11_checked :
    (Witness.linear .positive case_38_33_11).check 38 33 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_33_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_38_33_12_checked :
    (Witness.linear .positive case_38_33_12).check 38 33 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_33_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_38_33_13_checked :
    (Witness.linear .positive case_38_33_13).check 38 33 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_33_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_38_33_14_checked :
    (Witness.linear .positive case_38_33_14).check 38 33 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_33_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862] }

theorem case_38_33_15_checked :
    (Witness.linear .positive case_38_33_15).check 38 33 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_33_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796] }

theorem case_38_33_16_checked :
    (Witness.linear .positive case_38_33_16).check 38 33 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_33_17 : Certificate := {
  objectiveScale := 529
  eta := 31418552
  rows := #[⟨.assumptionRow 17, 415⟩]
  caps := #[0, 0, 11181291, 3782976, 1449624, 553588] }

theorem case_38_33_17_checked :
    (Witness.linear .conditional case_38_33_17).check 38 33 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_33_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 2674440] }

theorem case_38_33_18_checked :
    (Witness.linear .negative case_38_33_18).check 38 33 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_33_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_38_33_19_checked :
    (Witness.linear .negative case_38_33_19).check 38 33 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_33_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_38_33_20_checked :
    (Witness.linear .negative case_38_33_20).check 38 33 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_33_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_38_33_21_checked :
    (Witness.linear .negative case_38_33_21).check 38 33 21 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_34_1_checked :
    (Witness.rising).check 38 34 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_34_2_checked :
    (Witness.rising).check 38 34 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_34_3_checked :
    (Witness.rising).check 38 34 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_34_4_checked :
    (Witness.rising).check 38 34 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_34_5_checked :
    (Witness.rising).check 38 34 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_34_6_checked :
    (Witness.rising).check 38 34 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_34_7_checked :
    (Witness.rising).check 38 34 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_34_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5] }

theorem case_38_34_8_checked :
    (Witness.linear .positive case_38_34_8).check 38 34 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_34_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_38_34_9_checked :
    (Witness.linear .positive case_38_34_9).check 38 34 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_34_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_38_34_10_checked :
    (Witness.linear .positive case_38_34_10).check 38 34 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_34_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_38_34_11_checked :
    (Witness.linear .positive case_38_34_11).check 38 34 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_34_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_38_34_12_checked :
    (Witness.linear .positive case_38_34_12).check 38 34 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_34_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_38_34_13_checked :
    (Witness.linear .positive case_38_34_13).check 38 34 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_34_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_38_34_14_checked :
    (Witness.linear .positive case_38_34_14).check 38 34 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_34_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796] }

theorem case_38_34_15_checked :
    (Witness.linear .positive case_38_34_15).check 38 34 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_34_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786] }

theorem case_38_34_16_checked :
    (Witness.linear .positive case_38_34_16).check 38 34 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_34_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012] }

theorem case_38_34_17_checked :
    (Witness.linear .positive case_38_34_17).check 38 34 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_34_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 9694845] }

theorem case_38_34_18_checked :
    (Witness.linear .negative case_38_34_18).check 38 34 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_34_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_38_34_19_checked :
    (Witness.linear .negative case_38_34_19).check 38 34 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_34_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_38_34_20_checked :
    (Witness.linear .negative case_38_34_20).check 38 34 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_34_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_38_34_21_checked :
    (Witness.linear .negative case_38_34_21).check 38 34 21 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_34_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_38_34_22_checked :
    (Witness.linear .negative case_38_34_22).check 38 34 22 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_35_1_checked :
    (Witness.rising).check 38 35 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_35_2_checked :
    (Witness.rising).check 38 35 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_35_3_checked :
    (Witness.rising).check 38 35 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_35_4_checked :
    (Witness.rising).check 38 35 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_35_5_checked :
    (Witness.rising).check 38 35 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_35_6_checked :
    (Witness.rising).check 38 35 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_35_7_checked :
    (Witness.rising).check 38 35 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_35_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14] }

theorem case_38_35_8_checked :
    (Witness.linear .positive case_38_35_8).check 38 35 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_35_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_38_35_9_checked :
    (Witness.linear .positive case_38_35_9).check 38 35 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_35_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_38_35_10_checked :
    (Witness.linear .positive case_38_35_10).check 38 35 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_35_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_38_35_11_checked :
    (Witness.linear .positive case_38_35_11).check 38 35 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_35_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_38_35_12_checked :
    (Witness.linear .positive case_38_35_12).check 38 35 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_35_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_38_35_13_checked :
    (Witness.linear .positive case_38_35_13).check 38 35 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_35_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_38_35_14_checked :
    (Witness.linear .positive case_38_35_14).check 38 35 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_35_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_38_35_15_checked :
    (Witness.linear .positive case_38_35_15).check 38 35 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_35_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012] }

theorem case_38_35_16_checked :
    (Witness.linear .positive case_38_35_16).check 38 35 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_35_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900] }

theorem case_38_35_17_checked :
    (Witness.linear .positive case_38_35_17).check 38 35 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_35_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 35357670] }

theorem case_38_35_18_checked :
    (Witness.linear .negative case_38_35_18).check 38 35 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_35_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_38_35_19_checked :
    (Witness.linear .negative case_38_35_19).check 38 35 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_35_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_38_35_20_checked :
    (Witness.linear .negative case_38_35_20).check 38 35 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_35_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_38_35_21_checked :
    (Witness.linear .negative case_38_35_21).check 38 35 21 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_35_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_38_35_22_checked :
    (Witness.linear .negative case_38_35_22).check 38 35 22 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_36_1_checked :
    (Witness.rising).check 38 36 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_36_2_checked :
    (Witness.rising).check 38 36 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_36_3_checked :
    (Witness.rising).check 38 36 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_36_4_checked :
    (Witness.rising).check 38 36 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_36_5_checked :
    (Witness.rising).check 38 36 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_36_6_checked :
    (Witness.rising).check 38 36 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_36_7_checked :
    (Witness.rising).check 38 36 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_36_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_38_36_8_checked :
    (Witness.linear .positive case_38_36_8).check 38 36 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_36_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_38_36_9_checked :
    (Witness.linear .positive case_38_36_9).check 38 36 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_36_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_38_36_10_checked :
    (Witness.linear .positive case_38_36_10).check 38 36 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_36_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_38_36_11_checked :
    (Witness.linear .positive case_38_36_11).check 38 36 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_36_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_38_36_12_checked :
    (Witness.linear .positive case_38_36_12).check 38 36 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_36_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_38_36_13_checked :
    (Witness.linear .positive case_38_36_13).check 38 36 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_36_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_38_36_14_checked :
    (Witness.linear .positive case_38_36_14).check 38 36 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_36_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_38_36_15_checked :
    (Witness.linear .positive case_38_36_15).check 38 36 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_36_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900] }

theorem case_38_36_16_checked :
    (Witness.linear .positive case_38_36_16).check 38 36 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_36_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440] }

theorem case_38_36_17_checked :
    (Witness.linear .positive case_38_36_17).check 38 36 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_36_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845] }

theorem case_38_36_18_checked :
    (Witness.linear .positive case_38_36_18).check 38 36 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_36_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_38_36_19_checked :
    (Witness.linear .negative case_38_36_19).check 38 36 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_36_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_38_36_20_checked :
    (Witness.linear .negative case_38_36_20).check 38 36 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_36_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_38_36_21_checked :
    (Witness.linear .negative case_38_36_21).check 38 36 21 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_36_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_38_36_22_checked :
    (Witness.linear .negative case_38_36_22).check 38 36 22 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_36_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_38_36_23_checked :
    (Witness.linear .negative case_38_36_23).check 38 36 23 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_37_1_checked :
    (Witness.rising).check 38 37 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_37_2_checked :
    (Witness.rising).check 38 37 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_37_3_checked :
    (Witness.rising).check 38 37 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_37_4_checked :
    (Witness.rising).check 38 37 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_37_5_checked :
    (Witness.rising).check 38 37 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_37_6_checked :
    (Witness.rising).check 38 37 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_38_37_7_checked :
    (Witness.rising).check 38 37 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_37_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_38_37_8_checked :
    (Witness.linear .positive case_38_37_8).check 38 37 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_37_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_38_37_9_checked :
    (Witness.linear .positive case_38_37_9).check 38 37 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_37_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_38_37_10_checked :
    (Witness.linear .positive case_38_37_10).check 38 37 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_37_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_38_37_11_checked :
    (Witness.linear .positive case_38_37_11).check 38 37 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_37_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_38_37_12_checked :
    (Witness.linear .positive case_38_37_12).check 38 37 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_37_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_38_37_13_checked :
    (Witness.linear .positive case_38_37_13).check 38 37 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_37_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_38_37_14_checked :
    (Witness.linear .positive case_38_37_14).check 38 37 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_37_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_38_37_15_checked :
    (Witness.linear .positive case_38_37_15).check 38 37 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_37_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_38_37_16_checked :
    (Witness.linear .positive case_38_37_16).check 38 37 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_37_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0] }

theorem case_38_37_17_checked :
    (Witness.linear .positive case_38_37_17).check 38 37 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_37_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0] }

theorem case_38_37_18_checked :
    (Witness.linear .positive case_38_37_18).check 38 37 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_37_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_38_37_19_checked :
    (Witness.linear .negative case_38_37_19).check 38 37 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_37_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_38_37_20_checked :
    (Witness.linear .negative case_38_37_20).check 38 37 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_37_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_38_37_21_checked :
    (Witness.linear .negative case_38_37_21).check 38 37 21 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_37_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_38_37_22_checked :
    (Witness.linear .negative case_38_37_22).check 38 37 22 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_37_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_38_37_23_checked :
    (Witness.linear .negative case_38_37_23).check 38 37 23 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_38_37_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_38_37_24_checked :
    (Witness.linear .negative case_38_37_24).check 38 37 24 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_38 (a k : ℕ) (h : Domain 38 a k) :
    ∃ w : Witness, w.check 38 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 19 ≤ a := by omega
  have haHi : a ≤ 37 := by omega
  interval_cases a

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_38_19_1_checked⟩

    · exact ⟨Witness.rising, case_38_19_2_checked⟩

    · exact ⟨Witness.rising, case_38_19_3_checked⟩

    · exact ⟨Witness.rising, case_38_19_4_checked⟩

    · exact ⟨Witness.rising, case_38_19_5_checked⟩

    · exact ⟨Witness.rising, case_38_19_6_checked⟩

    · exact ⟨Witness.rising, case_38_19_7_checked⟩

    · exact ⟨Witness.rising, case_38_19_8_checked⟩

    · exact ⟨Witness.linear .positive case_38_19_9, case_38_19_9_checked⟩

    · exact ⟨Witness.linear .positive case_38_19_10, case_38_19_10_checked⟩

    · exact ⟨Witness.linear .conditional case_38_19_11, case_38_19_11_checked⟩

    · exact ⟨Witness.linear .conditional case_38_19_12, case_38_19_12_checked⟩

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_38_20_1_checked⟩

    · exact ⟨Witness.rising, case_38_20_2_checked⟩

    · exact ⟨Witness.rising, case_38_20_3_checked⟩

    · exact ⟨Witness.rising, case_38_20_4_checked⟩

    · exact ⟨Witness.rising, case_38_20_5_checked⟩

    · exact ⟨Witness.rising, case_38_20_6_checked⟩

    · exact ⟨Witness.rising, case_38_20_7_checked⟩

    · exact ⟨Witness.rising, case_38_20_8_checked⟩

    · exact ⟨Witness.linear .positive case_38_20_9, case_38_20_9_checked⟩

    · exact ⟨Witness.linear .positive case_38_20_10, case_38_20_10_checked⟩

    · exact ⟨Witness.linear .conditional case_38_20_11, case_38_20_11_checked⟩

    · exact ⟨Witness.linear .conditional case_38_20_12, case_38_20_12_checked⟩

  · have hkHi : k ≤ 13 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_38_21_1_checked⟩

    · exact ⟨Witness.rising, case_38_21_2_checked⟩

    · exact ⟨Witness.rising, case_38_21_3_checked⟩

    · exact ⟨Witness.rising, case_38_21_4_checked⟩

    · exact ⟨Witness.rising, case_38_21_5_checked⟩

    · exact ⟨Witness.rising, case_38_21_6_checked⟩

    · exact ⟨Witness.rising, case_38_21_7_checked⟩

    · exact ⟨Witness.rising, case_38_21_8_checked⟩

    · exact ⟨Witness.linear .positive case_38_21_9, case_38_21_9_checked⟩

    · exact ⟨Witness.linear .positive case_38_21_10, case_38_21_10_checked⟩

    · exact ⟨Witness.linear .positive case_38_21_11, case_38_21_11_checked⟩

    · exact ⟨Witness.linear .conditional case_38_21_12, case_38_21_12_checked⟩

    · exact ⟨Witness.linear .conditional case_38_21_13, case_38_21_13_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_38_22_1_checked⟩

    · exact ⟨Witness.rising, case_38_22_2_checked⟩

    · exact ⟨Witness.rising, case_38_22_3_checked⟩

    · exact ⟨Witness.rising, case_38_22_4_checked⟩

    · exact ⟨Witness.rising, case_38_22_5_checked⟩

    · exact ⟨Witness.rising, case_38_22_6_checked⟩

    · exact ⟨Witness.rising, case_38_22_7_checked⟩

    · exact ⟨Witness.rising, case_38_22_8_checked⟩

    · exact ⟨Witness.linear .positive case_38_22_9, case_38_22_9_checked⟩

    · exact ⟨Witness.linear .positive case_38_22_10, case_38_22_10_checked⟩

    · exact ⟨Witness.linear .positive case_38_22_11, case_38_22_11_checked⟩

    · exact ⟨Witness.linear .conditional case_38_22_12, case_38_22_12_checked⟩

    · exact ⟨Witness.linear .conditional case_38_22_13, case_38_22_13_checked⟩

    · exact ⟨Witness.linear .negative case_38_22_14, case_38_22_14_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_38_23_1_checked⟩

    · exact ⟨Witness.rising, case_38_23_2_checked⟩

    · exact ⟨Witness.rising, case_38_23_3_checked⟩

    · exact ⟨Witness.rising, case_38_23_4_checked⟩

    · exact ⟨Witness.rising, case_38_23_5_checked⟩

    · exact ⟨Witness.rising, case_38_23_6_checked⟩

    · exact ⟨Witness.rising, case_38_23_7_checked⟩

    · exact ⟨Witness.rising, case_38_23_8_checked⟩

    · exact ⟨Witness.linear .positive case_38_23_9, case_38_23_9_checked⟩

    · exact ⟨Witness.linear .positive case_38_23_10, case_38_23_10_checked⟩

    · exact ⟨Witness.linear .positive case_38_23_11, case_38_23_11_checked⟩

    · exact ⟨Witness.linear .conditional case_38_23_12, case_38_23_12_checked⟩

    · exact ⟨Witness.linear .conditional case_38_23_13, case_38_23_13_checked⟩

    · exact ⟨Witness.linear .negative case_38_23_14, case_38_23_14_checked⟩

  · have hkHi : k ≤ 15 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_38_24_1_checked⟩

    · exact ⟨Witness.rising, case_38_24_2_checked⟩

    · exact ⟨Witness.rising, case_38_24_3_checked⟩

    · exact ⟨Witness.rising, case_38_24_4_checked⟩

    · exact ⟨Witness.rising, case_38_24_5_checked⟩

    · exact ⟨Witness.rising, case_38_24_6_checked⟩

    · exact ⟨Witness.rising, case_38_24_7_checked⟩

    · exact ⟨Witness.rising, case_38_24_8_checked⟩

    · exact ⟨Witness.linear .positive case_38_24_9, case_38_24_9_checked⟩

    · exact ⟨Witness.linear .positive case_38_24_10, case_38_24_10_checked⟩

    · exact ⟨Witness.linear .conditional case_38_24_11, case_38_24_11_checked⟩

    · exact ⟨Witness.linear .conditional case_38_24_12, case_38_24_12_checked⟩

    · exact ⟨Witness.linear .conditional case_38_24_13, case_38_24_13_checked⟩

    · exact ⟨Witness.linear .conditional case_38_24_14, case_38_24_14_checked⟩

    · exact ⟨Witness.linear .negative case_38_24_15, case_38_24_15_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_38_25_1_checked⟩

    · exact ⟨Witness.rising, case_38_25_2_checked⟩

    · exact ⟨Witness.rising, case_38_25_3_checked⟩

    · exact ⟨Witness.rising, case_38_25_4_checked⟩

    · exact ⟨Witness.rising, case_38_25_5_checked⟩

    · exact ⟨Witness.rising, case_38_25_6_checked⟩

    · exact ⟨Witness.rising, case_38_25_7_checked⟩

    · exact ⟨Witness.linear .positive case_38_25_8, case_38_25_8_checked⟩

    · exact ⟨Witness.linear .positive case_38_25_9, case_38_25_9_checked⟩

    · exact ⟨Witness.linear .positive case_38_25_10, case_38_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_38_25_11, case_38_25_11_checked⟩

    · exact ⟨Witness.linear .conditional case_38_25_12, case_38_25_12_checked⟩

    · exact ⟨Witness.linear .conditional case_38_25_13, case_38_25_13_checked⟩

    · exact ⟨Witness.linear .conditional case_38_25_14, case_38_25_14_checked⟩

    · exact ⟨Witness.linear .negative case_38_25_15, case_38_25_15_checked⟩

    · exact ⟨Witness.linear .conditional case_38_25_16, case_38_25_16_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_38_26_1_checked⟩

    · exact ⟨Witness.rising, case_38_26_2_checked⟩

    · exact ⟨Witness.rising, case_38_26_3_checked⟩

    · exact ⟨Witness.rising, case_38_26_4_checked⟩

    · exact ⟨Witness.rising, case_38_26_5_checked⟩

    · exact ⟨Witness.rising, case_38_26_6_checked⟩

    · exact ⟨Witness.rising, case_38_26_7_checked⟩

    · exact ⟨Witness.linear .positive case_38_26_8, case_38_26_8_checked⟩

    · exact ⟨Witness.linear .positive case_38_26_9, case_38_26_9_checked⟩

    · exact ⟨Witness.linear .positive case_38_26_10, case_38_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_38_26_11, case_38_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_38_26_12, case_38_26_12_checked⟩

    · exact ⟨Witness.linear .conditional case_38_26_13, case_38_26_13_checked⟩

    · exact ⟨Witness.linear .conditional case_38_26_14, case_38_26_14_checked⟩

    · exact ⟨Witness.linear .negative case_38_26_15, case_38_26_15_checked⟩

    · exact ⟨Witness.linear .conditional case_38_26_16, case_38_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_38_27_1_checked⟩

    · exact ⟨Witness.rising, case_38_27_2_checked⟩

    · exact ⟨Witness.rising, case_38_27_3_checked⟩

    · exact ⟨Witness.rising, case_38_27_4_checked⟩

    · exact ⟨Witness.rising, case_38_27_5_checked⟩

    · exact ⟨Witness.rising, case_38_27_6_checked⟩

    · exact ⟨Witness.rising, case_38_27_7_checked⟩

    · exact ⟨Witness.linear .positive case_38_27_8, case_38_27_8_checked⟩

    · exact ⟨Witness.linear .positive case_38_27_9, case_38_27_9_checked⟩

    · exact ⟨Witness.linear .positive case_38_27_10, case_38_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_38_27_11, case_38_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_38_27_12, case_38_27_12_checked⟩

    · exact ⟨Witness.linear .conditional case_38_27_13, case_38_27_13_checked⟩

    · exact ⟨Witness.linear .conditional case_38_27_14, case_38_27_14_checked⟩

    · exact ⟨Witness.linear .conditional case_38_27_15, case_38_27_15_checked⟩

    · exact ⟨Witness.linear .conditional case_38_27_16, case_38_27_16_checked⟩

    · exact ⟨Witness.linear .negative case_38_27_17, case_38_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_38_28_1_checked⟩

    · exact ⟨Witness.rising, case_38_28_2_checked⟩

    · exact ⟨Witness.rising, case_38_28_3_checked⟩

    · exact ⟨Witness.rising, case_38_28_4_checked⟩

    · exact ⟨Witness.rising, case_38_28_5_checked⟩

    · exact ⟨Witness.rising, case_38_28_6_checked⟩

    · exact ⟨Witness.rising, case_38_28_7_checked⟩

    · exact ⟨Witness.linear .positive case_38_28_8, case_38_28_8_checked⟩

    · exact ⟨Witness.linear .positive case_38_28_9, case_38_28_9_checked⟩

    · exact ⟨Witness.linear .positive case_38_28_10, case_38_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_38_28_11, case_38_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_38_28_12, case_38_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_38_28_13, case_38_28_13_checked⟩

    · exact ⟨Witness.linear .conditional case_38_28_14, case_38_28_14_checked⟩

    · exact ⟨Witness.linear .conditional case_38_28_15, case_38_28_15_checked⟩

    · exact ⟨Witness.linear .conditional case_38_28_16, case_38_28_16_checked⟩

    · exact ⟨Witness.linear .negative case_38_28_17, case_38_28_17_checked⟩

    · exact ⟨Witness.linear .negative case_38_28_18, case_38_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_38_29_1_checked⟩

    · exact ⟨Witness.rising, case_38_29_2_checked⟩

    · exact ⟨Witness.rising, case_38_29_3_checked⟩

    · exact ⟨Witness.rising, case_38_29_4_checked⟩

    · exact ⟨Witness.rising, case_38_29_5_checked⟩

    · exact ⟨Witness.rising, case_38_29_6_checked⟩

    · exact ⟨Witness.rising, case_38_29_7_checked⟩

    · exact ⟨Witness.linear .positive case_38_29_8, case_38_29_8_checked⟩

    · exact ⟨Witness.linear .positive case_38_29_9, case_38_29_9_checked⟩

    · exact ⟨Witness.linear .positive case_38_29_10, case_38_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_38_29_11, case_38_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_38_29_12, case_38_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_38_29_13, case_38_29_13_checked⟩

    · exact ⟨Witness.linear .positive case_38_29_14, case_38_29_14_checked⟩

    · exact ⟨Witness.linear .conditional case_38_29_15, case_38_29_15_checked⟩

    · exact ⟨Witness.linear .conditional case_38_29_16, case_38_29_16_checked⟩

    · exact ⟨Witness.linear .negative case_38_29_17, case_38_29_17_checked⟩

    · exact ⟨Witness.linear .negative case_38_29_18, case_38_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_38_30_1_checked⟩

    · exact ⟨Witness.rising, case_38_30_2_checked⟩

    · exact ⟨Witness.rising, case_38_30_3_checked⟩

    · exact ⟨Witness.rising, case_38_30_4_checked⟩

    · exact ⟨Witness.rising, case_38_30_5_checked⟩

    · exact ⟨Witness.rising, case_38_30_6_checked⟩

    · exact ⟨Witness.rising, case_38_30_7_checked⟩

    · exact ⟨Witness.linear .positive case_38_30_8, case_38_30_8_checked⟩

    · exact ⟨Witness.linear .positive case_38_30_9, case_38_30_9_checked⟩

    · exact ⟨Witness.linear .positive case_38_30_10, case_38_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_38_30_11, case_38_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_38_30_12, case_38_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_38_30_13, case_38_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_38_30_14, case_38_30_14_checked⟩

    · exact ⟨Witness.linear .conditional case_38_30_15, case_38_30_15_checked⟩

    · exact ⟨Witness.linear .conditional case_38_30_16, case_38_30_16_checked⟩

    · exact ⟨Witness.linear .negative case_38_30_17, case_38_30_17_checked⟩

    · exact ⟨Witness.linear .negative case_38_30_18, case_38_30_18_checked⟩

    · exact ⟨Witness.linear .negative case_38_30_19, case_38_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_38_31_1_checked⟩

    · exact ⟨Witness.rising, case_38_31_2_checked⟩

    · exact ⟨Witness.rising, case_38_31_3_checked⟩

    · exact ⟨Witness.rising, case_38_31_4_checked⟩

    · exact ⟨Witness.rising, case_38_31_5_checked⟩

    · exact ⟨Witness.rising, case_38_31_6_checked⟩

    · exact ⟨Witness.rising, case_38_31_7_checked⟩

    · exact ⟨Witness.linear .positive case_38_31_8, case_38_31_8_checked⟩

    · exact ⟨Witness.linear .positive case_38_31_9, case_38_31_9_checked⟩

    · exact ⟨Witness.linear .positive case_38_31_10, case_38_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_38_31_11, case_38_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_38_31_12, case_38_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_38_31_13, case_38_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_38_31_14, case_38_31_14_checked⟩

    · exact ⟨Witness.linear .positive case_38_31_15, case_38_31_15_checked⟩

    · exact ⟨Witness.linear .conditional case_38_31_16, case_38_31_16_checked⟩

    · exact ⟨Witness.linear .negative case_38_31_17, case_38_31_17_checked⟩

    · exact ⟨Witness.linear .negative case_38_31_18, case_38_31_18_checked⟩

    · exact ⟨Witness.linear .negative case_38_31_19, case_38_31_19_checked⟩

    · exact ⟨Witness.linear .negative case_38_31_20, case_38_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_38_32_1_checked⟩

    · exact ⟨Witness.rising, case_38_32_2_checked⟩

    · exact ⟨Witness.rising, case_38_32_3_checked⟩

    · exact ⟨Witness.rising, case_38_32_4_checked⟩

    · exact ⟨Witness.rising, case_38_32_5_checked⟩

    · exact ⟨Witness.rising, case_38_32_6_checked⟩

    · exact ⟨Witness.rising, case_38_32_7_checked⟩

    · exact ⟨Witness.linear .positive case_38_32_8, case_38_32_8_checked⟩

    · exact ⟨Witness.linear .positive case_38_32_9, case_38_32_9_checked⟩

    · exact ⟨Witness.linear .positive case_38_32_10, case_38_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_38_32_11, case_38_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_38_32_12, case_38_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_38_32_13, case_38_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_38_32_14, case_38_32_14_checked⟩

    · exact ⟨Witness.linear .positive case_38_32_15, case_38_32_15_checked⟩

    · exact ⟨Witness.linear .positive case_38_32_16, case_38_32_16_checked⟩

    · exact ⟨Witness.linear .negative case_38_32_17, case_38_32_17_checked⟩

    · exact ⟨Witness.linear .negative case_38_32_18, case_38_32_18_checked⟩

    · exact ⟨Witness.linear .negative case_38_32_19, case_38_32_19_checked⟩

    · exact ⟨Witness.linear .negative case_38_32_20, case_38_32_20_checked⟩

  · have hkHi : k ≤ 21 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_38_33_1_checked⟩

    · exact ⟨Witness.rising, case_38_33_2_checked⟩

    · exact ⟨Witness.rising, case_38_33_3_checked⟩

    · exact ⟨Witness.rising, case_38_33_4_checked⟩

    · exact ⟨Witness.rising, case_38_33_5_checked⟩

    · exact ⟨Witness.rising, case_38_33_6_checked⟩

    · exact ⟨Witness.rising, case_38_33_7_checked⟩

    · exact ⟨Witness.linear .positive case_38_33_8, case_38_33_8_checked⟩

    · exact ⟨Witness.linear .positive case_38_33_9, case_38_33_9_checked⟩

    · exact ⟨Witness.linear .positive case_38_33_10, case_38_33_10_checked⟩

    · exact ⟨Witness.linear .positive case_38_33_11, case_38_33_11_checked⟩

    · exact ⟨Witness.linear .positive case_38_33_12, case_38_33_12_checked⟩

    · exact ⟨Witness.linear .positive case_38_33_13, case_38_33_13_checked⟩

    · exact ⟨Witness.linear .positive case_38_33_14, case_38_33_14_checked⟩

    · exact ⟨Witness.linear .positive case_38_33_15, case_38_33_15_checked⟩

    · exact ⟨Witness.linear .positive case_38_33_16, case_38_33_16_checked⟩

    · exact ⟨Witness.linear .conditional case_38_33_17, case_38_33_17_checked⟩

    · exact ⟨Witness.linear .negative case_38_33_18, case_38_33_18_checked⟩

    · exact ⟨Witness.linear .negative case_38_33_19, case_38_33_19_checked⟩

    · exact ⟨Witness.linear .negative case_38_33_20, case_38_33_20_checked⟩

    · exact ⟨Witness.linear .negative case_38_33_21, case_38_33_21_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_38_34_1_checked⟩

    · exact ⟨Witness.rising, case_38_34_2_checked⟩

    · exact ⟨Witness.rising, case_38_34_3_checked⟩

    · exact ⟨Witness.rising, case_38_34_4_checked⟩

    · exact ⟨Witness.rising, case_38_34_5_checked⟩

    · exact ⟨Witness.rising, case_38_34_6_checked⟩

    · exact ⟨Witness.rising, case_38_34_7_checked⟩

    · exact ⟨Witness.linear .positive case_38_34_8, case_38_34_8_checked⟩

    · exact ⟨Witness.linear .positive case_38_34_9, case_38_34_9_checked⟩

    · exact ⟨Witness.linear .positive case_38_34_10, case_38_34_10_checked⟩

    · exact ⟨Witness.linear .positive case_38_34_11, case_38_34_11_checked⟩

    · exact ⟨Witness.linear .positive case_38_34_12, case_38_34_12_checked⟩

    · exact ⟨Witness.linear .positive case_38_34_13, case_38_34_13_checked⟩

    · exact ⟨Witness.linear .positive case_38_34_14, case_38_34_14_checked⟩

    · exact ⟨Witness.linear .positive case_38_34_15, case_38_34_15_checked⟩

    · exact ⟨Witness.linear .positive case_38_34_16, case_38_34_16_checked⟩

    · exact ⟨Witness.linear .positive case_38_34_17, case_38_34_17_checked⟩

    · exact ⟨Witness.linear .negative case_38_34_18, case_38_34_18_checked⟩

    · exact ⟨Witness.linear .negative case_38_34_19, case_38_34_19_checked⟩

    · exact ⟨Witness.linear .negative case_38_34_20, case_38_34_20_checked⟩

    · exact ⟨Witness.linear .negative case_38_34_21, case_38_34_21_checked⟩

    · exact ⟨Witness.linear .negative case_38_34_22, case_38_34_22_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_38_35_1_checked⟩

    · exact ⟨Witness.rising, case_38_35_2_checked⟩

    · exact ⟨Witness.rising, case_38_35_3_checked⟩

    · exact ⟨Witness.rising, case_38_35_4_checked⟩

    · exact ⟨Witness.rising, case_38_35_5_checked⟩

    · exact ⟨Witness.rising, case_38_35_6_checked⟩

    · exact ⟨Witness.rising, case_38_35_7_checked⟩

    · exact ⟨Witness.linear .positive case_38_35_8, case_38_35_8_checked⟩

    · exact ⟨Witness.linear .positive case_38_35_9, case_38_35_9_checked⟩

    · exact ⟨Witness.linear .positive case_38_35_10, case_38_35_10_checked⟩

    · exact ⟨Witness.linear .positive case_38_35_11, case_38_35_11_checked⟩

    · exact ⟨Witness.linear .positive case_38_35_12, case_38_35_12_checked⟩

    · exact ⟨Witness.linear .positive case_38_35_13, case_38_35_13_checked⟩

    · exact ⟨Witness.linear .positive case_38_35_14, case_38_35_14_checked⟩

    · exact ⟨Witness.linear .positive case_38_35_15, case_38_35_15_checked⟩

    · exact ⟨Witness.linear .positive case_38_35_16, case_38_35_16_checked⟩

    · exact ⟨Witness.linear .positive case_38_35_17, case_38_35_17_checked⟩

    · exact ⟨Witness.linear .negative case_38_35_18, case_38_35_18_checked⟩

    · exact ⟨Witness.linear .negative case_38_35_19, case_38_35_19_checked⟩

    · exact ⟨Witness.linear .negative case_38_35_20, case_38_35_20_checked⟩

    · exact ⟨Witness.linear .negative case_38_35_21, case_38_35_21_checked⟩

    · exact ⟨Witness.linear .negative case_38_35_22, case_38_35_22_checked⟩

  · have hkHi : k ≤ 23 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_38_36_1_checked⟩

    · exact ⟨Witness.rising, case_38_36_2_checked⟩

    · exact ⟨Witness.rising, case_38_36_3_checked⟩

    · exact ⟨Witness.rising, case_38_36_4_checked⟩

    · exact ⟨Witness.rising, case_38_36_5_checked⟩

    · exact ⟨Witness.rising, case_38_36_6_checked⟩

    · exact ⟨Witness.rising, case_38_36_7_checked⟩

    · exact ⟨Witness.linear .positive case_38_36_8, case_38_36_8_checked⟩

    · exact ⟨Witness.linear .positive case_38_36_9, case_38_36_9_checked⟩

    · exact ⟨Witness.linear .positive case_38_36_10, case_38_36_10_checked⟩

    · exact ⟨Witness.linear .positive case_38_36_11, case_38_36_11_checked⟩

    · exact ⟨Witness.linear .positive case_38_36_12, case_38_36_12_checked⟩

    · exact ⟨Witness.linear .positive case_38_36_13, case_38_36_13_checked⟩

    · exact ⟨Witness.linear .positive case_38_36_14, case_38_36_14_checked⟩

    · exact ⟨Witness.linear .positive case_38_36_15, case_38_36_15_checked⟩

    · exact ⟨Witness.linear .positive case_38_36_16, case_38_36_16_checked⟩

    · exact ⟨Witness.linear .positive case_38_36_17, case_38_36_17_checked⟩

    · exact ⟨Witness.linear .positive case_38_36_18, case_38_36_18_checked⟩

    · exact ⟨Witness.linear .negative case_38_36_19, case_38_36_19_checked⟩

    · exact ⟨Witness.linear .negative case_38_36_20, case_38_36_20_checked⟩

    · exact ⟨Witness.linear .negative case_38_36_21, case_38_36_21_checked⟩

    · exact ⟨Witness.linear .negative case_38_36_22, case_38_36_22_checked⟩

    · exact ⟨Witness.linear .negative case_38_36_23, case_38_36_23_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_38_37_1_checked⟩

    · exact ⟨Witness.rising, case_38_37_2_checked⟩

    · exact ⟨Witness.rising, case_38_37_3_checked⟩

    · exact ⟨Witness.rising, case_38_37_4_checked⟩

    · exact ⟨Witness.rising, case_38_37_5_checked⟩

    · exact ⟨Witness.rising, case_38_37_6_checked⟩

    · exact ⟨Witness.rising, case_38_37_7_checked⟩

    · exact ⟨Witness.linear .positive case_38_37_8, case_38_37_8_checked⟩

    · exact ⟨Witness.linear .positive case_38_37_9, case_38_37_9_checked⟩

    · exact ⟨Witness.linear .positive case_38_37_10, case_38_37_10_checked⟩

    · exact ⟨Witness.linear .positive case_38_37_11, case_38_37_11_checked⟩

    · exact ⟨Witness.linear .positive case_38_37_12, case_38_37_12_checked⟩

    · exact ⟨Witness.linear .positive case_38_37_13, case_38_37_13_checked⟩

    · exact ⟨Witness.linear .positive case_38_37_14, case_38_37_14_checked⟩

    · exact ⟨Witness.linear .positive case_38_37_15, case_38_37_15_checked⟩

    · exact ⟨Witness.linear .positive case_38_37_16, case_38_37_16_checked⟩

    · exact ⟨Witness.linear .positive case_38_37_17, case_38_37_17_checked⟩

    · exact ⟨Witness.linear .positive case_38_37_18, case_38_37_18_checked⟩

    · exact ⟨Witness.linear .negative case_38_37_19, case_38_37_19_checked⟩

    · exact ⟨Witness.linear .negative case_38_37_20, case_38_37_20_checked⟩

    · exact ⟨Witness.linear .negative case_38_37_21, case_38_37_21_checked⟩

    · exact ⟨Witness.linear .negative case_38_37_22, case_38_37_22_checked⟩

    · exact ⟨Witness.linear .negative case_38_37_23, case_38_37_23_checked⟩

    · exact ⟨Witness.linear .negative case_38_37_24, case_38_37_24_checked⟩


#print axioms coverage_38
end ForestUnimodality.FiniteRows.FiniteData
