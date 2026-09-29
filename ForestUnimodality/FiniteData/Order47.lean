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

theorem case_47_24_1_checked :
    (Witness.rising).check 47 24 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_24_2_checked :
    (Witness.rising).check 47 24 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_24_3_checked :
    (Witness.rising).check 47 24 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_24_4_checked :
    (Witness.rising).check 47 24 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_24_5_checked :
    (Witness.rising).check 47 24 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_24_6_checked :
    (Witness.rising).check 47 24 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_24_7_checked :
    (Witness.rising).check 47 24 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_24_8_checked :
    (Witness.rising).check 47 24 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_24_9_checked :
    (Witness.rising).check 47 24 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_24_10 : Certificate := {
  objectiveScale := 20292772500000
  eta := 1841151235603680000
  rows := #[⟨.count 2, 435181201142688000⟩, ⟨.count 3, 69043171335138000⟩, ⟨.count 4, 9743754915694800⟩, ⟨.count 5, 1620288595926000⟩, ⟨.count 6, 314619144840000⟩, ⟨.count 7, 75570284790000⟩, ⟨.count 8, 25909811928000⟩, ⟨.count 9, 20080104244200⟩, ⟨.count 11, 3131955288000⟩, ⟨.path 10, 6111049132188⟩, ⟨.path 11, 3032320005000⟩, ⟨.privateRow 10 0, 191239088040⟩, ⟨.hall 8 3, 24320107350⟩, ⟨.hall 8 4, 3954489000⟩, ⟨.hall 7 5, 12997474875⟩, ⟨.hall 7 6, 1601885250⟩, ⟨.hall 6 8, 8064760900⟩, ⟨.hall 6 9, 395448900⟩, ⟨.hall 5 13, 49379079750⟩, ⟨.hall 9 14, 129549059640⟩, ⟨.hall 4 17, 2849051144940⟩]
  caps := #[0, 0, 0, 119840213132640, 17575492066704, 4905090554364, 0, 1137340043840, 1676429314560, 212668255800, 10554692148, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_24_10_checked :
    (Witness.linear .positive case_47_24_10).check 47 24 10 = true := by
  change case_47_24_10.check 47 24 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_24_11 : Certificate := {
  objectiveScale := 1681279600000
  eta := 227607979163685120
  rows := #[⟨.count 2, 60227436044936160⟩, ⟨.count 3, 10979234616430080⟩, ⟨.count 4, 1794682581531840⟩, ⟨.count 5, 327821276502720⟩, ⟨.count 6, 68527611472320⟩, ⟨.count 7, 16396511171040⟩, ⟨.count 8, 4766427666000⟩, ⟨.count 9, 1944702487728⟩, ⟨.count 10, 1715913959760⟩, ⟨.path 11, 246564077760⟩, ⟨.path 12, 365600715480⟩, ⟨.privateRow 8 7, 123927119316⟩, ⟨.privateRow 8 8, 193305122010⟩, ⟨.privateRow 9 4, 26480153700⟩, ⟨.privateRow 9 5, 132882225840⟩, ⟨.privateRow 10 2, 41483634192⟩, ⟨.privateRow 11 0, 52079021280⟩, ⟨.privateRow 12 0, 27921676860⟩, ⟨.hall 12 1, 28284296040⟩, ⟨.hall 9 3, 4923562644⟩, ⟨.hall 8 5, 2170526085⟩, ⟨.hall 7 7, 1839123468⟩, ⟨.hall 6 9, 738587304⟩, ⟨.hall 6 10, 1864985850⟩, ⟨.hall 10 13, 17509326120⟩, ⟨.hall 5 14, 29817051264⟩, ⟨.hall 4 18, 4722848898768⟩]
  caps := #[0, 0, 153386836723120, 30713951988720, 1972140970800, 2177929593840, 0, 347794807360, 0, 14194111750, 0, 0, 50484648060, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_24_11_checked :
    (Witness.linear .positive case_47_24_11).check 47 24 11 = true := by
  change case_47_24_11.check 47 24 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_24_12 : Certificate := {
  objectiveScale := 10808226000000
  eta := 1991569817682244800
  rows := #[⟨.count 2, 599195248177125600⟩, ⟨.count 3, 131786005251700800⟩, ⟨.count 4, 23278088778104160⟩, ⟨.count 5, 4699697678676000⟩, ⟨.count 6, 1026370757412000⟩, ⟨.count 7, 258022617652800⟩, ⟨.count 8, 73402986056400⟩, ⟨.count 9, 24022795436640⟩, ⟨.count 10, 10486140865200⟩, ⟨.count 11, 10486140865200⟩, ⟨.path 13, 3028582707150⟩, ⟨.path 14, 115517083500⟩, ⟨.privateRow 8 9, 3753561786975⟩, ⟨.privateRow 8 10, 595803458250⟩, ⟨.privateRow 9 6, 519011012520⟩, ⟨.privateRow 9 7, 2504434092160⟩, ⟨.privateRow 9 8, 1167774778170⟩, ⟨.privateRow 10 4, 727963498080⟩, ⟨.privateRow 10 5, 743562715896⟩, ⟨.privateRow 11 2, 305540235000⟩, ⟨.privateRow 12 0, 444678557400⟩, ⟨.privateRow 13 0, 250542992700⟩, ⟨.privateRow 14 0, 294651892080⟩, ⟨.hall 10 3, 51664076100⟩, ⟨.hall 9 5, 24443218800⟩, ⟨.hall 8 7, 22856878590⟩, ⟨.hall 7 9, 34174756980⟩, ⟨.hall 6 12, 34142908800⟩, ⟨.hall 11 12, 186144512400⟩, ⟨.hall 6 13, 241852070460⟩, ⟨.hall 5 16, 7124555037600⟩, ⟨.hall 4 19, 849834987137136⟩]
  caps := #[0, 0, 0, 0, 83287036678560, 0, 2966728436100, 810342809640, 748620647775, 633534318690, 322085134800, 1061125708500, 0, 632787805650, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_24_12_checked :
    (Witness.linear .positive case_47_24_12).check 47 24 12 = true := by
  change case_47_24_12.check 47 24 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_24_13 : Certificate := {
  objectiveScale := 171171000000
  eta := 38386266327208800
  rows := #[⟨.count 2, 12521723240426400⟩, ⟨.count 3, 2903162999536800⟩, ⟨.count 4, 642214845352080⟩, ⟨.count 5, 150482930598000⟩, ⟨.count 6, 37041952147200⟩, ⟨.count 7, 10062458406000⟩, ⟨.count 8, 2965777214400⟩, ⟨.count 9, 953285533200⟩, ⟨.count 10, 363156393600⟩, ⟨.count 11, 172848475800⟩, ⟨.count 12, 172848475800⟩, ⟨.path 14, 12978652050⟩, ⟨.path 15, 28517088600⟩, ⟨.privateRow 8 10, 13240076850⟩, ⟨.privateRow 9 8, 57373666350⟩, ⟨.privateRow 9 9, 151315164000⟩, ⟨.privateRow 9 10, 17064987940⟩, ⟨.privateRow 10 6, 34298103840⟩, ⟨.privateRow 10 7, 74333574315⟩, ⟨.privateRow 11 4, 19205386200⟩, ⟨.privateRow 11 5, 6595789200⟩, ⟨.privateRow 13 0, 12367104750⟩, ⟨.privateRow 14 0, 3920438340⟩, ⟨.privateRow 15 0, 2824549728⟩, ⟨.hall 15 1, 5148918775⟩, ⟨.hall 11 3, 2457752220⟩, ⟨.hall 11 4, 44767800⟩, ⟨.hall 10 5, 1253401500⟩, ⟨.hall 9 7, 1188829278⟩, ⟨.hall 8 9, 1909957140⟩, ⟨.hall 7 11, 4798493700⟩, ⟨.hall 12 11, 14404039650⟩, ⟨.hall 11 12, 10341361800⟩, ⟨.hall 6 14, 49198444295⟩, ⟨.hall 5 16, 272101830000⟩, ⟨.hall 4 19, 32110742267604⟩]
  caps := #[0, 0, 0, 0, 999436658220, 774733639680, 51291390150, 5884478600, 25019442630, 18620171570, 0, 2830654200, 1780836750, 3166663500, 0, 15100477392, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_24_13_checked :
    (Witness.linear .positive case_47_24_13).check 47 24 13 = true := by
  change case_47_24_13.check 47 24 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_24_14 : Certificate := {
  objectiveScale := 308626500000
  eta := 40644281993515200
  rows := #[⟨.count 2, 10879530028567200⟩, ⟨.count 3, 2903162999536800⟩, ⟨.count 4, 785906751389760⟩, ⟨.count 5, 220708298210400⟩, ⟨.count 6, 64308944700000⟩, ⟨.count 7, 19913075582400⟩, ⟨.count 8, 6778919347200⟩, ⟨.count 9, 2542094755200⟩, ⟨.count 10, 1089469180800⟩, ⟨.count 11, 576161586000⟩, ⟨.count 12, 422518496400⟩, ⟨.count 13, 408550942800⟩, ⟨.path 13, 49161262150⟩, ⟨.privateRow 3 21, 39099838377600⟩, ⟨.privateRow 9 9, 247148101200⟩, ⟨.privateRow 10 7, 161150649660⟩, ⟨.privateRow 10 8, 3890961360⟩, ⟨.privateRow 11 5, 78373495200⟩, ⟨.privateRow 11 6, 177649822350⟩, ⟨.privateRow 12 3, 34569695160⟩, ⟨.privateRow 12 4, 11025314300⟩, ⟨.privateRow 13 1, 17459442000⟩, ⟨.privateRow 14 0, 35902961640⟩, ⟨.privateRow 15 0, 31070047008⟩, ⟨.hall 12 2, 6809182380⟩, ⟨.hall 12 3, 3006903900⟩, ⟨.hall 11 4, 6016792320⟩, ⟨.hall 10 6, 4398872400⟩, ⟨.hall 9 7, 6262648938⟩, ⟨.hall 8 8, 513348745⟩, ⟨.hall 8 9, 8485024275⟩, ⟨.hall 13 10, 8253554400⟩, ⟨.hall 7 11, 10649689050⟩, ⟨.hall 7 12, 22320698400⟩, ⟨.hall 6 14, 207932254530⟩, ⟨.hall 5 16, 1297593897600⟩, ⟨.hall 4 18, 11992332007656⟩, ⟨.hall 3 20, 177345695498400⟩, ⟨.assumptionRow 14, 364873238730⟩]
  caps := #[0, 840995332437260, 15834181342980, 0, 6820608530840, 0, 243471408180, 313390517440, 178611232800, 70613743200, 26738350210, 0, 0, 5997641650, 31202139150, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_24_14_checked :
    (Witness.linear .conditional case_47_24_14).check 47 24 14 = true := by
  change case_47_24_14.check 47 24 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_24_15 : Certificate := {
  objectiveScale := 888844320000
  eta := 49676344658740800
  rows := #[⟨.count 2, 13958642300803200⟩, ⟨.count 3, 4105483029648000⟩, ⟨.count 4, 1255104811920960⟩, ⟨.count 5, 404374644273600⟩, ⟨.count 6, 135820491206400⟩, ⟨.count 7, 47452435430400⟩, ⟨.count 8, 17370980827200⟩, ⟨.count 9, 6482341625760⟩, ⟨.count 10, 2451305656800⟩, ⟨.count 11, 1229144716800⟩, ⟨.count 12, 691393903200⟩, ⟨.count 13, 544734590400⟩, ⟨.count 14, 508418951040⟩, ⟨.count 16, 847364918400⟩, ⟨.path 12, 116451706800⟩, ⟨.privateRow 3 21, 430098222153600⟩, ⟨.privateRow 12 4, 103851347600⟩, ⟨.privateRow 12 5, 10402917525⟩, ⟨.privateRow 15 0, 46605070512⟩, ⟨.hall 13 2, 29345971200⟩, ⟨.hall 12 3, 19593373800⟩, ⟨.hall 13 3, 6740402760⟩, ⟨.hall 12 4, 12648395760⟩, ⟨.hall 11 5, 24875974200⟩, ⟨.hall 10 6, 25047874800⟩, ⟨.hall 9 7, 3992392404⟩, ⟨.hall 9 8, 29701508928⟩, ⟨.hall 10 8, 4686084000⟩, ⟨.hall 8 9, 4147940160⟩, ⟨.hall 14 9, 12710473776⟩, ⟨.hall 8 10, 57863059800⟩, ⟨.hall 7 12, 183714410880⟩, ⟨.hall 6 14, 769185417000⟩, ⟨.hall 5 16, 4818724310400⟩, ⟨.hall 4 18, 47814986563344⟩, ⟨.hall 3 19, 36167350499280⟩, ⟨.hall 3 20, 170363581502400⟩, ⟨.hall 2 21, 223935437980800⟩, ⟨.assumptionRow 15, 554540095200⟩]
  caps := #[0, 0, 151637193708000, 24712794600000, 651663972960, 0, 0, 74493619200, 0, 85240875720, 42527472000, 15660978000, 0, 9805504800, 124694982048, 27267768528, 41479401600, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_24_15_checked :
    (Witness.linear .conditional case_47_24_15).check 47 24 15 = true := by
  change case_47_24_15.check 47 24 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_25_1_checked :
    (Witness.rising).check 47 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_25_2_checked :
    (Witness.rising).check 47 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_25_3_checked :
    (Witness.rising).check 47 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_25_4_checked :
    (Witness.rising).check 47 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_25_5_checked :
    (Witness.rising).check 47 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_25_6_checked :
    (Witness.rising).check 47 25 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_25_7_checked :
    (Witness.rising).check 47 25 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_25_8_checked :
    (Witness.rising).check 47 25 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_25_9_checked :
    (Witness.rising).check 47 25 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_25_10 : Certificate := {
  objectiveScale := 8008000000
  eta := 970640218548000
  rows := #[⟨.count 2, 209210673672000⟩, ⟨.count 3, 29484108894240⟩, ⟨.count 4, 4209820655040⟩, ⟨.count 5, 691393903200⟩, ⟨.count 6, 129542212800⟩, ⟨.count 7, 31632400800⟩, ⟨.count 8, 10544133600⟩, ⟨.count 9, 8134045920⟩, ⟨.count 11, 1274565600⟩, ⟨.path 10, 2564452800⟩, ⟨.path 11, 1120038920⟩, ⟨.privateRow 4 21, 115232317200⟩, ⟨.privateRow 6 12, 2698796100⟩, ⟨.privateRow 6 13, 6670778400⟩, ⟨.privateRow 6 14, 7364156800⟩, ⟨.privateRow 7 8, 136936800⟩, ⟨.privateRow 7 9, 1600448850⟩, ⟨.privateRow 7 10, 2364061700⟩, ⟨.privateRow 7 11, 3059681625⟩, ⟨.privateRow 7 12, 3389185800⟩, ⟨.privateRow 7 13, 2604652050⟩, ⟨.privateRow 8 5, 209530860⟩, ⟨.privateRow 8 6, 578462885⟩, ⟨.privateRow 8 7, 663002340⟩, ⟨.privateRow 8 8, 1722208488⟩, ⟨.privateRow 9 2, 127199072⟩, ⟨.privateRow 9 3, 319193160⟩, ⟨.privateRow 9 4, 84971040⟩, ⟨.privateRow 10 0, 76039425⟩, ⟨.hall 5 12, 2490180⟩, ⟨.hall 4 17, 270832848⟩, ⟨.hall 6 18, 7610803200⟩]
  caps := #[0, 0, 243785542000, 13494914160, 0, 1078303200, 579662720, 0, 402207211, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_25_10_checked :
    (Witness.linear .positive case_47_25_10).check 47 25 10 = true := by
  change case_47_25_10.check 47 25 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_25_11 : Certificate := {
  objectiveScale := 221221000000
  eta := 41260104447962400
  rows := #[⟨.count 2, 9794509513588800⟩, ⟨.count 3, 1557151063387920⟩, ⟨.count 4, 257441567423040⟩, ⟨.count 5, 46302440184000⟩, ⟨.count 6, 9623644430400⟩, ⟨.count 7, 2224332910800⟩, ⟨.count 8, 635523688800⟩, ⟨.count 9, 245130565680⟩, ⟨.count 10, 230464634400⟩, ⟨.path 11, 37284587340⟩, ⟨.path 12, 45129084000⟩, ⟨.privateRow 4 21, 10649561242320⟩, ⟨.privateRow 6 13, 64849356000⟩, ⟨.privateRow 6 14, 590129139600⟩, ⟨.privateRow 7 10, 44133589500⟩, ⟨.privateRow 7 11, 173066718825⟩, ⟨.privateRow 7 12, 251291254500⟩, ⟨.privateRow 7 13, 353699195850⟩, ⟨.privateRow 8 7, 13962262860⟩, ⟨.privateRow 8 8, 57726735066⟩, ⟨.privateRow 8 9, 88855626860⟩, ⟨.privateRow 8 10, 19860115275⟩, ⟨.privateRow 8 11, 325327602600⟩, ⟨.privateRow 9 4, 2793510720⟩, ⟨.privateRow 9 5, 21436314900⟩, ⟨.privateRow 9 6, 9629146800⟩, ⟨.privateRow 9 7, 90789098400⟩, ⟨.privateRow 10 2, 8829489240⟩, ⟨.privateRow 10 3, 14504767200⟩, ⟨.privateRow 10 4, 1571349780⟩, ⟨.privateRow 11 0, 6052606560⟩, ⟨.privateRow 12 0, 3242467800⟩, ⟨.hall 6 11, 139639500⟩, ⟨.hall 5 13, 178240920⟩, ⟨.hall 5 14, 840639800⟩, ⟨.hall 7 17, 229494665400⟩, ⟨.hall 4 18, 117902955456⟩]
  caps := #[0, 0, 0, 3867111207960, 1869246659280, 661463431200, 140651047680, 28338410100, 54426741187, 28643633200, 0, 9056787740, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_25_11_checked :
    (Witness.linear .positive case_47_25_11).check 47 25 11 = true := by
  change case_47_25_11.check 47 25 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_25_12 : Certificate := {
  objectiveScale := 468468000000
  eta := 118237911253862400
  rows := #[⟨.count 2, 31201671025324800⟩, ⟨.count 3, 5700756435454080⟩, ⟨.count 4, 1037174660121600⟩, ⟨.count 5, 207846509270400⟩, ⟨.count 6, 46484018380800⟩, ⟨.count 7, 11439426398400⟩, ⟨.count 8, 3219986689920⟩, ⟨.count 9, 1089469180800⟩, ⟨.count 10, 502831929600⟩, ⟨.count 11, 460929268800⟩, ⟨.path 12, 238918680⟩, ⟨.path 13, 136086350400⟩, ⟨.privateRow 4 21, 42598244969280⟩, ⟨.privateRow 6 14, 60526065600⟩, ⟨.privateRow 7 12, 830071756800⟩, ⟨.privateRow 7 13, 1308876168600⟩, ⟨.privateRow 7 14, 962364443040⟩, ⟨.privateRow 8 9, 167119192240⟩, ⟨.privateRow 8 10, 410442382350⟩, ⟨.privateRow 8 11, 708154967520⟩, ⟨.privateRow 8 12, 942693471720⟩, ⟨.privateRow 9 6, 20909004480⟩, ⟨.privateRow 9 7, 130736301696⟩, ⟨.privateRow 9 8, 216548812480⟩, ⟨.privateRow 9 9, 180065045160⟩, ⟨.privateRow 9 10, 677891934720⟩, ⟨.privateRow 10 4, 34918884000⟩, ⟨.privateRow 10 6, 263148709824⟩, ⟨.privateRow 10 7, 17692234560⟩, ⟨.privateRow 11 2, 36530524800⟩, ⟨.privateRow 11 3, 29681051400⟩, ⟨.privateRow 12 0, 16960600800⟩, ⟨.privateRow 13 0, 10314501120⟩, ⟨.hall 13 1, 14122748640⟩, ⟨.hall 14 1, 25035781680⟩, ⟨.hall 15 2, 12105213120⟩, ⟨.hall 7 11, 814488675⟩, ⟨.hall 6 13, 3970824000⟩, ⟨.hall 5 16, 84948864000⟩, ⟨.hall 8 16, 558263946240⟩, ⟨.hall 4 19, 4480312307328⟩]
  caps := #[0, 0, 0, 3807089526240, 0, 667997890560, 248156868960, 197774418270, 0, 58478358848, 0, 7538731200, 0, 41966527680, 28245497280, 57774880800, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_25_12_checked :
    (Witness.linear .positive case_47_25_12).check 47 25 12 = true := by
  change case_47_25_12.check 47 25 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_25_13 : Certificate := {
  objectiveScale := 104104000000
  eta := 34486057449043200
  rows := #[⟨.count 2, 9618560240889600⟩, ⟨.count 3, 2005821708770880⟩, ⟨.count 4, 461789670101760⟩, ⟨.count 5, 105638159827200⟩, ⟨.count 6, 26631468864000⟩, ⟨.count 7, 6672998732400⟩, ⟨.count 8, 1977184809600⟩, ⟨.count 9, 617365869120⟩, ⟨.count 10, 223480857600⟩, ⟨.count 11, 102428726400⟩, ⟨.count 12, 111740428800⟩, ⟨.path 14, 16016000000⟩, ⟨.path 15, 8409164400⟩, ⟨.privateRow 11 8, 22946695200⟩, ⟨.privateRow 11 14, 183906122400⟩, ⟨.privateRow 13 1, 3957473520⟩, ⟨.privateRow 14 0, 1345023680⟩, ⟨.privateRow 15 0, 641943120⟩, ⟨.privateRow 16 0, 3026303280⟩, ⟨.hall 14 1, 641943120⟩, ⟨.hall 11 3, 780238800⟩, ⟨.hall 10 5, 360002880⟩, ⟨.hall 12 5, 24418800⟩, ⟨.hall 11 6, 17054400⟩, ⟨.hall 9 7, 367530072⟩, ⟨.hall 8 9, 448198296⟩, ⟨.hall 9 11, 129698712⟩, ⟨.hall 6 14, 14141487360⟩, ⟨.hall 7 14, 9285361085⟩, ⟨.hall 5 16, 62260438240⟩, ⟨.hall 4 19, 3004513896384⟩]
  caps := #[0, 329827741443200, 2078837560800, 0, 498057763840, 369881512000, 0, 0, 3468745280, 37090173120, 743142400, 13433774640, 0, 627718000, 13020127120, 27025514880, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_25_13_checked :
    (Witness.linear .positive case_47_25_13).check 47 25 13 = true := by
  change case_47_25_13.check 47 25 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_25_14 : Certificate := {
  objectiveScale := 39939900000
  eta := 11495352483014400
  rows := #[⟨.count 2, 2893388039942400⟩, ⟨.count 3, 715527042310080⟩, ⟨.count 4, 177801370306560⟩, ⟨.count 5, 49732250568000⟩, ⟨.count 6, 14284151481600⟩, ⟨.count 7, 4342745206800⟩, ⟨.count 8, 1384029366720⟩, ⟨.count 9, 490261131360⟩, ⟨.count 10, 195545750400⟩, ⟨.count 11, 89625135600⟩, ⟨.count 12, 97772875200⟩, ⟨.count 13, 18157819680⟩, ⟨.path 13, 7987980000⟩, ⟨.privateRow 3 22, 19549919188800⟩, ⟨.privateRow 7 13, 214363149000⟩, ⟨.privateRow 8 11, 104407463160⟩, ⟨.privateRow 8 12, 380137317560⟩, ⟨.privateRow 8 13, 21890260392⟩, ⟨.privateRow 9 9, 47916468600⟩, ⟨.privateRow 9 10, 168031886880⟩, ⟨.privateRow 9 11, 323478195040⟩, ⟨.privateRow 9 12, 201753552000⟩, ⟨.privateRow 10 7, 21572110560⟩, ⟨.privateRow 10 8, 75424789440⟩, ⟨.privateRow 10 9, 148056068160⟩, ⟨.privateRow 10 10, 213470777520⟩, ⟨.privateRow 10 11, 125707982400⟩, ⟨.privateRow 11 5, 10010080080⟩, ⟨.privateRow 11 6, 35565530000⟩, ⟨.privateRow 11 7, 53251298100⟩, ⟨.privateRow 11 8, 139841816400⟩, ⟨.privateRow 12 3, 5079110400⟩, ⟨.privateRow 12 4, 18274215960⟩, ⟨.privateRow 12 5, 36082846800⟩, ⟨.privateRow 12 6, 3928374450⟩, ⟨.privateRow 13 0, 3223281600⟩, ⟨.privateRow 13 2, 11047065120⟩, ⟨.privateRow 13 3, 419026608⟩, ⟨.privateRow 14 0, 4203199000⟩, ⟨.privateRow 15 0, 3530687160⟩, ⟨.hall 8 11, 806405600⟩, ⟨.hall 7 12, 2528100575⟩, ⟨.hall 8 12, 1014245232⟩, ⟨.hall 6 15, 37891253400⟩, ⟨.hall 9 15, 885193709400⟩, ⟨.hall 5 16, 49818969200⟩, ⟨.hall 4 19, 2975115521664⟩, ⟨.hall 3 21, 51451832774160⟩, ⟨.assumptionRow 14, 54669735120⟩]
  caps := #[0, 113979272447040, 0, 1456660645440, 31730331360, 0, 92806633920, 0, 19065710664, 0, 0, 7451426840, 0, 2597234640, 3933889960, 1102341240, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_25_14_checked :
    (Witness.linear .conditional case_47_25_14).check 47 25 14 = true := by
  change case_47_25_14.check 47 25 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_25_15 : Certificate := {
  objectiveScale := 2034900000
  eta := 331596706240800
  rows := #[⟨.count 2, 87222716380800⟩, ⟨.count 3, 23459903026560⟩, ⟨.count 4, 6791024560320⟩, ⟨.count 5, 2018311495200⟩, ⟨.count 6, 619228209600⟩, ⟨.count 7, 197582685300⟩, ⟨.count 8, 65181916800⟩, ⟨.count 9, 23744841120⟩, ⟨.count 10, 9669844800⟩, ⟨.count 11, 4432012200⟩, ⟨.count 12, 2148854400⟩, ⟨.count 13, 1396755360⟩, ⟨.count 14, 2172730560⟩, ⟨.path 12, 295925630⟩, ⟨.privateRow 3 22, 2782103884560⟩, ⟨.privateRow 7 13, 2812910100⟩, ⟨.privateRow 8 11, 717777060⟩, ⟨.privateRow 8 12, 15548603070⟩, ⟨.privateRow 8 13, 26588790228⟩, ⟨.privateRow 9 9, 38798760⟩, ⟨.privateRow 9 10, 5653533600⟩, ⟨.privateRow 9 11, 16515338840⟩, ⟨.privateRow 9 12, 23387892528⟩, ⟨.privateRow 10 8, 1913823450⟩, ⟨.privateRow 10 9, 6884008560⟩, ⟨.privateRow 10 10, 13278129480⟩, ⟨.privateRow 10 11, 16352781984⟩, ⟨.privateRow 11 6, 661568600⟩, ⟨.privateRow 11 7, 2820371400⟩, ⟨.privateRow 11 8, 6158770200⟩, ⟨.privateRow 11 9, 9446005800⟩, ⟨.privateRow 11 10, 8944606440⟩, ⟨.privateRow 12 4, 214885440⟩, ⟨.privateRow 12 5, 1223653200⟩, ⟨.privateRow 12 6, 2848351275⟩, ⟨.privateRow 12 7, 5001202800⟩, ⟨.privateRow 13 2, 29302560⟩, ⟨.privateRow 13 3, 590934960⟩, ⟨.privateRow 13 4, 1468383840⟩, ⟨.privateRow 13 5, 517068090⟩, ⟨.privateRow 14 1, 268064160⟩, ⟨.privateRow 14 2, 341429088⟩, ⟨.privateRow 15 0, 111105540⟩, ⟨.hall 9 10, 50116680⟩, ⟨.hall 8 11, 111524490⟩, ⟨.hall 9 11, 5819814⟩, ⟨.hall 7 12, 18506950⟩, ⟨.hall 7 13, 407767360⟩, ⟨.hall 10 14, 8989374240⟩, ⟨.hall 6 15, 2556754200⟩, ⟨.hall 5 16, 3169246080⟩, ⟨.hall 4 18, 20293210080⟩, ⟨.hall 3 21, 3701496937320⟩, ⟨.assumptionRow 15, 1720334385⟩]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 642868226, 298356940, 636587886, 0, 0, 1027229490, 0, 0, 2034900000, 0, 0, 0, 0, 0, 0] }

theorem case_47_25_15_checked :
    (Witness.linear .conditional case_47_25_15).check 47 25 15 = true := by
  change case_47_25_15.check 47 25 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_25_16 : Certificate := {
  objectiveScale := 216216000000
  eta := 35717702357937600
  rows := #[⟨.count 2, 9383961210624000⟩, ⟨.count 3, 2604049235948160⟩, ⟨.count 4, 729726457299840⟩, ⟨.count 5, 209904395500800⟩, ⟨.count 6, 61010274124800⟩, ⟨.count 7, 17953544208600⟩, ⟨.count 8, 5762081445120⟩, ⟨.count 9, 1906571066400⟩, ⟨.count 10, 628539912000⟩, ⟨.count 11, 192053862000⟩, ⟨.count 12, 83805321600⟩, ⟨.count 13, 54473459040⟩, ⟨.count 14, 84736491840⟩, ⟨.path 11, 36634197600⟩, ⟨.path 12, 14839504680⟩, ⟨.privateRow 3 22, 387088399938240⟩, ⟨.privateRow 7 13, 185361075900⟩, ⟨.privateRow 8 12, 1468765858560⟩, ⟨.privateRow 8 13, 3188210505480⟩, ⟨.privateRow 9 10, 413306562240⟩, ⟨.privateRow 9 11, 1701791211120⟩, ⟨.privateRow 9 12, 3062618919360⟩, ⟨.privateRow 10 8, 110518267860⟩, ⟨.privateRow 10 9, 592623345600⟩, ⟨.privateRow 10 10, 1493131479840⟩, ⟨.privateRow 10 11, 2303808290784⟩, ⟨.privateRow 11 6, 21339318000⟩, ⟨.privateRow 11 7, 202093041150⟩, ⟨.privateRow 11 8, 605593216800⟩, ⟨.privateRow 11 9, 1187242056000⟩, ⟨.privateRow 11 10, 1617442706880⟩, ⟨.privateRow 12 5, 59362102800⟩, ⟨.privateRow 12 6, 247051104300⟩, ⟨.privateRow 12 7, 374130900000⟩, ⟨.privateRow 12 8, 1275121247400⟩, ⟨.privateRow 12 9, 313571578320⟩, ⟨.privateRow 13 3, 5866372512⟩, ⟨.privateRow 13 4, 96376119840⟩, ⟨.privateRow 13 5, 268700812380⟩, ⟨.privateRow 13 6, 375328118880⟩, ⟨.privateRow 14 2, 22394644272⟩, ⟨.privateRow 14 3, 130467296960⟩, ⟨.privateRow 14 4, 72631278720⟩, ⟨.privateRow 15 1, 55078719696⟩, ⟨.privateRow 15 2, 1176895720⟩, ⟨.privateRow 16 0, 11348637300⟩, ⟨.hall 9 11, 24039157428⟩, ⟨.hall 10 11, 20429465760⟩, ⟨.hall 8 12, 30849122304⟩, ⟨.hall 9 12, 471404934⟩, ⟨.hall 10 12, 17068043520⟩, ⟨.hall 8 13, 38362844520⟩, ⟨.hall 7 14, 112229122005⟩, ⟨.hall 6 15, 336078943200⟩, ⟨.hall 7 15, 567635843775⟩, ⟨.hall 5 16, 406639593360⟩, ⟨.hall 4 18, 2599435238400⟩, ⟨.hall 3 20, 23117144703120⟩, ⟨.assumptionRow 16, 77821494660⟩]
  caps := #[0, 366148709166240, 34437158595840, 0, 1692657351840, 0, 193683409920, 38452574160, 78471513120, 0, 0, 22725588600, 34259356560, 50116799304, 0, 77821494660, 6354096840, 216216000000, 0, 0, 0, 0, 0] }

theorem case_47_25_16_checked :
    (Witness.linear .conditional case_47_25_16).check 47 25 16 = true := by
  change case_47_25_16.check 47 25 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_26_1_checked :
    (Witness.rising).check 47 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_26_2_checked :
    (Witness.rising).check 47 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_26_3_checked :
    (Witness.rising).check 47 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_26_4_checked :
    (Witness.rising).check 47 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_26_5_checked :
    (Witness.rising).check 47 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_26_6_checked :
    (Witness.rising).check 47 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_26_7_checked :
    (Witness.rising).check 47 26 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_26_8_checked :
    (Witness.rising).check 47 26 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_26_9_checked :
    (Witness.rising).check 47 26 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_26_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_26_10_checked :
    (Witness.linear .positive case_47_26_10).check 47 26 10 = true := by
  change case_47_26_10.check 47 26 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_26_11 : Certificate := {
  objectiveScale := 820934400000
  eta := 202341663604080000
  rows := #[⟨.count 2, 42356854914454080⟩, ⟨.count 3, 6261942010484160⟩, ⟨.count 4, 1031824155922560⟩, ⟨.count 5, 180972936144000⟩, ⟨.count 6, 37586686737600⟩, ⟨.count 7, 8770226905440⟩, ⟨.count 8, 2505779115840⟩, ⟨.count 9, 963761198400⟩, ⟨.count 10, 803134332000⟩, ⟨.path 11, 150949312800⟩, ⟨.path 12, 160424264000⟩, ⟨.privateRow 5 17, 5345662113792⟩, ⟨.privateRow 5 18, 12111265726560⟩, ⟨.privateRow 6 14, 2361597381000⟩, ⟨.privateRow 6 15, 3509250845100⟩, ⟨.privateRow 6 16, 4663533354480⟩, ⟨.privateRow 6 17, 6351454008900⟩, ⟨.privateRow 7 10, 118328458248⟩, ⟨.privateRow 7 11, 649646437440⟩, ⟨.privateRow 7 12, 1148482094760⟩, ⟨.privateRow 7 13, 1620801570960⟩, ⟨.privateRow 7 14, 1786527702960⟩, ⟨.privateRow 7 15, 2129912248464⟩, ⟨.privateRow 7 16, 1270290801780⟩, ⟨.privateRow 8 7, 43503109650⟩, ⟨.privateRow 8 8, 227798101440⟩, ⟨.privateRow 8 9, 386307613692⟩, ⟨.privateRow 8 10, 154677723200⟩, ⟨.privateRow 8 11, 1396449819765⟩, ⟨.privateRow 9 4, 7648898400⟩, ⟨.privateRow 9 5, 62603291520⟩, ⟨.privateRow 9 6, 194536982640⟩, ⟨.privateRow 9 7, 179123293440⟩, ⟨.privateRow 9 8, 38550447936⟩, ⟨.privateRow 10 2, 33196219056⟩, ⟨.privateRow 10 3, 56219403240⟩, ⟨.privateRow 11 0, 20078358300⟩, ⟨.privateRow 12 0, 10708457760⟩, ⟨.hall 5 15, 1641868800⟩, ⟨.hall 4 19, 354473130336⟩, ⟨.hall 6 19, 208814926320⟩, ⟨.hall 4 20, 512244408000⟩, ⟨.hall 3 22, 105569563619520⟩]
  caps := #[0, 0, 41458049181120, 18008906344000, 0, 5791133956608, 0, 418624209432, 58044520469, 8122514400, 37332702264, 9640059000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_26_11_checked :
    (Witness.linear .positive case_47_26_11).check 47 26 11 = true := by
  change case_47_26_11.check 47 26 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_26_12 : Certificate := {
  objectiveScale := 448948500000
  eta := 145685997794937600
  rows := #[⟨.count 2, 32104877291847360⟩, ⟨.count 3, 5495173601037120⟩, ⟨.count 4, 1012891602602880⟩, ⟨.count 5, 206030727302400⟩, ⟨.count 6, 45939283790400⟩, ⟨.count 7, 11206401045840⟩, ⟨.count 8, 3062618919360⟩, ⟨.count 9, 963761198400⟩, ⟨.count 10, 481880599200⟩, ⟨.count 11, 481880599200⟩, ⟨.path 12, 5578933360⟩, ⟨.path 13, 126064738800⟩, ⟨.privateRow 5 17, 111367960704⟩, ⟨.privateRow 5 18, 15173884645920⟩, ⟨.privateRow 6 15, 3741267429900⟩, ⟨.privateRow 6 16, 5498793059760⟩, ⟨.privateRow 6 17, 10658261864250⟩, ⟨.privateRow 7 12, 826559083350⟩, ⟨.privateRow 7 13, 1640688706800⟩, ⟨.privateRow 7 14, 2749396529880⟩, ⟨.privateRow 7 15, 3702984693408⟩, ⟨.privateRow 7 16, 4332909721140⟩, ⟨.privateRow 8 9, 163571692284⟩, ⟨.privateRow 8 10, 491101771160⟩, ⟨.privateRow 8 11, 822208772385⟩, ⟨.privateRow 8 12, 174012438600⟩, ⟨.privateRow 8 13, 3381641723460⟩, ⟨.privateRow 8 14, 396748360008⟩, ⟨.privateRow 9 6, 17847429600⟩, ⟨.privateRow 9 7, 147971416320⟩, ⟨.privateRow 9 8, 261286369344⟩, ⟨.privateRow 9 9, 387884136640⟩, ⟨.privateRow 9 10, 481880599200⟩, ⟨.privateRow 9 11, 119322815040⟩, ⟨.privateRow 10 4, 35832147120⟩, ⟨.privateRow 10 5, 91021890960⟩, ⟨.privateRow 10 6, 147484668240⟩, ⟨.privateRow 10 7, 46581791256⟩, ⟨.privateRow 11 2, 41721264000⟩, ⟨.privateRow 11 3, 21342031200⟩, ⟨.privateRow 12 0, 14991840864⟩, ⟨.privateRow 13 0, 9178678080⟩, ⟨.privateRow 15 8, 87006219300⟩, ⟨.hall 13 1, 13385572200⟩, ⟨.hall 5 19, 2883634696800⟩, ⟨.hall 6 19, 12111265726560⟩, ⟨.hall 4 20, 6679667080320⟩, ⟨.hall 3 22, 150019906196160⟩]
  caps := #[0, 1117855905566400, 11600829240000, 6790352048480, 10634429725920, 0, 0, 1209635037468, 22196013840, 95580115232, 0, 0, 0, 0, 187398010800, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_26_12_checked :
    (Witness.linear .positive case_47_26_12).check 47 26 12 = true := by
  change case_47_26_12.check 47 26 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_26_13 : Certificate := {
  objectiveScale := 5855850000
  eta := 2580589332921600
  rows := #[⟨.count 2, 580632599907360⟩, ⟨.count 3, 125016588496800⟩, ⟨.count 4, 29839350340800⟩, ⟨.count 5, 6839445412800⟩, ⟨.count 6, 1702295595000⟩, ⟨.count 7, 434274520680⟩, ⟨.count 8, 121052131200⟩, ⟨.count 9, 37712394720⟩, ⟨.count 10, 13967553600⟩, ⟨.count 11, 6983776800⟩, ⟨.count 12, 4190266080⟩, ⟨.path 14, 1330809480⟩, ⟨.privateRow 11 11, 2031644160⟩, ⟨.privateRow 11 13, 3809332800⟩, ⟨.privateRow 13 3, 465585120⟩, ⟨.privateRow 13 11, 155195040⟩, ⟨.privateRow 14 0, 116396280⟩, ⟨.privateRow 14 2, 412677720⟩, ⟨.privateRow 15 0, 252191940⟩, ⟨.privateRow 15 1, 687796200⟩, ⟨.privateRow 15 2, 151315164⟩, ⟨.hall 11 3, 19953648⟩, ⟨.hall 9 7, 926478⟩, ⟨.hall 11 7, 746130⟩, ⟨.hall 12 8, 1860480⟩, ⟨.hall 15 8, 320971560⟩, ⟨.hall 8 9, 40776736⟩, ⟨.hall 7 12, 68528460⟩, ⟨.hall 10 14, 160044885⟩, ⟨.hall 4 19, 45344765856⟩]
  caps := #[0, 0, 638549992080, 151315164000, 0, 11149538400, 10456205760, 4892607720, 0, 0, 1401800400, 0, 6706515816, 0, 8208771480, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_26_13_checked :
    (Witness.linear .positive case_47_26_13).check 47 26 13 = true := by
  change case_47_26_13.check 47 26 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_26_14 : Certificate := {
  objectiveScale := 96696600000
  eta := 41817277144843200
  rows := #[⟨.count 2, 9307716525787680⟩, ⟨.count 3, 2364202595795040⟩, ⟨.count 4, 601108567899840⟩, ⟨.count 5, 153130945968000⟩, ⟨.count 6, 43329097211400⟩, ⟨.count 7, 12911722944120⟩, ⟨.count 8, 4037088575520⟩, ⟨.count 9, 1445641797600⟩, ⟨.count 10, 562194032400⟩, ⟨.count 11, 240940299600⟩, ⟨.count 12, 192752239680⟩, ⟨.count 13, 139209950880⟩, ⟨.path 13, 21778491735⟩, ⟨.privateRow 3 23, 255589469815680⟩, ⟨.privateRow 5 18, 12459290603760⟩, ⟨.privateRow 6 16, 5846817936960⟩, ⟨.privateRow 6 17, 14203765300725⟩, ⟨.privateRow 7 13, 273448117800⟩, ⟨.privateRow 7 14, 2215758384840⟩, ⟨.privateRow 7 15, 5791133956608⟩, ⟨.privateRow 7 16, 9066048051060⟩, ⟨.privateRow 8 11, 213165237285⟩, ⟨.privateRow 8 12, 932209492500⟩, ⟨.privateRow 8 13, 2296964189520⟩, ⟨.privateRow 8 14, 3796951410252⟩, ⟨.privateRow 8 15, 4546074958425⟩, ⟨.privateRow 9 9, 117793035360⟩, ⟨.privateRow 9 10, 418968409860⟩, ⟨.privateRow 9 11, 977529215520⟩, ⟨.privateRow 9 12, 1615192378800⟩, ⟨.privateRow 9 13, 2086007571648⟩, ⟨.privateRow 9 14, 1903428366840⟩, ⟨.privateRow 10 7, 59431940568⟩, ⟨.privateRow 10 8, 197214097080⟩, ⟨.privateRow 10 9, 448751308005⟩, ⟨.privateRow 10 10, 737736250680⟩, ⟨.privateRow 10 11, 872739307440⟩, ⟨.privateRow 11 5, 29204884800⟩, ⟨.privateRow 11 6, 97836364080⟩, ⟨.privateRow 11 7, 222281623200⟩, ⟨.privateRow 11 8, 321253732800⟩, ⟨.privateRow 12 3, 16062686640⟩, ⟨.privateRow 12 4, 53298914760⟩, ⟨.privateRow 12 5, 101998060164⟩, ⟨.privateRow 13 1, 9884730240⟩, ⟨.privateRow 13 2, 26771144400⟩, ⟨.privateRow 14 0, 9369900540⟩, ⟨.privateRow 15 0, 8700621930⟩, ⟨.hall 7 14, 6834193366⟩, ⟨.hall 6 16, 44823018240⟩, ⟨.hall 6 17, 129440831520⟩, ⟨.hall 8 17, 812058046800⟩, ⟨.hall 5 19, 7391385487200⟩, ⟨.hall 4 20, 12642191989440⟩, ⟨.hall 3 21, 14648408349120⟩, ⟨.assumptionRow 14, 142832965275⟩]
  caps := #[0, 0, 85710942096780, 0, 827567851110, 0, 7681508835, 419121387828, 223560190854, 0, 0, 172144279125, 0, 21374172435, 68168685585, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_26_14_checked :
    (Witness.linear .conditional case_47_26_14).check 47 26 14 = true := by
  change case_47_26_14.check 47 26 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_26_15 : Certificate := {
  objectiveScale := 26919200000
  eta := 5603307607497600
  rows := #[⟨.count 2, 1494215361999360⟩, ⟨.count 3, 403044933170880⟩, ⟨.count 4, 111410794535040⟩, ⟨.count 5, 31804119547200⟩, ⟨.count 6, 9517141834200⟩, ⟨.count 7, 2979628371720⟩, ⟨.count 8, 995886571680⟩, ⟨.count 9, 355850288640⟩, ⟨.count 10, 148270953600⟩, ⟨.count 11, 55601607600⟩, ⟨.count 12, 22240643040⟩, ⟨.count 13, 32125373280⟩, ⟨.path 11, 2001027600⟩, ⟨.path 12, 2287565280⟩, ⟨.privateRow 2 24, 93388460124960⟩, ⟨.privateRow 5 18, 5140059724800⟩, ⟨.privateRow 6 16, 1807052247000⟩, ⟨.privateRow 6 17, 5114961776925⟩, ⟨.privateRow 7 13, 5736673800⟩, ⟨.privateRow 7 14, 622429107300⟩, ⟨.privateRow 7 15, 1898609560848⟩, ⟨.privateRow 7 16, 3523751881650⟩, ⟨.privateRow 8 12, 221435608680⟩, ⟨.privateRow 8 13, 715458834090⟩, ⟨.privateRow 8 14, 1400666275008⟩, ⟨.privateRow 8 15, 2063051315325⟩, ⟨.privateRow 9 10, 75988863720⟩, ⟨.privateRow 9 11, 278890603200⟩, ⟨.privateRow 9 12, 577432991520⟩, ⟨.privateRow 9 13, 889131485088⟩, ⟨.privateRow 9 14, 1066933070280⟩, ⟨.privateRow 10 8, 26359280640⟩, ⟨.privateRow 10 9, 110044848375⟩, ⟨.privateRow 10 10, 249942464640⟩, ⟨.privateRow 10 11, 258547475340⟩, ⟨.privateRow 10 12, 814748890032⟩, ⟨.privateRow 11 6, 9098444880⟩, ⟨.privateRow 11 7, 45305013600⟩, ⟨.privateRow 11 8, 72450579600⟩, ⟨.privateRow 11 9, 279211536000⟩, ⟨.privateRow 11 10, 78909352200⟩, ⟨.privateRow 12 4, 2695835520⟩, ⟨.privateRow 12 5, 19460562660⟩, ⟨.privateRow 12 6, 53336356920⟩, ⟨.privateRow 12 7, 71818743150⟩, ⟨.privateRow 13 2, 205931880⟩, ⟨.privateRow 13 3, 9210771360⟩, ⟨.privateRow 13 4, 27430126416⟩, ⟨.privateRow 13 5, 2471182560⟩, ⟨.privateRow 14 1, 3681032355⟩, ⟨.privateRow 14 2, 5110854840⟩, ⟨.privateRow 15 0, 1338557220⟩, ⟨.hall 7 16, 13846953120⟩, ⟨.hall 7 17, 562522800840⟩, ⟨.hall 8 17, 2955534341760⟩, ⟨.hall 6 18, 1613031900480⟩, ⟨.hall 5 19, 3116161208160⟩, ⟨.hall 4 20, 5182337272320⟩, ⟨.hall 3 21, 7110500604480⟩, ⟨.hall 2 23, 149162123810700⟩, ⟨.assumptionRow 15, 25472115900⟩]
  caps := #[0, 57560418567520, 0, 0, 0, 0, 5356202280, 9607866268, 0, 3117385040, 24769770443, 5046828820, 51056637170, 0, 25472115900, 21519385580, 26919200000, 0, 0, 0, 0, 0] }

theorem case_47_26_15_checked :
    (Witness.linear .conditional case_47_26_15).check 47 26 15 = true := by
  change case_47_26_15.check 47 26 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_26_16 : Certificate := {
  objectiveScale := 860562434239200000
  eta := 169832169083301257332800
  rows := #[⟨.count 2, 43922112693957221724000⟩, ⟨.count 3, 11558450708936110980000⟩, ⟨.count 4, 3102801879198849347520⟩, ⟨.count 5, 858196078781138697600⟩, ⟨.count 6, 247033554367458058200⟩, ⟨.count 7, 74034520880767246800⟩, ⟨.count 8, 22965810558931880640⟩, ⟨.count 9, 7112892743960683680⟩, ⟨.count 10, 2092027277635495200⟩, ⟨.count 11, 1046013638817747600⟩, ⟨.count 12, 418405455527099040⟩, ⟨.count 13, 604363435761365280⟩, ⟨.path 10, 112083499851523200⟩, ⟨.path 11, 109035788664745800⟩, ⟨.privateRow 2 24, 4392211269395722172400⟩, ⟨.privateRow 5 18, 169826125448943643680⟩, ⟨.privateRow 6 16, 53712800353291339260⟩, ⟨.privateRow 6 17, 169221762013182278400⟩, ⟨.privateRow 7 14, 16468903624497203880⟩, ⟨.privateRow 7 15, 58713907784216636952⟩, ⟨.privateRow 7 16, 123101277321643090470⟩, ⟨.privateRow 8 12, 4813323077670873480⟩, ⟨.privateRow 8 13, 20321720527475907540⟩, ⟨.privateRow 8 14, 46626639068989331352⟩, ⟨.privateRow 8 15, 78888314724225711705⟩, ⟨.privateRow 9 10, 1290083487875222040⟩, ⟨.privateRow 9 11, 6960141545911107840⟩, ⟨.privateRow 9 12, 18014679335194542000⟩, ⟨.privateRow 9 13, 32812285612336278048⟩, ⟨.privateRow 9 14, 46036222481745536040⟩, ⟨.privateRow 10 8, 267314596586757720⟩, ⟨.privateRow 10 9, 2314305175884266565⟩, ⟨.privateRow 10 10, 7063082570683648080⟩, ⟨.privateRow 10 11, 14214163114156725720⟩, ⟨.privateRow 10 12, 21771030535926720048⟩, ⟨.privateRow 10 13, 25627334151034816200⟩, ⟨.privateRow 11 5, 2881580272225200⟩, ⟨.privateRow 11 7, 714952083097652400⟩, ⟨.privateRow 11 8, 2777483184891064650⟩, ⟨.privateRow 11 9, 6389286772172475600⟩, ⟨.privateRow 11 10, 10808807601116725200⟩, ⟨.privateRow 11 11, 9870565064480200080⟩, ⟨.privateRow 12 5, 115061500269952236⟩, ⟨.privateRow 12 6, 1073132510935244760⟩, ⟨.privateRow 12 7, 2048443376018089050⟩, ⟨.privateRow 12 8, 7496431078193857800⟩, ⟨.privateRow 13 4, 311479616892395952⟩, ⟨.privateRow 13 5, 1379188353404141280⟩, ⟨.privateRow 13 6, 1847957428578020760⟩, ⟨.privateRow 14 2, 48074364208290420⟩, ⟨.privateRow 14 3, 551481635132245818⟩, ⟨.privateRow 14 4, 428090766997633740⟩, ⟨.privateRow 15 1, 206032989464101800⟩, ⟨.privateRow 15 2, 45327257682102396⟩, ⟨.privateRow 16 0, 34338831577350300⟩, ⟨.hall 8 14, 83248100710266492⟩, ⟨.hall 8 15, 1238105649650019150⟩, ⟨.hall 7 16, 1117666952409047040⟩, ⟨.hall 9 16, 29805235684900996320⟩, ⟨.hall 7 17, 24495715952237149620⟩, ⟨.hall 6 18, 68766221194031661300⟩, ⟨.hall 5 19, 121491440193647787120⟩, ⟨.hall 4 20, 192184956280184456160⟩, ⟨.hall 3 21, 262052463503784713760⟩, ⟨.hall 2 23, 5758676997652169070480⟩, ⟨.assumptionRow 16, 464185960464946720⟩]
  caps := #[0, 1756939120756975978240, 585905034337468472880, 0, 1839441017089276480, 7269098452239143520, 2006625151674037180, 0, 1485763317243996219, 96559507088918720, 512443495705681397, 140987294214509340, 125778645576890306, 0, 1307111548315902714, 464185960464946720, 1752324063734454980, 860562434239200000, 0, 0, 0, 0] }

theorem case_47_26_16_checked :
    (Witness.linear .conditional case_47_26_16).check 47 26 16 = true := by
  change case_47_26_16.check 47 26 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_27_1_checked :
    (Witness.rising).check 47 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_27_2_checked :
    (Witness.rising).check 47 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_27_3_checked :
    (Witness.rising).check 47 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_27_4_checked :
    (Witness.rising).check 47 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_27_5_checked :
    (Witness.rising).check 47 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_27_6_checked :
    (Witness.rising).check 47 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_27_7_checked :
    (Witness.rising).check 47 27 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_27_8_checked :
    (Witness.rising).check 47 27 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_27_9_checked :
    (Witness.rising).check 47 27 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_27_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_27_10_checked :
    (Witness.linear .positive case_47_27_10).check 47 27 10 = true := by
  change case_47_27_10.check 47 27 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_27_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_27_11_checked :
    (Witness.linear .positive case_47_27_11).check 47 27 11 = true := by
  change case_47_27_11.check 47 27 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_27_12 : Certificate := {
  objectiveScale := 380926000000
  eta := 215291530074741120
  rows := #[⟨.count 2, 42342655499464320⟩, ⟨.count 3, 7554088774552320⟩, ⟨.count 4, 1391542668996480⟩, ⟨.count 5, 274069590795000⟩, ⟨.count 6, 57006474885360⟩, ⟨.count 7, 12424488116040⟩, ⟨.count 8, 3148286581440⟩, ⟨.count 9, 1011949258320⟩, ⟨.count 10, 306651290400⟩, ⟨.count 11, 337316419440⟩, ⟨.path 12, 47610988425⟩, ⟨.path 13, 79354504320⟩, ⟨.privateRow 5 18, 3946602107448⟩, ⟨.privateRow 6 17, 23289824782224⟩, ⟨.privateRow 6 18, 2375269786890⟩, ⟨.privateRow 6 19, 8364197882040⟩, ⟨.privateRow 7 16, 22343197116240⟩, ⟨.privateRow 9 15, 1958309212860⟩, ⟨.privateRow 10 12, 388424967840⟩, ⟨.privateRow 11 9, 65163399210⟩, ⟨.privateRow 11 16, 306651290400⟩, ⟨.privateRow 12 5, 6814473120⟩, ⟨.privateRow 13 0, 3747960216⟩, ⟨.hall 11 1, 2342475135⟩, ⟨.hall 13 1, 7457675940⟩, ⟨.hall 8 8, 11360160⟩, ⟨.hall 7 11, 171152982⟩, ⟨.hall 6 13, 656362707⟩, ⟨.hall 9 14, 440936496⟩, ⟨.hall 5 16, 5999584500⟩, ⟨.hall 4 19, 201386727360⟩, ⟨.hall 3 22, 13684943432160⟩]
  caps := #[0, 0, 83816694339560, 0, 4502994843438, 0, 0, 240274788390, 184542604155, 19701199700, 270855381160, 43609580560, 60561007325, 124330026912, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_27_12_checked :
    (Witness.linear .positive case_47_27_12).check 47 27 12 = true := by
  change case_47_27_12.check 47 27 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_27_13 : Certificate := {
  objectiveScale := 11223712500
  eta := 7284299889746880
  rows := #[⟨.count 2, 1718129213760960⟩, ⟨.count 3, 395217050548320⟩, ⟨.count 4, 90764887973760⟩, ⟨.count 5, 22447604579400⟩, ⟨.count 6, 5429188084320⟩, ⟨.count 7, 1392099508800⟩, ⟨.count 8, 385504479360⟩, ⟨.count 9, 112438806480⟩, ⟨.count 10, 29204884800⟩, ⟨.count 11, 16062686640⟩, ⟨.count 12, 21416915520⟩, ⟨.path 13, 2992990000⟩, ⟨.hall 9 9, 157183656⟩, ⟨.hall 8 10, 133668640⟩, ⟨.hall 7 12, 145252107⟩, ⟨.hall 4 19, 37101692160⟩]
  caps := #[0, 0, 0, 661247266680, 456299283440, 22267845600, 27780933180, 0, 0, 0, 5214500200, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_27_13_checked :
    (Witness.linear .positive case_47_27_13).check 47 27 13 = true := by
  change case_47_27_13.check 47 27 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_27_14 : Certificate := {
  objectiveScale := 8296568280000
  eta := 5920517077055380800
  rows := #[⟨.count 2, 1377627242306515200⟩, ⟨.count 3, 311606161950283200⟩, ⟨.count 4, 78464296714003200⟩, ⟨.count 5, 19696467925134000⟩, ⟨.count 6, 5064806037891600⟩, ⟨.count 7, 1447087439397600⟩, ⟨.count 8, 445257673660800⟩, ⟨.count 9, 148419224553600⟩, ⟨.count 10, 50597462916000⟩, ⟨.count 11, 18552403069200⟩, ⟨.count 12, 24736537425600⟩, ⟨.path 12, 2719954487250⟩, ⟨.privateRow 4 21, 8843312129652000⟩, ⟨.privateRow 5 18, 747661843688760⟩, ⟨.privateRow 5 19, 3245897520315450⟩, ⟨.privateRow 5 20, 7168442408127000⟩, ⟨.privateRow 6 16, 529258832001900⟩, ⟨.privateRow 6 17, 1305058487012280⟩, ⟨.privateRow 6 18, 2696540251655250⟩, ⟨.privateRow 6 19, 3858899838393600⟩, ⟨.privateRow 7 13, 4306807855350⟩, ⟨.privateRow 7 14, 265791570501600⟩, ⟨.privateRow 7 15, 557970884370900⟩, ⟨.privateRow 7 16, 1064642901842520⟩, ⟨.privateRow 7 17, 1494462325806450⟩, ⟨.privateRow 7 18, 1638501121857600⟩, ⟨.privateRow 8 11, 15803898910800⟩, ⟨.privateRow 8 12, 108608859634275⟩, ⟨.privateRow 8 13, 245156754843000⟩, ⟨.privateRow 8 14, 450411118957800⟩, ⟨.privateRow 8 15, 304259410334880⟩, ⟨.privateRow 8 16, 1298668214844000⟩, ⟨.privateRow 8 17, 127805443365600⟩, ⟨.privateRow 9 9, 12574406524680⟩, ⟨.privateRow 9 10, 49473074851200⟩, ⟨.privateRow 9 11, 104872611793950⟩, ⟨.privateRow 9 12, 203781951172800⟩, ⟨.privateRow 9 13, 279316735097400⟩, ⟨.privateRow 9 14, 178927620711840⟩, ⟨.privateRow 10 7, 7666282260000⟩, ⟨.privateRow 10 8, 24961415038560⟩, ⟨.privateRow 10 9, 49285676840400⟩, ⟨.privateRow 10 10, 94659420205350⟩, ⟨.privateRow 10 11, 78787477969200⟩, ⟨.privateRow 11 5, 4357003751100⟩, ⟨.privateRow 11 6, 13492656777600⟩, ⟨.privateRow 11 7, 26310680716320⟩, ⟨.privateRow 11 8, 26048323501200⟩, ⟨.privateRow 12 3, 2537080761600⟩, ⟨.privateRow 12 4, 8073730965300⟩, ⟨.privateRow 12 5, 6184134356400⟩, ⟨.privateRow 13 1, 1766895530400⟩, ⟨.privateRow 13 2, 1664959249800⟩, ⟨.privateRow 14 0, 820344353400⟩, ⟨.privateRow 15 0, 1030689059400⟩, ⟨.hall 6 19, 113316900016320⟩, ⟨.hall 6 20, 846048476473200⟩, ⟨.hall 5 21, 10780070571270000⟩, ⟨.hall 4 22, 25586183711088000⟩, ⟨.hall 3 23, 47720388105690300⟩, ⟨.hall 2 24, 55105089692260608⟩, ⟨.assumptionRow 14, 11965495141600⟩]
  caps := #[0, 41599568249439200, 8394447044283300, 1314169778297376, 0, 267034108180840, 39283308013950, 20043126203100, 35725088283885, 15553471293360, 3597688571750, 16247510679400, 0, 8431704080800, 17864054179400, 0, 0, 0, 0, 0, 0] }

theorem case_47_27_14_checked :
    (Witness.linear .conditional case_47_27_14).check 47 27 14 = true := by
  change case_47_27_14.check 47 27 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_27_15 : Certificate := {
  objectiveScale := 368190900000
  eta := 227712195271360800
  rows := #[⟨.count 2, 54247226574340800⟩, ⟨.count 3, 12825894655173600⟩, ⟨.count 4, 3364169089881600⟩, ⟨.count 5, 896699481678000⟩, ⟨.count 6, 244273307077800⟩, ⟨.count 7, 69571511509500⟩, ⟨.count 8, 20930916283200⟩, ⟨.count 9, 6421985677800⟩, ⟨.count 10, 2594741688000⟩, ⟨.count 11, 713553964200⟩, ⟨.path 11, 117347630400⟩, ⟨.privateRow 2 25, 1892345113058400⟩, ⟨.privateRow 4 21, 469994211086400⟩, ⟨.privateRow 5 18, 23499710554320⟩, ⟨.privateRow 5 19, 164266068841875⟩, ⟨.privateRow 5 20, 400422699576900⟩, ⟨.privateRow 6 16, 15546226645950⟩, ⟨.privateRow 6 17, 61635205752120⟩, ⟨.privateRow 6 18, 147903880023900⟩, ⟨.privateRow 6 19, 238260954231300⟩, ⟨.privateRow 7 14, 7446202592400⟩, ⟨.privateRow 7 15, 24258003219450⟩, ⟨.privateRow 7 16, 56894036078880⟩, ⟨.privateRow 7 17, 92817230831325⟩, ⟨.privateRow 7 18, 119412689596200⟩, ⟨.privateRow 8 12, 3151530008550⟩, ⟨.privateRow 8 13, 9853840458000⟩, ⟨.privateRow 8 14, 22992294402000⟩, ⟨.privateRow 8 15, 38079996556140⟩, ⟨.privateRow 8 16, 49829851833300⟩, ⟨.privateRow 8 17, 49631642398800⟩, ⟨.privateRow 9 10, 1259731072600⟩, ⟨.privateRow 9 11, 4093024822425⟩, ⟨.privateRow 9 12, 9808535444400⟩, ⟨.privateRow 9 13, 16702448347200⟩, ⟨.privateRow 9 14, 22548305268720⟩, ⟨.privateRow 9 15, 19087568542350⟩, ⟨.privateRow 10 8, 486514066500⟩, ⟨.privateRow 10 9, 1744243023600⟩, ⟨.privateRow 10 10, 4411060869600⟩, ⟨.privateRow 10 11, 7923229083000⟩, ⟨.privateRow 10 12, 10595195226000⟩, ⟨.privateRow 11 6, 176914206000⟩, ⟨.privateRow 11 7, 758961943740⟩, ⟨.privateRow 11 8, 1009066212000⟩, ⟨.privateRow 11 9, 6243597186750⟩, ⟨.privateRow 12 4, 59462830350⟩, ⟨.privateRow 12 5, 345965558400⟩, ⟨.privateRow 12 6, 1054474191540⟩, ⟨.privateRow 12 7, 960214593800⟩, ⟨.privateRow 13 1, 8494690050⟩, ⟨.privateRow 13 3, 168478019325⟩, ⟨.privateRow 13 4, 443268371700⟩, ⟨.privateRow 14 1, 67957520400⟩, ⟨.privateRow 14 2, 73620647100⟩, ⟨.privateRow 15 0, 39641886900⟩, ⟨.hall 7 19, 54188477297955⟩, ⟨.hall 6 20, 290359832162400⟩, ⟨.hall 5 21, 776530507252500⟩, ⟨.hall 4 22, 1629384965208000⟩, ⟨.hall 3 23, 2864800240602300⟩, ⟨.hall 2 24, 3608071348898016⟩, ⟨.assumptionRow 15, 378802161738⟩]
  caps := #[0, 1798552408653000, 271467641491200, 23440012693020, 17823995148960, 4420311687792, 1391146146390, 872028458730, 0, 543370046912, 0, 1274973697620, 756982762690, 265451963238, 378802161738, 0, 368190900000, 0, 0, 0, 0] }

theorem case_47_27_15_checked :
    (Witness.linear .conditional case_47_27_15).check 47 27 15 = true := by
  change case_47_27_15.check 47 27 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_27_16 : Certificate := {
  objectiveScale := 1338876000000
  eta := 679867989709708800
  rows := #[⟨.count 2, 155057611688179200⟩, ⟨.count 3, 39012892684365600⟩, ⟨.count 4, 9822654134092800⟩, ⟨.count 5, 2521440235314000⟩, ⟨.count 6, 657767017908000⟩, ⟨.count 7, 175404538108800⟩, ⟨.count 8, 47224298721600⟩, ⟨.count 9, 13492656777600⟩, ⟨.count 10, 4599769356000⟩, ⟨.count 11, 3373164194400⟩, ⟨.path 10, 615107001600⟩, ⟨.privateRow 2 25, 14163916452285600⟩, ⟨.privateRow 4 20, 211947150214800⟩, ⟨.privateRow 4 21, 1866109391546400⟩, ⟨.privateRow 5 18, 128629994613120⟩, ⟨.privateRow 5 19, 636755015947050⟩, ⟨.privateRow 5 20, 1606656845593800⟩, ⟨.privateRow 6 16, 55016932670700⟩, ⟨.privateRow 6 17, 224128020916800⟩, ⟨.privateRow 6 18, 575850662437050⟩, ⟨.privateRow 6 19, 1010606239242600⟩, ⟨.privateRow 7 14, 19986571519200⟩, ⟨.privateRow 7 15, 80132727975300⟩, ⟨.privateRow 7 16, 212260372604280⟩, ⟨.privateRow 7 17, 387090669665700⟩, ⟨.privateRow 7 18, 561190114485000⟩, ⟨.privateRow 8 12, 6359819991525⟩, ⟨.privateRow 8 13, 28631738935800⟩, ⟨.privateRow 8 14, 80534295141300⟩, ⟨.privateRow 8 15, 154547139506760⟩, ⟨.privateRow 8 16, 232748329413600⟩, ⟨.privateRow 8 17, 275943570903000⟩, ⟨.privateRow 9 10, 1707404098400⟩, ⟨.privateRow 9 11, 10049218329150⟩, ⟨.privateRow 9 12, 31375781236800⟩, ⟨.privateRow 9 13, 64746012731400⟩, ⟨.privateRow 9 14, 102918987531360⟩, ⟨.privateRow 9 15, 129773122479000⟩, ⟨.privateRow 9 16, 106816866156000⟩, ⟨.privateRow 10 8, 260653596840⟩, ⟨.privateRow 10 9, 3356128011600⟩, ⟨.privateRow 10 10, 12419377261200⟩, ⟨.privateRow 10 11, 28496666343600⟩, ⟨.privateRow 10 12, 48859772270400⟩, ⟨.privateRow 10 13, 66543330016800⟩, ⟨.privateRow 10 14, 5711380283700⟩, ⟨.privateRow 11 7, 858623613120⟩, ⟨.privateRow 11 8, 4889384463600⟩, ⟨.privateRow 11 9, 13071011253300⟩, ⟨.privateRow 11 10, 24926369176800⟩, ⟨.privateRow 11 11, 17453569278600⟩, ⟨.privateRow 12 1, 24986401440⟩, ⟨.privateRow 12 5, 68144731200⟩, ⟨.privateRow 12 6, 1705321898280⟩, ⟨.privateRow 12 7, 6142490354000⟩, ⟨.privateRow 12 8, 12883613242500⟩, ⟨.privateRow 13 4, 408868387200⟩, ⟨.privateRow 13 5, 2698531355520⟩, ⟨.privateRow 13 6, 3560562205200⟩, ⟨.privateRow 14 2, 43503109650⟩, ⟨.privateRow 14 3, 996616693800⟩, ⟨.privateRow 14 4, 783055973700⟩, ⟨.privateRow 15 1, 304521767550⟩, ⟨.hall 7 18, 2654147616120⟩, ⟨.hall 7 19, 463360321504080⟩, ⟨.hall 6 20, 1642677420384000⟩, ⟨.hall 5 21, 3755583907803000⟩, ⟨.hall 4 22, 7285643568403200⟩, ⟨.hall 3 23, 12465903076426800⟩, ⟨.hall 2 24, 17354525000484672⟩, ⟨.assumptionRow 16, 891242892540⟩]
  caps := #[0, 34615089709200, 588728355138000, 0, 86419313442000, 1370177327610, 3504620565810, 0, 765733209150, 0, 367268969340, 0, 994269896620, 891242892540, 891242892540, 11945018768760, 12497517107460, 1338876000000, 0, 0, 0] }

theorem case_47_27_16_checked :
    (Witness.linear .conditional case_47_27_16).check 47 27 16 = true := by
  change case_47_27_16.check 47 27 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_27_17 : Certificate := {
  objectiveScale := 362367276001731000000
  eta := 1756391214962875593683861280
  rows := #[⟨.count 2, 238715650620503880462999360⟩, ⟨.count 3, 30813880964260975327787040⟩, ⟨.count 4, 3581902771080736708045440⟩, ⟨.count 5, 340670100510396154297800⟩, ⟨.count 6, 21629847651453724082400⟩, ⟨.count 15, 54074619128634310206000⟩, ⟨.count 16, 17303878121162979265920⟩, ⟨.path 5, 79761921158282258095200⟩, ⟨.path 6, 20613050230533896935800⟩, ⟨.privateRow 3 22, 220624446044827985640480⟩, ⟨.privateRow 4 19, 33742562336267809568544⟩, ⟨.privateRow 4 20, 481264110244845360833400⟩, ⟨.privateRow 4 21, 1016602839618325031872800⟩, ⟨.privateRow 5 16, 2935479324125862554040⟩, ⟨.privateRow 5 17, 60743822154499208464740⟩, ⟨.privateRow 5 18, 171092094922998957491784⟩, ⟨.privateRow 5 19, 359055471014131819767840⟩, ⟨.privateRow 5 20, 759928647487740839428320⟩, ⟨.privateRow 6 13, 200276367143090037800⟩, ⟨.privateRow 6 14, 5632772825899407313125⟩, ⟨.privateRow 6 15, 23689833142068364471200⟩, ⟨.privateRow 6 16, 59061500670497252147220⟩, ⟨.privateRow 6 17, 122136539738542028651952⟩, ⟨.privateRow 6 18, 266587872304167149315580⟩, ⟨.privateRow 6 19, 440287565527369139099520⟩, ⟨.privateRow 7 10, 28090711235654187120⟩, ⟨.privateRow 7 11, 293547932412586255404⟩, ⟨.privateRow 7 12, 2351816768451714443880⟩, ⟨.privateRow 7 13, 8169129961218683291835⟩, ⟨.privateRow 7 14, 20393856357084939849120⟩, ⟨.privateRow 7 15, 42796198567519154077320⟩, ⟨.privateRow 7 16, 95449427707629362415048⟩, ⟨.privateRow 7 17, 165004837798232695142880⟩, ⟨.privateRow 7 18, 239215815097625115149400⟩, ⟨.privateRow 8 8, 6932643478030039770⟩, ⟨.privateRow 8 9, 121006140707433421440⟩, ⟨.privateRow 8 10, 815278873016332676952⟩, ⟨.privateRow 8 11, 2773057391212015908000⟩, ⟨.privateRow 8 12, 7144089104109955982985⟩, ⟨.privateRow 8 13, 15509313837992917542600⟩, ⟨.privateRow 8 14, 35689248624898644735960⟩, ⟨.privateRow 8 15, 64606691100457546624584⟩, ⟨.privateRow 8 16, 97979050274998552069410⟩, ⟨.privateRow 8 17, 119629695856886366271120⟩, ⟨.privateRow 9 6, 4266242140326178320⟩, ⟨.privateRow 9 7, 41595860868180238620⟩, ⟨.privateRow 9 8, 262179971532772413120⟩, ⟨.privateRow 9 9, 942839513012085408720⟩, ⟨.privateRow 9 10, 2569699849189801408080⟩, ⟨.privateRow 9 11, 5837285808501293486340⟩, ⟨.privateRow 9 12, 14031670399532800494480⟩, ⟨.privateRow 9 13, 26815464973020193830360⟩, ⟨.privateRow 9 14, 42849282809008069810416⟩, ⟨.privateRow 9 15, 56376256763340283409640⟩, ⟨.privateRow 9 16, 54407386015579752114960⟩, ⟨.privateRow 10 5, 20943370507055784480⟩, ⟨.privateRow 10 6, 83191721736360477240⟩, ⟨.privateRow 10 7, 325891538041610464560⟩, ⟨.privateRow 10 8, 948385627794509440536⟩, ⟨.privateRow 10 9, 2294074750911758614800⟩, ⟨.privateRow 10 10, 5825311242493787054010⟩, ⟨.privateRow 10 11, 11895335796328946161200⟩, ⟨.privateRow 10 12, 10913241315051651696120⟩, ⟨.privateRow 10 13, 47373904086960184493760⟩, ⟨.privateRow 11 3, 6482471823612504720⟩, ⟨.privateRow 11 4, 34905617511759640800⟩, ⟨.privateRow 11 5, 117224698810326127020⟩, ⟨.privateRow 11 6, 358893212780001397680⟩, ⟨.privateRow 11 7, 939310167241451933928⟩, ⟨.privateRow 11 8, 2571380490032960205600⟩, ⟨.privateRow 11 9, 5677835008506602571630⟩, ⟨.privateRow 11 10, 10430297164192520094480⟩, ⟨.privateRow 11 11, 10406528100839274243840⟩, ⟨.privateRow 12 1, 3697409854949354544⟩, ⟨.privateRow 12 2, 15846042235497233760⟩, ⟨.privateRow 12 3, 51194905683914139840⟩, ⟨.privateRow 12 4, 143274631879287488580⟩, ⟨.privateRow 12 5, 398311879828635012240⟩, ⟨.privateRow 12 6, 1203506907786014904072⟩, ⟨.privateRow 12 7, 2471102253057818620240⟩, ⟨.privateRow 12 8, 6814788538903529093910⟩, ⟨.privateRow 13 1, 53480392544803163940⟩, ⟨.privateRow 13 2, 63993632104892674800⟩, ⟨.privateRow 13 3, 180248730428781034020⟩, ⟨.privateRow 13 4, 589904935948737929520⟩, ⟨.privateRow 13 5, 1638876918206301401628⟩, ⟨.privateRow 13 6, 1247875826045407158600⟩, ⟨.privateRow 14 0, 121392002125505594340⟩, ⟨.privateRow 14 1, 83191721736360477240⟩, ⟨.privateRow 14 2, 308997823592196058320⟩, ⟨.privateRow 14 3, 505632802241775368160⟩, ⟨.hall 7 18, 5387539684763407853682⟩, ⟨.hall 8 18, 3432753149542453376640⟩, ⟨.hall 7 19, 135889517870258021547678⟩, ⟨.hall 6 20, 722745909382146580410480⟩, ⟨.hall 5 21, 1649030089700034487145700⟩, ⟨.hall 4 22, 3299774323453079437405440⟩, ⟨.hall 3 23, 6054915352563612494799840⟩, ⟨.hall 2 24, 9089727177046913008387776⟩]
  caps := #[0, 0, 464381558610811993110960, 0, 17896322534852113384032, 4765122488034906693696, 0, 0, 754838826694234421139, 280067215054148651976, 0, 13696299442709497152, 353740653896466106886, 299580271177112396856, 0, 1729941375632263794000, 0, 3261305484015579000000, 362367276001731000000, 0, 0] }

theorem case_47_27_17_checked :
    (Witness.linear .negative case_47_27_17).check 47 27 17 = true := by
  change case_47_27_17.check 47 27 17 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_28_1_checked :
    (Witness.rising).check 47 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_28_2_checked :
    (Witness.rising).check 47 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_28_3_checked :
    (Witness.rising).check 47 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_28_4_checked :
    (Witness.rising).check 47 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_28_5_checked :
    (Witness.rising).check 47 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_28_6_checked :
    (Witness.rising).check 47 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_28_7_checked :
    (Witness.rising).check 47 28 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_28_8_checked :
    (Witness.rising).check 47 28 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_28_9_checked :
    (Witness.rising).check 47 28 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_28_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_28_10_checked :
    (Witness.linear .positive case_47_28_10).check 47 28 10 = true := by
  change case_47_28_10.check 47 28 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_28_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_28_11_checked :
    (Witness.linear .positive case_47_28_11).check 47 28 11 = true := by
  change case_47_28_11.check 47 28 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_28_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_28_12_checked :
    (Witness.linear .positive case_47_28_12).check 47 28 12 = true := by
  change case_47_28_12.check 47 28 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_28_13 : Certificate := {
  objectiveScale := 36436400000
  eta := 42094165737143520
  rows := #[⟨.count 2, 9111291285096000⟩, ⟨.count 3, 2143833243552000⟩, ⟨.count 4, 490401854462520⟩, ⟨.count 5, 114337772989440⟩, ⟨.count 6, 27946397639160⟩, ⟨.count 7, 6802547792040⟩, ⟨.count 8, 1786527702960⟩, ⟨.count 9, 562194032400⟩, ⟨.count 10, 112438806480⟩, ⟨.path 12, 14574560000⟩, ⟨.privateRow 8 20, 181281027397470⟩, ⟨.privateRow 11 15, 2144666123600⟩, ⟨.privateRow 12 14, 4076947834960⟩, ⟨.privateRow 13 11, 23558607072⟩, ⟨.privateRow 13 13, 137425207920⟩, ⟨.hall 12 5, 67418175⟩, ⟨.hall 10 6, 473104940⟩, ⟨.hall 13 6, 203970624⟩, ⟨.hall 9 9, 335814444⟩, ⟨.hall 8 10, 148540854⟩, ⟨.hall 11 10, 141325800⟩, ⟨.hall 9 11, 12458985⟩, ⟨.hall 13 11, 631034118⟩, ⟨.hall 8 12, 224596449⟩, ⟨.hall 12 14, 10306890594⟩, ⟨.hall 6 15, 3236918685⟩, ⟨.hall 5 18, 32535414912⟩]
  caps := #[0, 132852696456480, 0, 0, 0, 291141410560, 405020255640, 0, 49866857040, 42150972864, 47881353520, 65585520000, 51010960000, 37079074747, 0, 0, 0, 0, 0, 0] }

theorem case_47_28_13_checked :
    (Witness.linear .positive case_47_28_13).check 47 28 13 = true := by
  change case_47_28_13.check 47 28 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_28_14 : Certificate := {
  objectiveScale := 1292971680000
  eta := 1443228539559206400
  rows := #[⟨.count 2, 302494870665187200⟩, ⟨.count 3, 70746497037216000⟩, ⟨.count 4, 16078749326640000⟩, ⟨.count 5, 4073283162748800⟩, ⟨.count 6, 1056603527179200⟩, ⟨.count 7, 272101911681600⟩, ⟨.count 8, 82455124752000⟩, ⟨.count 9, 26985313555200⟩, ⟨.count 10, 6746328388800⟩, ⟨.count 11, 8245512475200⟩, ⟨.path 12, 500198899200⟩, ⟨.privateRow 2 26, 9111291285096000⟩, ⟨.privateRow 3 24, 6967458041544000⟩, ⟨.privateRow 4 21, 854183557977750⟩, ⟨.privateRow 4 22, 2719988427756600⟩, ⟨.privateRow 5 19, 576691142515488⟩, ⟨.privateRow 5 20, 1061197455558240⟩, ⟨.privateRow 5 21, 1979472694879680⟩, ⟨.privateRow 6 16, 46486180026000⟩, ⟨.privateRow 6 17, 234800783817600⟩, ⟨.privateRow 6 18, 446376707496720⟩, ⟨.privateRow 6 19, 756084045717000⟩, ⟨.privateRow 6 20, 946859682568800⟩, ⟨.privateRow 7 14, 37767391962300⟩, ⟨.privateRow 7 15, 98946149702400⟩, ⟨.privateRow 7 16, 180223344100800⟩, ⟨.privateRow 7 17, 310620234244320⟩, ⟨.privateRow 7 18, 373256680797000⟩, ⟨.privateRow 7 19, 351023245372800⟩, ⟨.privateRow 8 11, 515344529700⟩, ⟨.privateRow 8 12, 21071865214400⟩, ⟨.privateRow 8 13, 45994499275725⟩, ⟨.privateRow 8 14, 76712714278200⟩, ⟨.privateRow 8 15, 60638872994700⟩, ⟨.privateRow 8 16, 303434859087360⟩, ⟨.privateRow 9 9, 1226605161600⟩, ⟨.privateRow 9 10, 9819655765920⟩, ⟨.privateRow 9 11, 22820913315200⟩, ⟨.privateRow 9 12, 36542612106000⟩, ⟨.privateRow 9 13, 60074448033600⟩, ⟨.privateRow 9 14, 33231913915200⟩, ⟨.privateRow 10 7, 1124388064800⟩, ⟨.privateRow 10 8, 4967750904480⟩, ⟨.privateRow 10 9, 11468758260960⟩, ⟨.privateRow 10 10, 19564352327520⟩, ⟨.privateRow 10 11, 11215770946380⟩, ⟨.privateRow 11 5, 807252969600⟩, ⟨.privateRow 11 6, 2873436165600⟩, ⟨.privateRow 11 7, 6337460001600⟩, ⟨.privateRow 11 8, 2623572151200⟩, ⟨.privateRow 12 3, 588965176800⟩, ⟨.privateRow 12 4, 1902810571200⟩, ⟨.privateRow 12 5, 343563019800⟩, ⟨.privateRow 13 1, 353379106080⟩, ⟨.privateRow 13 2, 126206823600⟩, ⟨.hall 6 21, 208814926320000⟩, ⟨.hall 5 22, 1787304454135200⟩, ⟨.hall 4 23, 5339484672221700⟩, ⟨.hall 3 24, 11833959504407040⟩, ⟨.hall 2 25, 9812159845488000⟩, ⟨.assumptionRow 14, 1965163028400⟩]
  caps := #[0, 919912613505600, 2085232483276800, 268332224160000, 10531535414400, 21696568951200, 23734504021800, 6682368735900, 1044143100000, 2055557632960, 2909589025200, 2360354011200, 2465361927600, 2731632377760, 14843468811600, 1292971680000, 0, 0, 0, 0] }

theorem case_47_28_14_checked :
    (Witness.linear .conditional case_47_28_14).check 47 28 14 = true := by
  change case_47_28_14.check 47 28 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_28_15 : Certificate := {
  objectiveScale := 683783100000
  eta := 885617512911331200
  rows := #[⟨.count 2, 191337116987016000⟩, ⟨.count 3, 43734198168460800⟩, ⟨.count 4, 9647249595984000⟩, ⟨.count 5, 2385014483451600⟩, ⟨.count 6, 585725868327600⟩, ⟨.count 7, 148419224553600⟩, ⟨.count 8, 41227562376000⟩, ⟨.count 9, 10119492583200⟩, ⟨.count 10, 3373164194400⟩, ⟨.path 10, 532788656400⟩, ⟨.privateRow 2 26, 12755807799134400⟩, ⟨.privateRow 3 23, 678880527124800⟩, ⟨.privateRow 3 24, 5413178939968800⟩, ⟨.privateRow 4 21, 748666765521675⟩, ⟨.privateRow 4 22, 2083537933577100⟩, ⟨.privateRow 5 19, 403040649787776⟩, ⟨.privateRow 5 20, 790538508559800⟩, ⟨.privateRow 5 21, 1548919518466320⟩, ⟨.privateRow 6 16, 22696193777400⟩, ⟨.privateRow 6 17, 152811923163900⟩, ⟨.privateRow 6 18, 317363885518680⟩, ⟨.privateRow 6 19, 587640005152200⟩, ⟨.privateRow 6 20, 805851603156600⟩, ⟨.privateRow 7 14, 16785507538800⟩, ⟨.privateRow 7 15, 60326861680800⟩, ⟨.privateRow 7 16, 124124411010600⟩, ⟨.privateRow 7 17, 237117380179680⟩, ⟨.privateRow 7 18, 321795848474100⟩, ⟨.privateRow 7 19, 351612210549600⟩, ⟨.privateRow 8 12, 8646335998300⟩, ⟨.privateRow 8 13, 25767226485000⟩, ⟨.privateRow 8 14, 50945487793200⟩, ⟨.privateRow 8 15, 98688477437550⟩, ⟨.privateRow 8 16, 140070643172460⟩, ⟨.privateRow 8 17, 155118703439700⟩, ⟨.privateRow 8 18, 41742906905700⟩, ⟨.privateRow 9 10, 3860399022480⟩, ⟨.privateRow 9 11, 11660320672000⟩, ⟨.privateRow 9 12, 22862557317600⟩, ⟨.privateRow 9 13, 44172388260000⟩, ⟨.privateRow 9 14, 65589303780000⟩, ⟨.privateRow 9 15, 35230826030400⟩, ⟨.privateRow 10 8, 1594586710080⟩, ⟨.privateRow 10 9, 5464525994928⟩, ⟨.privateRow 10 10, 8245512475200⟩, ⟨.privateRow 10 11, 28165921023240⟩, ⟨.privateRow 10 12, 17540453810880⟩, ⟨.privateRow 11 6, 624660036000⟩, ⟨.privateRow 11 7, 2657644516800⟩, ⟨.privateRow 11 8, 6034215947760⟩, ⟨.privateRow 11 9, 9494832547200⟩, ⟨.privateRow 12 4, 237851321400⟩, ⟨.privateRow 12 5, 1331306701725⟩, ⟨.privateRow 12 6, 3420013697100⟩, ⟨.privateRow 12 7, 206137811880⟩, ⟨.privateRow 13 2, 63103411800⟩, ⟨.privateRow 13 3, 679575204000⟩, ⟨.privateRow 13 4, 515344529700⟩, ⟨.privateRow 14 1, 273448117800⟩, ⟨.hall 6 21, 416585778008400⟩, ⟨.hall 5 22, 1789634707660800⟩, ⟨.hall 4 23, 4615940952522900⟩, ⟨.hall 3 24, 9595797598138752⟩, ⟨.hall 2 25, 8059988444508000⟩, ⟨.assumptionRow 15, 739579800960⟩]
  caps := #[0, 12337348041018000, 225809248785120, 178063805119200, 27395043010335, 0, 14341698356700, 436557675840, 0, 1182491805040, 5421202185672, 1846360912200, 761397741720, 4101045498000, 466131683160, 7465817399040, 683783100000, 0, 0, 0] }

theorem case_47_28_15_checked :
    (Witness.linear .conditional case_47_28_15).check 47 28 15 = true := by
  change case_47_28_15.check 47 28 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_28_16 : Certificate := {
  objectiveScale := 175949103607200000
  eta := 211607086888332380044800
  rows := #[⟨.count 2, 45391026354133025966400⟩, ⟨.count 3, 9854251595289988286400⟩, ⟨.count 4, 2088986083796854242000⟩, ⟨.count 5, 480226685930311320000⟩, ⟨.count 6, 109080061518456428400⟩, ⟨.count 7, 25488954868608831600⟩, ⟨.count 8, 5910482288373062400⟩, ⟨.count 9, 1813443429387189600⟩, ⟨.count 10, 604481143129063200⟩, ⟨.path 9, 242148494732344200⟩, ⟨.privateRow 2 26, 4571758050056563766400⟩, ⟨.privateRow 3 23, 313748101474470062400⟩, ⟨.privateRow 3 24, 1527120861258389997600⟩, ⟨.privateRow 4 21, 216102008668640094000⟩, ⟨.privateRow 4 22, 575071456401547805700⟩, ⟨.privateRow 5 19, 97966243929783509280⟩, ⟨.privateRow 5 20, 210099175094511202500⟩, ⟨.privateRow 5 21, 443089155551700577920⟩, ⟨.privateRow 6 16, 3332185167679711200⟩, ⟨.privateRow 6 17, 34416245825005644600⟩, ⟨.privateRow 6 18, 79717629864431679120⟩, ⟨.privateRow 6 19, 164820658992510420900⟩, ⟨.privateRow 6 20, 252119010113413443000⟩, ⟨.privateRow 7 14, 2097693490739546700⟩, ⟨.privateRow 7 15, 12303452926817395200⟩, ⟨.privateRow 7 16, 29657955768443402400⟩, ⟨.privateRow 7 17, 64403148077950762080⟩, ⟨.privateRow 7 18, 100293496330830402600⟩, ⟨.privateRow 7 19, 127180913526598932000⟩, ⟨.privateRow 8 12, 841422825775331800⟩, ⟨.privateRow 8 13, 4594476466352497725⟩, ⟨.privateRow 8 14, 11398787270433763200⟩, ⟨.privateRow 8 15, 25873751892591452850⟩, ⟨.privateRow 8 16, 42721704790646541660⟩, ⟨.privateRow 8 17, 55987966989471391875⟩, ⟨.privateRow 8 18, 55841744120357995800⟩, ⟨.privateRow 9 10, 235076000105746800⟩, ⟨.privateRow 9 11, 1731353397604230400⟩, ⟨.privateRow 9 12, 4617564287791455000⟩, ⟨.privateRow 9 13, 10967015025341575200⟩, ⟨.privateRow 9 14, 15962779816704520800⟩, ⟨.privateRow 9 15, 33770346529476997440⟩, ⟨.privateRow 9 16, 12139996291175352600⟩, ⟨.privateRow 10 8, 27476415596775600⟩, ⟨.privateRow 10 9, 622615577422935096⟩, ⟨.privateRow 10 10, 1947772572304759200⟩, ⟨.privateRow 10 11, 4994525445103884690⟩, ⟨.privateRow 10 12, 9438541277715229680⟩, ⟨.privateRow 10 13, 12311265948395253840⟩, ⟨.privateRow 11 7, 158752623448036800⟩, ⟨.privateRow 11 8, 826124228943053040⟩, ⟨.privateRow 11 9, 1492546032417440000⟩, ⟨.privateRow 11 10, 6926346431687182500⟩, ⟨.privateRow 11 11, 1055443265780904000⟩, ⟨.privateRow 12 5, 23087821438957275⟩, ⟨.privateRow 12 6, 293845000132183500⟩, ⟨.privateRow 12 7, 1228272100552527030⟩, ⟨.privateRow 12 8, 1918854492926671300⟩, ⟨.privateRow 13 4, 79158244933567800⟩, ⟨.privateRow 13 5, 546911510450104800⟩, ⟨.privateRow 13 6, 427454522641266120⟩, ⟨.privateRow 14 3, 200094452470963050⟩, ⟨.privateRow 14 4, 62367102068871600⟩, ⟨.privateRow 15 1, 73881028604663280⟩, ⟨.hall 7 20, 15040066537377882000⟩, ⟨.hall 6 21, 220498889364495541800⟩, ⟨.hall 5 22, 661251267104911282800⟩, ⟨.hall 4 23, 1489303009741377981150⟩, ⟨.hall 3 24, 2876749939396936931328⟩, ⟨.hall 2 25, 2436596323381794974400⟩, ⟨.assumptionRow 16, 133429431746380770⟩]
  caps := #[0, 452740837120456084200, 93977498320124994960, 55855573509738156000, 0, 0, 980950576634293980, 3595287979823276880, 432243169079992270, 7529617229847440, 152883448483516380, 1127577974719818440, 256886333937750825, 133429431746380770, 2753904374887225560, 133429431746380770, 1802010707932819230, 175949103607200000, 0, 0] }

theorem case_47_28_16_checked :
    (Witness.linear .conditional case_47_28_16).check 47 28 16 = true := by
  change case_47_28_16.check 47 28 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_28_17 : Certificate := {
  objectiveScale := 461729790522000000
  eta := 734746829473376319600000
  rows := #[⟨.count 2, 153480448823327497872000⟩, ⟨.count 3, 32501742103763470137600⟩, ⟨.count 4, 6569501063526658857600⟩, ⟨.count 5, 1411866456635115280800⟩, ⟨.count 6, 292252240294732317600⟩, ⟨.count 7, 55410771453497460000⟩, ⟨.count 8, 10343344004652859200⟩, ⟨.count 9, 1208962286258126400⟩, ⟨.path 9, 901587758789718000⟩, ⟨.privateRow 2 26, 14041828296602302996800⟩, ⟨.privateRow 3 23, 832392922279206288000⟩, ⟨.privateRow 3 24, 4898312196489175464000⟩, ⟨.privateRow 4 21, 630297525283533607500⟩, ⟨.privateRow 4 22, 1810454605957273676400⟩, ⟨.privateRow 5 19, 289672736953163788224⟩, ⟨.privateRow 5 20, 644464212518477791440⟩, ⟨.privateRow 5 21, 1429154617328606488320⟩, ⟨.privateRow 6 16, 11564642640770762400⟩, ⟨.privateRow 6 17, 98675149989966349800⟩, ⟨.privateRow 6 18, 237918020972331379680⟩, ⟨.privateRow 6 19, 519330858927493813200⟩, ⟨.privateRow 6 20, 849315195973893448800⟩, ⟨.privateRow 7 14, 7322137656355021500⟩, ⟨.privateRow 7 15, 34060661962843744800⟩, ⟨.privateRow 7 16, 85015955058651817200⟩, ⟨.privateRow 7 17, 196882386798769832160⟩, ⟨.privateRow 7 18, 331277255046981243000⟩, ⟨.privateRow 7 19, 459751086574161782400⟩, ⟨.privateRow 8 12, 3037331175969490400⟩, ⟨.privateRow 8 13, 12305808826964227575⟩, ⟨.privateRow 8 14, 31109190258892145400⟩, ⟨.privateRow 8 15, 75943540653210129900⟩, ⟨.privateRow 8 16, 136975427033045721120⟩, ⟨.privateRow 8 17, 198462913089276735900⟩, ⟨.privateRow 8 18, 226814757816316269600⟩, ⟨.privateRow 9 10, 980602743298258080⟩, ⟨.privateRow 9 11, 4507489017900668800⟩, ⟨.privateRow 9 12, 11955293719663694400⟩, ⟨.privateRow 9 13, 30588664830086563200⟩, ⟨.privateRow 9 14, 59440645741024548000⟩, ⟨.privateRow 9 15, 78018366206524423680⟩, ⟨.privateRow 9 16, 144538157779304889600⟩, ⟨.privateRow 10 8, 241792457251625280⟩, ⟨.privateRow 10 9, 1571650972135564320⟩, ⟨.privateRow 10 10, 4782117487865477760⟩, ⟨.privateRow 10 11, 13132352834478898020⟩, ⟨.privateRow 10 12, 27512527457274219360⟩, ⟨.privateRow 10 13, 46665944249563679040⟩, ⟨.privateRow 10 14, 38154849754306469184⟩, ⟨.privateRow 11 6, 22388190486261600⟩, ⟨.privateRow 11 7, 476257870344110400⟩, ⟨.privateRow 11 8, 1894040915137731360⟩, ⟨.privateRow 11 9, 6000035050318108800⟩, ⟨.privateRow 11 10, 11300439147940542600⟩, ⟨.privateRow 11 11, 30742183850563785600⟩, ⟨.privateRow 12 5, 76959404796524250⟩, ⟨.privateRow 12 6, 688436857452544200⟩, ⟨.privateRow 12 7, 2807479086977204640⟩, ⟨.privateRow 12 8, 7552282924032246400⟩, ⟨.privateRow 12 9, 7595893253416943475⟩, ⟨.privateRow 13 4, 131930408222613000⟩, ⟨.privateRow 13 5, 863544490184376000⟩, ⟨.privateRow 13 6, 5066127675748339200⟩, ⟨.privateRow 13 7, 316632979734271200⟩, ⟨.privateRow 14 3, 285849217815661500⟩, ⟨.privateRow 14 4, 1746278857928404800⟩, ⟨.privateRow 15 2, 640302247907081760⟩, ⟨.hall 7 20, 192829484658171160800⟩, ⟨.hall 6 21, 952532749897875946800⟩, ⟨.hall 5 22, 2463771693033771120000⟩, ⟨.hall 4 23, 5178044241043581807900⟩, ⟨.hall 3 24, 9602996993211249403776⟩, ⟨.hall 2 25, 8063375461912950379200⟩, ⟨.assumptionRow 17, 140020296650609760⟩]
  caps := #[0, 3421410629775148810800, 127232237833773515520, 65692060290023798400, 11814742333674624960, 17703405876727807236, 0, 745683365559972840, 1580374249992002465, 562807620847712240, 271346954549747076, 1214129554342570320, 98351396080439040, 1558639620371433600, 3782522721989831820, 140020296650609760, 23393185425031292640, 4477277608569390240, 461729790522000000, 0] }

theorem case_47_28_17_checked :
    (Witness.linear .conditional case_47_28_17).check 47 28 17 = true := by
  change case_47_28_17.check 47 28 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_28_18 : Certificate := {
  objectiveScale := 2436635916000000
  eta := 5036572397223993225600
  rows := #[⟨.count 2, 882698255183586441600⟩, ⟨.count 3, 156788386733878099200⟩, ⟨.count 4, 29525085813522499200⟩, ⟨.count 5, 6193480644790639200⟩, ⟨.count 6, 1454437724804064000⟩, ⟨.count 7, 332842479330160800⟩, ⟨.count 8, 78315877489449600⟩, ⟨.count 9, 10679437839470400⟩, ⟨.path 5, 261383923394193600⟩, ⟨.path 10, 1327511029244400⟩, ⟨.path 11, 149287208970900⟩, ⟨.privateRow 7 14, 2447371171545300⟩, ⟨.privateRow 8 12, 1269007274134600⟩, ⟨.privateRow 9 10, 474641681754240⟩, ⟨.privateRow 9 15, 74518744035415680⟩, ⟨.privateRow 9 17, 920013793133635200⟩, ⟨.privateRow 10 8, 97085798540640⟩, ⟨.privateRow 10 9, 106794378394704⟩, ⟨.privateRow 10 11, 32171806491404580⟩, ⟨.privateRow 10 13, 75290036768266320⟩, ⟨.privateRow 11 7, 323619328468800⟩, ⟨.privateRow 11 9, 8174384519100800⟩, ⟨.privateRow 11 12, 28478500905254400⟩, ⟨.privateRow 11 15, 889162083819609600⟩, ⟨.privateRow 12 7, 2121055015339260⟩, ⟨.privateRow 15 3, 1542585465701280⟩, ⟨.hall 13 4, 133190267839200⟩, ⟨.hall 14 5, 59330210219280⟩, ⟨.hall 15 5, 49441841849400⟩, ⟨.hall 12 6, 104782553370000⟩, ⟨.hall 13 6, 29059694801280⟩, ⟨.hall 11 7, 102099640606425⟩, ⟨.hall 10 8, 19063548509600⟩, ⟨.hall 9 10, 77096261390400⟩, ⟨.hall 9 12, 30762167990400⟩, ⟨.hall 8 14, 590781537706360⟩, ⟨.hall 7 15, 1058074002735750⟩, ⟨.hall 6 17, 4859724136307040⟩, ⟨.hall 5 18, 6578806794880320⟩, ⟨.hall 4 20, 41133616319495700⟩, ⟨.hall 3 22, 328302428461207200⟩]
  caps := #[0, 5876529852352988400, 1718664793038936600, 205166721789829800, 92720241219949200, 0, 0, 6304120468202700, 4192700360391400, 4227439652579520, 7977062002266396, 149287208970900, 0, 23959197298436400, 29554054490600640, 0, 23925915350937600, 107211980304000000, 21929723244000000, 2436635916000000] }

theorem case_47_28_18_checked :
    (Witness.linear .negative case_47_28_18).check 47 28 18 = true := by
  change case_47_28_18.check 47 28 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_29_1_checked :
    (Witness.rising).check 47 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_29_2_checked :
    (Witness.rising).check 47 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_29_3_checked :
    (Witness.rising).check 47 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_29_4_checked :
    (Witness.rising).check 47 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_29_5_checked :
    (Witness.rising).check 47 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_29_6_checked :
    (Witness.rising).check 47 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_29_7_checked :
    (Witness.rising).check 47 29 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_29_8_checked :
    (Witness.rising).check 47 29 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_29_9_checked :
    (Witness.rising).check 47 29 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_29_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_29_10_checked :
    (Witness.linear .positive case_47_29_10).check 47 29 10 = true := by
  change case_47_29_10.check 47 29 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_29_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_29_11_checked :
    (Witness.linear .positive case_47_29_11).check 47 29 11 = true := by
  change case_47_29_11.check 47 29 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_29_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_29_12_checked :
    (Witness.linear .positive case_47_29_12).check 47 29 12 = true := by
  change case_47_29_12.check 47 29 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_29_13 : Certificate := {
  objectiveScale := 50277500000
  eta := 174253445827461000
  rows := #[⟨.count 2, 34752024112806000⟩, ⟨.count 3, 6783222372176250⟩, ⟨.count 4, 1430643263949900⟩, ⟨.count 5, 293645990137500⟩, ⟨.count 6, 62343302521500⟩, ⟨.count 7, 13703479539750⟩, ⟨.count 8, 3066512904000⟩, ⟨.count 9, 689965403400⟩, ⟨.path 10, 83783894103⟩, ⟨.hall 11 6, 146012625⟩, ⟨.hall 9 7, 73181745⟩, ⟨.hall 10 13, 473279625⟩]
  caps := #[0, 0, 0, 3555719120590, 0, 425234304404, 0, 120862987245, 0, 64125461218, 184338894103, 50277500000, 50277500000, 0, 0, 0, 0, 0, 0] }

theorem case_47_29_13_checked :
    (Witness.linear .positive case_47_29_13).check 47 29 13 = true := by
  change case_47_29_13.check 47 29 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_29_14 : Certificate := {
  objectiveScale := 739688647100000
  eta := 2920417832110957778600
  rows := #[⟨.count 2, 606593886426292244480⟩, ⟨.count 3, 118623462653188498005⟩, ⟨.count 4, 25116778109838663248⟩, ⟨.count 5, 5077515790398651600⟩, ⟨.count 6, 1093618785624324960⟩, ⟨.count 7, 239229109355321085⟩, ⟨.count 8, 49709944801105680⟩, ⟨.count 9, 14912983440331704⟩, ⟨.path 8, 629083668698856⟩, ⟨.path 9, 1951832056159440⟩]
  caps := #[0, 0, 0, 91975616600374899, 17453339060070928, 0, 0, 0, 1504382607387576, 0, 3698443235500000, 1479377294200000, 739688647100000, 739688647100000, 0, 0, 0, 0, 0] }

theorem case_47_29_14_checked :
    (Witness.linear .positive case_47_29_14).check 47 29 14 = true := by
  change case_47_29_14.check 47 29 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_29_15 : Certificate := {
  objectiveScale := 1144773720090000000
  eta := 4283755936427227812552000
  rows := #[⟨.count 2, 803629889504630972784000⟩, ⟨.count 3, 152383209980221339119000⟩, ⟨.count 4, 31554958938176187914400⟩, ⟨.count 5, 6323964021525546396000⟩, ⟨.count 6, 1347116596301299824000⟩, ⟨.count 7, 283767616350505287000⟩, ⟨.count 8, 63500445616896288000⟩, ⟨.count 9, 14287600263801664800⟩, ⟨.path 9, 3306443006634768000⟩, ⟨.privateRow 2 27, 31781973031256592144000⟩, ⟨.privateRow 3 24, 3972746628907074018000⟩, ⟨.privateRow 3 25, 18444895062782843655000⟩, ⟨.privateRow 4 22, 4043688532994700339750⟩, ⟨.privateRow 4 23, 7113108249852665860800⟩, ⟨.privateRow 4 24, 12230384264706777869700⟩, ⟨.privateRow 5 19, 456730734887956128600⟩, ⟨.privateRow 5 20, 1621529236288601640000⟩, ⟨.privateRow 5 21, 2837676163505052870000⟩, ⟨.privateRow 5 22, 4810536734322851532000⟩, ⟨.privateRow 5 23, 5375369418296714436600⟩, ⟨.privateRow 6 16, 16371208635606074250⟩, ⟨.privateRow 6 17, 309159695050628994000⟩, ⟨.privateRow 6 18, 647572252697306937000⟩, ⟨.privateRow 6 19, 1101392550494488652400⟩, ⟨.privateRow 6 20, 1872554435367894778500⟩, ⟨.privateRow 6 21, 2214011072624821470000⟩, ⟨.privateRow 6 22, 1830457041733479159000⟩, ⟨.privateRow 7 14, 28064929089610413000⟩, ⟨.privateRow 7 15, 137985901357251197250⟩, ⟨.privateRow 7 16, 281985716090847483000⟩, ⟨.privateRow 7 17, 446959981797499170000⟩, ⟨.privateRow 7 18, 757753085419481151000⟩, ⟨.privateRow 7 19, 919126427684741025750⟩, ⟨.privateRow 7 20, 782699689054690407000⟩, ⟨.privateRow 8 12, 19248572577621687300⟩, ⟨.privateRow 8 13, 61736544349760280000⟩, ⟨.privateRow 8 14, 126256745386719572625⟩, ⟨.privateRow 8 15, 201840702139420344000⟩, ⟨.privateRow 8 16, 331723682050765504500⟩, ⟨.privateRow 8 17, 417515429931093093600⟩, ⟨.privateRow 8 18, 28773639420156130500⟩, ⟨.privateRow 9 10, 10246662815453719200⟩, ⟨.privateRow 9 11, 30321462782067977520⟩, ⟨.privateRow 9 12, 60678203589478675200⟩, ⟨.privateRow 9 13, 62111373369026681700⟩, ⟨.privateRow 9 14, 240848118732656635200⟩, ⟨.privateRow 10 8, 5027118611337622800⟩, ⟨.privateRow 10 9, 16308068987975637600⟩, ⟨.privateRow 10 10, 33020231720786069760⟩, ⟨.privateRow 10 11, 54857329407929848800⟩, ⟨.privateRow 10 12, 19645450362727289100⟩, ⟨.privateRow 11 6, 2289679529455395000⟩, ⟨.privateRow 11 7, 9260481652464042000⟩, ⟨.privateRow 11 8, 20565485228199366000⟩, ⟨.privateRow 11 9, 5357850098925624300⟩, ⟨.privateRow 12 4, 1113687662286127500⟩, ⟨.privateRow 12 5, 5756908531202136000⟩, ⟨.privateRow 12 6, 3378185908934586750⟩, ⟨.privateRow 13 2, 415776727253487600⟩, ⟨.privateRow 13 3, 1781900259657804000⟩, ⟨.hall 5 23, 1050615817678656479250⟩, ⟨.hall 4 24, 4458556788099139069344⟩, ⟨.hall 3 25, 11230649124025766935500⟩, ⟨.hall 2 26, 22028774958172558576000⟩, ⟨.assumptionRow 15, 1301378764998312000⟩]
  caps := #[0, 0, 0, 7130166058880865000, 0, 29432991342016342080, 21040944372781047000, 6154342267138065000, 830044292549472000, 12658725212341004160, 5988540284534808000, 49047375952575315000, 1301378764998312000, 54048583237849200, 84810332098123632000, 13580679596171688000, 1144773720090000000, 0, 0] }

theorem case_47_29_15_checked :
    (Witness.linear .conditional case_47_29_15).check 47 29 15 = true := by
  change case_47_29_15.check 47 29 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_29_16 : Certificate := {
  objectiveScale := 4534575902356500000
  eta := 12801097694710914102914400
  rows := #[⟨.count 2, 2477177783693370953395200⟩, ⟨.count 3, 467109873274566752930700⟩, ⟨.count 4, 91486679511402904528800⟩, ⟨.count 5, 17090918150481861285600⟩, ⟨.count 6, 3480051207111691212000⟩, ⟨.count 7, 676676623605051069000⟩, ⟨.count 8, 147638536059283869600⟩, ⟨.count 9, 44291560817785160880⟩, ⟨.count 10, 49212845353094623200⟩, ⟨.path 8, 20878388273159746560⟩, ⟨.path 9, 1717217174413540800⟩, ⟨.privateRow 2 27, 260385164763223651351200⟩, ⟨.privateRow 3 24, 32254919058507434289000⟩, ⟨.privateRow 3 25, 83129723209880523826650⟩, ⟨.privateRow 4 21, 1794546405800595434988⟩, ⟨.privateRow 4 22, 17373672311059686196575⟩, ⟨.privateRow 4 23, 31844401906853703307140⟩, ⟨.privateRow 4 24, 56475431006077562218740⟩, ⟨.privateRow 5 19, 1935295143510446057340⟩, ⟨.privateRow 5 20, 6434228009593171307520⟩, ⟨.privateRow 5 21, 12064177517987196201600⟩, ⟨.privateRow 5 22, 22301972606167997422680⟩, ⟨.privateRow 5 23, 27219800524958611429860⟩, ⟨.privateRow 6 17, 1035729525926098575000⟩, ⟨.privateRow 6 18, 2442480384250612906200⟩, ⟨.privateRow 6 19, 4551133634189400618360⟩, ⟨.privateRow 6 20, 8564792693058217816200⟩, ⟨.privateRow 6 21, 11503502601285868173000⟩, ⟨.privateRow 6 22, 11145830671666055465100⟩, ⟨.privateRow 7 14, 23629977332239878600⟩, ⟨.privateRow 7 15, 410839378617352434750⟩, ⟨.privateRow 7 16, 998443262992759026300⟩, ⟨.privateRow 7 17, 1804470996280136184000⟩, ⟨.privateRow 7 18, 3431717162568473278500⟩, ⟨.privateRow 7 19, 4792320516460058106525⟩, ⟨.privateRow 7 20, 5213632271395107760200⟩, ⟨.privateRow 7 21, 3228714175486957957800⟩, ⟨.privateRow 8 12, 13533532472101021380⟩, ⟨.privateRow 8 13, 157891212174511916100⟩, ⟨.privateRow 8 14, 416771284084020090225⟩, ⟨.privateRow 8 15, 778617517550747074200⟩, ⟨.privateRow 8 16, 1477410628204361500650⟩, ⟨.privateRow 8 17, 2155522626465544496160⟩, ⟨.privateRow 8 18, 2452952760568310125125⟩, ⟨.privateRow 9 10, 3579116025679608960⟩, ⟨.privateRow 9 11, 62008185144899225232⟩, ⟨.privateRow 9 12, 180447099628013618400⟩, ⟨.privateRow 9 13, 360484092211418114940⟩, ⟨.privateRow 9 14, 707961932436661222320⟩, ⟨.privateRow 9 15, 1072019814608244542040⟩, ⟨.privateRow 9 16, 438978580549604038944⟩, ⟨.privateRow 10 9, 23711643670127409360⟩, ⟨.privateRow 10 10, 82677580193198966976⟩, ⟨.privateRow 10 11, 179353480842389293440⟩, ⟨.privateRow 10 12, 375863106384260184690⟩, ⟨.privateRow 10 13, 356441608485985342320⟩, ⟨.privateRow 11 7, 7176873280659632550⟩, ⟨.privateRow 11 8, 38587344651858284100⟩, ⟨.privateRow 11 9, 97195369572361880820⟩, ⟨.privateRow 11 10, 200268940117454508300⟩, ⟨.privateRow 12 5, 2230802055840827700⟩, ⟨.privateRow 12 6, 16916915590126276725⟩, ⟨.privateRow 12 7, 56243251832108140800⟩, ⟨.privateRow 12 8, 34800512071116912120⟩, ⟨.privateRow 13 4, 7436006852802759000⟩, ⟨.privateRow 13 5, 24167022271608966750⟩, ⟨.privateRow 14 2, 3590529023210475060⟩, ⟨.privateRow 14 3, 7733447126914869360⟩, ⟨.hall 6 22, 126088811851872870000⟩, ⟨.hall 5 23, 8011367883038372477625⟩, ⟨.hall 4 24, 24912526574643560156304⟩, ⟨.hall 3 25, 56434830408661259154600⟩, ⟨.hall 2 26, 108949948819847333598400⟩, ⟨.assumptionRow 16, 3798988828804669500⟩]
  caps := #[0, 9196588621828430222400, 0, 0, 715879190236583511369, 3081001848051928680, 0, 57129015731830993170, 25629662548249671870, 95836853382626760768, 0, 91333959315703622700, 3798988828804669500, 148517364167610807600, 208459805594194440, 299775489706989796500, 50615921999473330500, 4534575902356500000, 0] }

theorem case_47_29_16_checked :
    (Witness.linear .conditional case_47_29_16).check 47 29 16 = true := by
  change case_47_29_16.check 47 29 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_29_17 : Certificate := {
  objectiveScale := 5929308000000
  eta := 19573787067771736800
  rows := #[⟨.count 2, 3698433920113732800⟩, ⟨.count 3, 672895659319884000⟩, ⟨.count 4, 124111866052334160⟩, ⟨.count 5, 21539781687223800⟩, ⟨.count 6, 3697228897362000⟩, ⟨.count 7, 575124495145200⟩, ⟨.count 8, 69712060017600⟩, ⟨.path 8, 39552512464080⟩, ⟨.privateRow 2 27, 403737395591930400⟩, ⟨.privateRow 3 24, 46936549076016600⟩, ⟨.privateRow 3 25, 126167936122478250⟩, ⟨.privateRow 4 21, 2417439961260324⟩, ⟨.privateRow 4 22, 24797451149010540⟩, ⟨.privateRow 4 23, 47476527074236260⟩, ⟨.privateRow 4 24, 88161792401632950⟩, ⟨.privateRow 5 19, 2604948804598140⟩, ⟨.privateRow 5 20, 8893615645402488⟩, ⟨.privateRow 5 21, 17552251854217080⟩, ⟨.privateRow 5 22, 34475518347870600⟩, ⟨.privateRow 5 23, 45037725346013400⟩, ⟨.privateRow 6 16, 41080321081800⟩, ⟨.privateRow 6 17, 1298920628491200⟩, ⟨.privateRow 6 18, 3249909845582400⟩, ⟨.privateRow 6 19, 6433178281409880⟩, ⟨.privateRow 6 20, 13005344982479850⟩, ⟨.privateRow 6 21, 19043011061474400⟩, ⟨.privateRow 6 22, 20444306458375800⟩, ⟨.privateRow 7 14, 54013014755700⟩, ⟨.privateRow 7 15, 489540492891450⟩, ⟨.privateRow 7 16, 1259796513175200⟩, ⟨.privateRow 7 17, 2454549184637550⟩, ⟨.privateRow 7 18, 5078897029746540⟩, ⟨.privateRow 7 19, 7827512846127975⟩, ⟨.privateRow 7 20, 9617359613261400⟩, ⟨.privateRow 7 21, 7500581957518650⟩, ⟨.privateRow 8 12, 26577722881710⟩, ⟨.privateRow 8 13, 179121265323000⟩, ⟨.privateRow 8 14, 495609176687625⟩, ⟨.privateRow 8 15, 1007090295611400⟩, ⟨.privateRow 8 16, 2109515982824250⟩, ⟨.privateRow 8 17, 3429833352865920⟩, ⟨.privateRow 8 18, 4500784874886300⟩, ⟨.privateRow 8 19, 2983095234919800⟩, ⟨.privateRow 9 10, 8555571002160⟩, ⟨.privateRow 9 11, 66575017316808⟩, ⟨.privateRow 9 12, 201390395606400⟩, ⟨.privateRow 9 13, 437878876985550⟩, ⟨.privateRow 9 14, 959536711813680⟩, ⟨.privateRow 9 15, 1436649370196040⟩, ⟨.privateRow 9 16, 2709707772884112⟩, ⟨.privateRow 10 8, 1452334583700⟩, ⟨.privateRow 10 9, 24399221006160⟩, ⟨.privateRow 10 10, 85745833821648⟩, ⟨.privateRow 10 11, 203326841718000⟩, ⟨.privateRow 10 12, 398230142850540⟩, ⟨.privateRow 10 13, 1029248771831280⟩, ⟨.privateRow 10 14, 548401538805120⟩, ⟨.privateRow 11 7, 7624756564425⟩, ⟨.privateRow 11 8, 37628668759500⟩, ⟨.privateRow 11 9, 101953887775740⟩, ⟨.privateRow 11 10, 259967890482300⟩, ⟨.privateRow 11 11, 443325131674425⟩, ⟨.privateRow 12 5, 1580012349300⟩, ⟨.privateRow 12 6, 15405120405675⟩, ⟨.privateRow 12 7, 34233600901500⟩, ⟨.privateRow 12 8, 197185541192640⟩, ⟨.privateRow 12 9, 54773761442400⟩, ⟨.privateRow 13 4, 5266707831000⟩, ⟨.privateRow 13 5, 27386880721200⟩, ⟨.privateRow 13 6, 67222343588400⟩, ⟨.privateRow 14 3, 10954752288480⟩, ⟨.privateRow 14 4, 17801472468780⟩, ⟨.privateRow 15 2, 9585408252420⟩, ⟨.hall 6 22, 2657718163900800⟩, ⟨.hall 5 23, 16503448434598125⟩, ⟨.hall 4 24, 43962516408899088⟩, ⟨.hall 3 25, 92954496527842950⟩, ⟨.hall 2 26, 172423743705012800⟩, ⟨.assumptionRow 17, 2698156310850⟩]
  caps := #[0, 10727542633257450, 0, 0, 351356474044422, 48821223962016, 66563170349940, 0, 27764396759715, 50836740159660, 13750328657016, 3372046870500, 8784608266665, 0, 339175430914320, 2698156310850, 353027144269800, 62524231689150, 5929308000000] }

theorem case_47_29_17_checked :
    (Witness.linear .conditional case_47_29_17).check 47 29 17 = true := by
  change case_47_29_17.check 47 29 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_29_18 : Certificate := {
  objectiveScale := 3132581420468500000
  eta := 13080249357835451170579200
  rows := #[⟨.count 2, 2599160023041908159433600⟩, ⟨.count 3, 480305067434865248776200⟩, ⟨.count 4, 93832491806567081568000⟩, ⟨.count 5, 17090918150481861285600⟩, ⟨.count 6, 3016044379496799050400⟩, ⟨.count 7, 496229523977037450600⟩, ⟨.count 8, 65617127137459497600⟩, ⟨.path 8, 15540163998772311360⟩, ⟨.path 9, 4970330455134844800⟩, ⟨.privateRow 5 19, 1010933393868371533560⟩, ⟨.privateRow 6 17, 648136521112865241600⟩, ⟨.privateRow 6 18, 1550985784897926577200⟩, ⟨.privateRow 7 14, 15037258302334468200⟩, ⟨.privateRow 7 15, 265031677578645002025⟩, ⟨.privateRow 7 16, 693248296019868646200⟩, ⟨.privateRow 7 19, 3782944552915856928600⟩, ⟨.privateRow 8 12, 12713318382882777660⟩, ⟨.privateRow 8 13, 95235969248118298600⟩, ⟨.privateRow 8 14, 277334888916918657825⟩, ⟨.privateRow 8 17, 3658154837913366991200⟩, ⟨.privateRow 8 19, 3706000659784431208200⟩, ⟨.privateRow 9 10, 6263453044939315680⟩, ⟨.privateRow 9 14, 440572139351513769600⟩, ⟨.privateRow 9 17, 6756923666979891765360⟩, ⟨.privateRow 10 8, 2460642267654731160⟩, ⟨.privateRow 10 10, 18044709962801361840⟩, ⟨.privateRow 10 11, 13487965022700007840⟩, ⟨.privateRow 10 15, 1469167476607718151264⟩, ⟨.privateRow 11 8, 745649172016585200⟩, ⟨.privateRow 11 15, 1801395193445567770050⟩, ⟨.privateRow 12 14, 114390572085615775950⟩, ⟨.privateRow 14 12, 41889505270788875700⟩, ⟨.privateRow 15 11, 29322653689552212990⟩, ⟨.hall 12 5, 252032725263062700⟩, ⟨.hall 13 5, 92064846748986540⟩, ⟨.hall 11 6, 68736197799017100⟩, ⟨.hall 10 7, 22951930336542900⟩, ⟨.hall 9 9, 61081435031803956⟩, ⟨.hall 11 9, 58321622374923600⟩, ⟨.hall 7 13, 58485952305060280⟩, ⟨.hall 6 15, 259890345847232100⟩, ⟨.hall 5 18, 2835250624215330750⟩, ⟨.hall 4 20, 15718222794625391040⟩, ⟨.hall 3 23, 753366640946956856820⟩]
  caps := #[0, 13139893690339064448800, 0, 0, 0, 0, 0, 0, 2204989891435824955, 52478629005339380480, 0, 3626904361793976900, 56901775212100068250, 0, 0, 646612295119032702460, 651576935457448000000, 169159396705299000000, 31325814204685000000] }

theorem case_47_29_18_checked :
    (Witness.linear .negative case_47_29_18).check 47 29 18 = true := by
  change case_47_29_18.check 47 29 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_30_1_checked :
    (Witness.rising).check 47 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_30_2_checked :
    (Witness.rising).check 47 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_30_3_checked :
    (Witness.rising).check 47 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_30_4_checked :
    (Witness.rising).check 47 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_30_5_checked :
    (Witness.rising).check 47 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_30_6_checked :
    (Witness.rising).check 47 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_30_7_checked :
    (Witness.rising).check 47 30 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_30_8_checked :
    (Witness.rising).check 47 30 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_30_9_checked :
    (Witness.rising).check 47 30 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_30_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_30_10_checked :
    (Witness.linear .positive case_47_30_10).check 47 30 10 = true := by
  change case_47_30_10.check 47 30 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_30_11_checked :
    (Witness.linear .positive case_47_30_11).check 47 30 11 = true := by
  change case_47_30_11.check 47 30 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_30_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_47_30_12_checked :
    (Witness.linear .positive case_47_30_12).check 47 30 12 = true := by
  change case_47_30_12.check 47 30 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_30_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_47_30_13_checked :
    (Witness.linear .positive case_47_30_13).check 47 30 13 = true := by
  change case_47_30_13.check 47 30 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_30_14 : Certificate := {
  objectiveScale := 11534524500
  eta := 215952869570638200
  rows := #[⟨.count 2, 24572207355350655⟩, ⟨.count 3, 3279658065909225⟩, ⟨.count 4, 530511722309712⟩, ⟨.count 5, 93150051576120⟩, ⟨.count 6, 17188402374165⟩, ⟨.count 7, 3175569940095⟩, ⟨.count 8, 564545767128⟩, ⟨.count 9, 282272883564⟩, ⟨.path 3, 357666772567104⟩, ⟨.path 8, 136754785244⟩]
  caps := #[0, 191272907610372, 19736174489345, 1240664016375, 0, 0, 204594093539, 0, 56659047116, 0, 57672622500, 23069049000, 11534524500, 11534524500, 0, 0, 0, 0] }

theorem case_47_30_14_checked :
    (Witness.linear .positive case_47_30_14).check 47 30 14 = true := by
  change case_47_30_14.check 47 30 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_30_15 : Certificate := {
  objectiveScale := 102580978500000
  eta := 698147656712358652800
  rows := #[⟨.count 2, 117781903623675891600⟩, ⟨.count 3, 20627089857410596560⟩, ⟨.count 4, 3696486094481019840⟩, ⟨.count 5, 657212694592053600⟩, ⟨.count 6, 120712535741397600⟩, ⟨.count 7, 21338074499742000⟩, ⟨.count 8, 3414091919958720⟩, ⟨.path 8, 1095691182746160⟩, ⟨.privateRow 2 28, 10374571821774560400⟩, ⟨.privateRow 3 25, 2129160491527589520⟩, ⟨.privateRow 3 26, 3376821416499170640⟩, ⟨.privateRow 4 22, 367904983931837352⟩, ⟨.privateRow 4 23, 893608077085623900⟩, ⟨.privateRow 4 24, 1319343307306904880⟩, ⟨.privateRow 4 25, 1970296833379034160⟩, ⟨.privateRow 5 19, 50967515090812320⟩, ⟨.privateRow 5 20, 198952142240451600⟩, ⟨.privateRow 5 21, 340141100711315904⟩, ⟨.privateRow 5 22, 499615772929673400⟩, ⟨.privateRow 5 23, 764512726362184800⟩, ⟨.privateRow 5 24, 720251463257005680⟩, ⟨.privateRow 6 16, 3974075250745600⟩, ⟨.privateRow 6 17, 38002094585254800⟩, ⟨.privateRow 6 18, 84945858484687200⟩, ⟨.privateRow 6 19, 138782159147131500⟩, ⟨.privateRow 6 20, 194257765850508360⟩, ⟨.privateRow 6 21, 200349278070791850⟩, ⟨.privateRow 6 22, 486948408067921800⟩, ⟨.privateRow 6 23, 58679704874290500⟩, ⟨.privateRow 7 14, 4633410462801120⟩, ⟨.privateRow 7 15, 19305876928338000⟩, ⟨.privateRow 7 16, 38027497054897350⟩, ⟨.privateRow 7 17, 60182079507435600⟩, ⟨.privateRow 7 18, 83015270791853400⟩, ⟨.privateRow 7 19, 123029240972798160⟩, ⟨.privateRow 7 20, 94192357434575400⟩, ⟨.privateRow 8 12, 3181312925416080⟩, ⟨.privateRow 8 13, 9687485822882868⟩, ⟨.privateRow 8 14, 18587833786441920⟩, ⟨.privateRow 8 15, 28966436133399765⟩, ⟨.privateRow 8 16, 39688818569520120⟩, ⟨.privateRow 8 17, 43671925809471960⟩, ⟨.privateRow 9 10, 1865105771088560⟩, ⟨.privateRow 9 11, 5345295430238400⟩, ⟨.privateRow 9 12, 10204341405209952⟩, ⟨.privateRow 9 13, 16058876808694720⟩, ⟨.privateRow 9 14, 12992516473176240⟩, ⟨.privateRow 10 8, 1083317628448440⟩, ⟨.privateRow 10 9, 3342965004959580⟩, ⟨.privateRow 10 10, 6517811847193920⟩, ⟨.privateRow 10 11, 3243387323960784⟩, ⟨.privateRow 11 6, 653206362237000⟩, ⟨.privateRow 11 7, 2344843351620000⟩, ⟨.privateRow 11 8, 1016098785702000⟩, ⟨.privateRow 12 4, 447083465708880⟩, ⟨.privateRow 12 5, 558854332136100⟩, ⟨.privateRow 13 2, 167656299640830⟩, ⟨.hall 4 25, 394327616755232160⟩, ⟨.hall 3 26, 1374235221707828480⟩, ⟨.hall 2 27, 3400069756716032400⟩, ⟨.assumptionRow 15, 121258923065280⟩]
  caps := #[0, 2391912657771436800, 181134928338764400, 73201354521327032, 16797131837409924, 1352337375589200, 0, 287606547442500, 901328951162640, 2286171395953536, 578425415087520, 265646046631680, 121258923065280, 8513605729629000, 8849537918020800, 1314874775934720, 102580978500000, 0] }

theorem case_47_30_15_checked :
    (Witness.linear .conditional case_47_30_15).check 47 30 15 = true := by
  change case_47_30_15.check 47 30 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_30_16 : Certificate := {
  objectiveScale := 59805726230250000
  eta := 503026371341219383257600
  rows := #[⟨.count 2, 75395735056351747837800⟩, ⟨.count 3, 11760570255894249469680⟩, ⟨.count 4, 1846426164645348926640⟩, ⟨.count 5, 275108541509875273200⟩, ⟨.count 6, 44785111408584346800⟩, ⟨.count 7, 8142747528833517600⟩, ⟨.count 8, 1628549505766703520⟩, ⟨.count 9, 1628549505766703520⟩, ⟨.path 3, 128970510366359581920⟩, ⟨.path 7, 1938244995078472080⟩, ⟨.privateRow 2 28, 6986477379739158100800⟩, ⟨.privateRow 3 25, 1319667949506285419040⟩, ⟨.privateRow 3 26, 2222087944389260007060⟩, ⟨.privateRow 4 22, 197118468928354817844⟩, ⟨.privateRow 4 23, 540620273432196757800⟩, ⟨.privateRow 4 24, 863606231662201487460⟩, ⟨.privateRow 4 25, 1384819623484011694980⟩, ⟨.privateRow 5 19, 20473193786781415680⟩, ⟨.privateRow 5 20, 104711855721975782280⟩, ⟨.privateRow 5 21, 200893214032792641360⟩, ⟨.privateRow 5 22, 325011951365154973920⟩, ⟨.privateRow 5 23, 547231408925844923280⟩, ⟨.privateRow 5 24, 586045172146618023840⟩, ⟨.privateRow 6 16, 59239565355270300⟩, ⟨.privateRow 6 17, 15594815579774906475⟩, ⟨.privateRow 6 18, 43261808299448824800⟩, ⟨.privateRow 6 19, 80239991273713621350⟩, ⟨.privateRow 6 20, 125931468032233603740⟩, ⟨.privateRow 6 21, 214062169411269229050⟩, ⟨.privateRow 6 22, 252005111021319856200⟩, ⟨.privateRow 6 23, 197001174588951382650⟩, ⟨.privateRow 7 14, 348974894092865040⟩, ⟨.privateRow 7 15, 7593435195539193000⟩, ⟨.privateRow 7 16, 18466588145747441700⟩, ⟨.privateRow 7 17, 33900418283306889600⟩, ⟨.privateRow 7 18, 53121733878580567200⟩, ⟨.privateRow 7 19, 89570222817168693600⟩, ⟨.privateRow 7 20, 110581419565676609550⟩, ⟨.privateRow 7 21, 61652231289739490400⟩, ⟨.privateRow 8 12, 185062443837125400⟩, ⟨.privateRow 8 13, 3419953962110077392⟩, ⟨.privateRow 8 14, 8527266162139544820⟩, ⟨.privateRow 8 15, 15674788993004521380⟩, ⟨.privateRow 8 16, 24689973757070201580⟩, ⟨.privateRow 8 17, 41901221658789142650⟩, ⟨.privateRow 8 18, 44785111408584346800⟩, ⟨.privateRow 9 10, 30158324180864880⟩, ⟨.privateRow 9 11, 1546299530727981120⟩, ⟨.privateRow 9 12, 4288513698518985936⟩, ⟨.privateRow 9 13, 8162853078287427520⟩, ⟨.privateRow 9 14, 12530783697149357640⟩, ⟨.privateRow 9 15, 23394242900299471200⟩, ⟨.privateRow 10 9, 695526351421196295⟩, ⟨.privateRow 10 10, 2350293036731492580⟩, ⟨.privateRow 10 11, 4844934779655942972⟩, ⟨.privateRow 10 12, 8029653813155274300⟩, ⟨.privateRow 10 13, 1323196473435446610⟩, ⟨.privateRow 11 7, 313182597262827600⟩, ⟨.privateRow 11 8, 1381358955784257450⟩, ⟨.privateRow 11 9, 3278249005114792800⟩, ⟨.privateRow 11 10, 639787305836919240⟩, ⟨.privateRow 12 5, 152330310913552200⟩, ⟨.privateRow 12 6, 861252142472775900⟩, ⟨.privateRow 12 7, 666445110246790875⟩, ⟨.privateRow 13 3, 85304974111589232⟩, ⟨.privateRow 13 4, 365592746192525280⟩, ⟨.hall 5 24, 52206644156292609984⟩, ⟨.hall 4 25, 374915361220434674640⟩, ⟨.hall 3 26, 1060909528034464748640⟩, ⟨.hall 2 27, 2391205055565485659500⟩, ⟨.assumptionRow 16, 54162784116215775⟩]
  caps := #[0, 2017185590816882806320, 0, 9668338450672313412, 6032518156555540650, 20489893771222315440, 0, 272552354335217970, 1865457531695783844, 0, 451712967913612503, 162870499587522375, 2423398676471375625, 0, 20681589993223559400, 4624236383095479150, 723311656877034225, 59805726230250000] }

theorem case_47_30_16_checked :
    (Witness.linear .conditional case_47_30_16).check 47 30 16 = true := by
  change case_47_30_16.check 47 30 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_30_17 : Certificate := {
  objectiveScale := 1411056615969000000
  eta := 13431324594731180417280000
  rows := #[⟨.count 2, 1968528510915288629907600⟩, ⟨.count 3, 287094563212378981419360⟩, ⟨.count 4, 40054128702144770172960⟩, ⟨.count 5, 5073645966416311284000⟩, ⟨.count 6, 599612705121927697200⟩, ⟨.count 7, 58703341760188725600⟩, ⟨.count 8, 23481336704075490240⟩, ⟨.path 6, 112889843049379968000⟩, ⟨.path 7, 24680201985511712640⟩, ⟨.privateRow 2 28, 188878002113407224618000⟩, ⟨.privateRow 3 25, 33671584574291362018320⟩, ⟨.privateRow 3 26, 59461593257924496639000⟩, ⟨.privateRow 4 22, 4724948116360790253936⟩, ⟨.privateRow 4 23, 13476295547615324994570⟩, ⟨.privateRow 4 24, 22745308614291790647120⟩, ⟨.privateRow 4 25, 38495135668827758160240⟩, ⟨.privateRow 5 19, 469147523128365407040⟩, ⟨.privateRow 5 20, 2373851324892965037120⟩, ⟨.privateRow 5 21, 4867010203420446969888⟩, ⟨.privateRow 5 22, 8403802682555017417680⟩, ⟨.privateRow 5 23, 15227087773147620289920⟩, ⟨.privateRow 5 24, 17813109747545267435280⟩, ⟨.privateRow 6 16, 12812237288930079000⟩, ⟨.privateRow 6 17, 312298283917670675625⟩, ⟨.privateRow 6 18, 937855769549681782800⟩, ⟨.privateRow 6 19, 1875711539099363565600⟩, ⟨.privateRow 6 20, 3190247084943589671000⟩, ⟨.privateRow 6 21, 5903878942738980403200⟩, ⟨.privateRow 6 22, 7759090902176055842400⟩, ⟨.privateRow 6 23, 7110791695356193845000⟩, ⟨.privateRow 7 14, 10482739600033701000⟩, ⟨.privateRow 7 15, 141167559947120506800⟩, ⟨.privateRow 7 16, 378951036541218291150⟩, ⟨.privateRow 7 17, 761346401808161941200⟩, ⟨.privateRow 7 18, 1305450504857530231200⟩, ⟨.privateRow 7 19, 2430318348871813239840⟩, ⟨.privateRow 7 20, 2849208623289159931800⟩, ⟨.privateRow 7 21, 4638961697668247149200⟩, ⟨.privateRow 8 12, 3735667202921100720⟩, ⟨.privateRow 8 13, 59290375177790612856⟩, ⟨.privateRow 8 14, 164369356928528431680⟩, ⟨.privateRow 8 15, 334609048033075735920⟩, ⟨.privateRow 8 16, 582421012177872427560⟩, ⟨.privateRow 8 17, 1100687658003538605000⟩, ⟨.privateRow 8 18, 1607884530811569194184⟩, ⟨.privateRow 8 19, 1135909663059651840360⟩, ⟨.privateRow 9 10, 434839568593990560⟩, ⟨.privateRow 9 11, 24667262800240919040⟩, ⟨.privateRow 9 12, 76966603641136329120⟩, ⟨.privateRow 9 13, 163209784745611123520⟩, ⟨.privateRow 9 14, 290255412036488698800⟩, ⟨.privateRow 9 15, 558706725704907299520⟩, ⟨.privateRow 9 16, 807497078879040469920⟩, ⟨.privateRow 10 9, 9539293036030667910⟩, ⟨.privateRow 10 10, 38957672259034336080⟩, ⟨.privateRow 10 11, 89816112893088750168⟩, ⟨.privateRow 10 12, 166000005310755896280⟩, ⟨.privateRow 10 13, 326904234427050965685⟩, ⟨.privateRow 10 14, 95183275568306005080⟩, ⟨.privateRow 11 7, 3870550006166289600⟩, ⟨.privateRow 11 8, 20616054546732945300⟩, ⟨.privateRow 11 9, 55653817512906194400⟩, ⟨.privateRow 11 10, 111117039760357230600⟩, ⟨.privateRow 11 11, 70350830204670615600⟩, ⟨.privateRow 12 5, 1647287651433867300⟩, ⟨.privateRow 12 6, 11235346545677146200⟩, ⟨.privateRow 12 7, 38436711866790237000⟩, ⟨.privateRow 12 8, 37039013253452410200⟩, ⟨.privateRow 13 3, 1229974779737287584⟩, ⟨.privateRow 13 4, 6589150605735469200⟩, ⟨.privateRow 13 5, 19868823364986953280⟩, ⟨.privateRow 14 2, 3997418034146184648⟩, ⟨.privateRow 14 3, 4282947893728054980⟩, ⟨.hall 5 24, 2996218563440032554624⟩, ⟨.hall 4 25, 12591866807560481641200⟩, ⟨.hall 3 26, 31588485620941850240640⟩, ⟨.hall 2 27, 66706913444814456313500⟩, ⟨.assumptionRow 17, 807038153096625450⟩]
  caps := #[0, 12932278267608155506050, 478123980242848299360, 270601945602270199632, 56607697691799368400, 224517826986931218312, 0, 79193775759528238380, 0, 8762218931480924910, 35268314181118390827, 896210039618462250, 23165263226695877100, 16382641473325835928, 0, 421236381810453709500, 98159863439356869150, 16125641238531374550] }

theorem case_47_30_17_checked :
    (Witness.linear .conditional case_47_30_17).check 47 30 17 = true := by
  change case_47_30_17.check 47 30 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_30_18 : Certificate := {
  objectiveScale := 1089564642753186600000
  eta := 19210220034899537134082592000
  rows := #[⟨.count 2, 2290789275634108914378714000⟩, ⟨.count 3, 307893864056288593636753200⟩, ⟨.count 4, 46089375412390431993471600⟩, ⟨.count 5, 6961163128671543996204000⟩, ⟨.count 6, 1011796966376677906425000⟩, ⟨.count 7, 103019327485625386836000⟩, ⟨.path 3, 26107070511760948969459200⟩, ⟨.path 7, 22366246774435468304400⟩, ⟨.path 8, 8459409932732598840000⟩, ⟨.privateRow 3 25, 38466272223938234718042000⟩, ⟨.privateRow 4 23, 24544170810365452654057650⟩, ⟨.privateRow 4 24, 19922956799267705762779200⟩, ⟨.privateRow 5 19, 374653962406907019064800⟩, ⟨.privateRow 5 20, 1805045788015993385062200⟩, ⟨.privateRow 5 21, 5785859772528394940100720⟩, ⟨.privateRow 5 22, 11081200375757376431166600⟩, ⟨.privateRow 5 23, 15908146436685047830084800⟩, ⟨.privateRow 6 17, 311970731299475687814375⟩, ⟨.privateRow 6 18, 879781552668482789110500⟩, ⟨.privateRow 6 19, 1971879865582992275410500⟩, ⟨.privateRow 6 20, 3719365648400667984018300⟩, ⟨.privateRow 6 21, 7490670207742005433899750⟩, ⟨.privateRow 6 22, 9297289902150140317927500⟩, ⟨.privateRow 6 23, 6647506069094773845212250⟩, ⟨.privateRow 7 15, 175786947693725858490000⟩, ⟨.privateRow 7 16, 363787000183614647264625⟩, ⟨.privateRow 7 17, 778952261906616445362000⟩, ⟨.privateRow 7 19, 5705799038025280353759600⟩, ⟨.privateRow 7 20, 2970084004027539054405750⟩, ⟨.privateRow 7 21, 4894644476132510938839000⟩, ⟨.privateRow 7 22, 2993079389627009006824500⟩, ⟨.privateRow 8 11, 214623598928386222575⟩, ⟨.privateRow 8 13, 79067333845217484396630⟩, ⟨.privateRow 8 15, 667694016266209538430825⟩, ⟨.privateRow 8 17, 1254260312137489084728300⟩, ⟨.privateRow 8 19, 6329249932398109703736750⟩, ⟨.privateRow 9 9, 176101414505342541600⟩, ⟨.privateRow 9 10, 953882661903938767000⟩, ⟨.privateRow 9 11, 30593618465428145181600⟩, ⟨.privateRow 9 12, 48533549837672404464960⟩, ⟨.privateRow 9 17, 3808967934901855969283040⟩, ⟨.privateRow 10 8, 990570456592551796500⟩, ⟨.privateRow 10 9, 12877415935703173354500⟩, ⟨.privateRow 10 15, 116325990619185332635650⟩, ⟨.privateRow 10 17, 2401638072008641830614250⟩, ⟨.privateRow 11 7, 6792483130920355176000⟩, ⟨.privateRow 11 8, 10117969663766779064250⟩, ⟨.privateRow 11 10, 1103778508774557716100⟩, ⟨.privateRow 11 16, 535332576755660492308500⟩, ⟨.hall 13 4, 110532441705015233475⟩, ⟨.hall 12 5, 98251059293346874200⟩, ⟨.hall 10 6, 25819380322211876400⟩, ⟨.hall 11 6, 83781900257737592625⟩, ⟨.hall 10 7, 23256427128462903375⟩, ⟨.hall 4 22, 16938361040594611351734⟩, ⟨.hall 5 22, 28189543306703269671180⟩, ⟨.hall 3 23, 28477212988480187950018⟩]
  caps := #[0, 1761563942772216224241600, 860229829700898194538000, 69377035092120107352000, 0, 0, 5410374368995018246395, 17436092528875885979400, 8459409932732598840000, 16296921416146587776000, 2515427603125385602500, 43897652755879121476200, 852584332954368514500, 442129766820060933900, 0, 991503824905399806000000, 297451147471619941800000, 70821701778957129000000] }

theorem case_47_30_18_checked :
    (Witness.linear .negative case_47_30_18).check 47 30 18 = true := by
  change case_47_30_18.check 47 30 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_30_19 : Certificate := {
  objectiveScale := 87352243731903150000
  eta := 1836800794952462577965126400
  rows := #[⟨.count 2, 189916131576874988771085600⟩, ⟨.count 3, 20786840272095769915243200⟩, ⟨.count 4, 2510618370525852730022880⟩, ⟨.count 5, 311491112968468080648000⟩, ⟨.count 6, 31149111296846808064800⟩, ⟨.count 7, 3303693622392843279600⟩, ⟨.path 3, 3120544414175877583614720⟩, ⟨.path 6, 3950026515529017580800⟩, ⟨.path 7, 2155695902886856249920⟩, ⟨.privateRow 5 19, 18096150372453859923360⟩, ⟨.privateRow 6 17, 7246494641974778265075⟩, ⟨.privateRow 7 14, 424760608593365564520⟩, ⟨.privateRow 7 15, 4142726923318009826800⟩, ⟨.privateRow 10 10, 60067156770778968720⟩, ⟨.hall 12 6, 2908413753206984880⟩, ⟨.hall 13 6, 3817293051084167655⟩, ⟨.hall 11 9, 2828665197957106200⟩, ⟨.hall 14 9, 2753078018660702733⟩, ⟨.hall 9 10, 2881117267852999560⟩, ⟨.hall 10 10, 2986191706573019700⟩, ⟨.hall 8 11, 2562658272056504160⟩, ⟨.hall 12 11, 2088091925379373760⟩, ⟨.hall 7 15, 8161298474290620750⟩, ⟨.hall 6 16, 7912877997855630800⟩]
  caps := #[0, 110582997111540015622560, 109658066935390518402000, 0, 1542385619221238391600, 1314359997982354614720, 3663386053621502720655, 0, 57455541259005970080, 0, 82328069942558338080, 564295494508094349000, 14542068766034924400, 2848537256487643520800, 0, 20438721664512564988575, 55643379257222306550000, 18169266696235855200000] }

theorem case_47_30_19_checked :
    (Witness.linear .negative case_47_30_19).check 47 30 19 = true := by
  change case_47_30_19.check 47 30 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_31_1_checked :
    (Witness.rising).check 47 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_31_2_checked :
    (Witness.rising).check 47 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_31_3_checked :
    (Witness.rising).check 47 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_31_4_checked :
    (Witness.rising).check 47 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_31_5_checked :
    (Witness.rising).check 47 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_31_6_checked :
    (Witness.rising).check 47 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_31_7_checked :
    (Witness.rising).check 47 31 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_31_8_checked :
    (Witness.rising).check 47 31 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_31_9_checked :
    (Witness.rising).check 47 31 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_31_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_31_10_checked :
    (Witness.linear .positive case_47_31_10).check 47 31 10 = true := by
  change case_47_31_10.check 47 31 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_47_31_11_checked :
    (Witness.linear .positive case_47_31_11).check 47 31 11 = true := by
  change case_47_31_11.check 47 31 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_47_31_12_checked :
    (Witness.linear .positive case_47_31_12).check 47 31 12 = true := by
  change case_47_31_12.check 47 31 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_31_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_47_31_13_checked :
    (Witness.linear .positive case_47_31_13).check 47 31 13 = true := by
  change case_47_31_13.check 47 31 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_31_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_47_31_14_checked :
    (Witness.linear .positive case_47_31_14).check 47 31 14 = true := by
  change case_47_31_14.check 47 31 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_31_15 : Certificate := {
  objectiveScale := 1020301410000
  eta := 38259236268778264740
  rows := #[⟨.count 2, 4808804218920750048⟩, ⟨.count 3, 577892012795012916⟩, ⟨.count 4, 69089962604779116⟩, ⟨.count 5, 8703192963780315⟩, ⟨.count 6, 1582398720687330⟩, ⟨.count 7, 426030424800435⟩, ⟨.count 8, 151477484373488⟩, ⟨.count 9, 85206084960087⟩, ⟨.path 5, 1392006702166080⟩, ⟨.path 6, 127099864801728⟩]
  caps := #[0, 4740767825651100, 624485803093152, 0, 36128233230804, 0, 3732160414398, 11678880089565, 0, 0, 14284219740000, 5101507050000, 2040602820000, 1020301410000, 1020301410000, 0, 0] }

theorem case_47_31_15_checked :
    (Witness.linear .positive case_47_31_15).check 47 31 15 = true := by
  change case_47_31_15.check 47 31 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_31_16 : Certificate := {
  objectiveScale := 634367037253950000
  eta := 10340596547994744284853600
  rows := #[⟨.count 2, 1544799581622572503868640⟩, ⟨.count 3, 229671226769851984637520⟩, ⟨.count 4, 33509272522578621088320⟩, ⟨.count 5, 4976624632066131844800⟩, ⟨.count 6, 678630631645381615200⟩, ⟨.count 7, 105564764922614917920⟩, ⟨.count 8, 46917673298939963520⟩, ⟨.path 6, 15130893846526698240⟩, ⟨.path 7, 30963535254051079680⟩, ⟨.privateRow 2 29, 130829931994094088275520⟩, ⟨.privateRow 3 25, 3234806010842985699120⟩, ⟨.privateRow 3 26, 27435947277149767596240⟩, ⟨.privateRow 3 27, 42951035366192976782760⟩, ⟨.privateRow 4 22, 539134335140497616520⟩, ⟨.privateRow 4 23, 5590408336687621438992⟩, ⟨.privateRow 4 24, 11384028845851276594980⟩, ⟨.privateRow 4 25, 16754636261289310544160⟩, ⟨.privateRow 4 26, 25131954391933965816240⟩, ⟨.privateRow 5 20, 975576415968519496560⟩, ⟨.privateRow 5 21, 2631159874916445632760⟩, ⟨.privateRow 5 22, 4390488842067231871968⟩, ⟨.privateRow 5 23, 6435052128407734371540⟩, ⟨.privateRow 5 24, 9999329121836579725200⟩, ⟨.privateRow 5 25, 9289699313190112776960⟩, ⟨.privateRow 6 17, 85177918786766005200⟩, ⟨.privateRow 6 18, 543532867012273238100⟩, ⟨.privateRow 6 19, 1118483818822943773200⟩, ⟨.privateRow 6 20, 1820154379320483406200⟩, ⟨.privateRow 6 21, 2591363634171809056560⟩, ⟨.privateRow 6 22, 4037223896594052664500⟩, ⟨.privateRow 6 23, 4117863647576605726800⟩, ⟨.privateRow 6 24, 1030513181387431341600⟩, ⟨.privateRow 7 15, 69371131234861231776⟩, ⟨.privateRow 7 16, 262236281117289438960⟩, ⟨.privateRow 7 17, 511800601365891968130⟩, ⟨.privateRow 7 18, 818665523889666710400⟩, ⟨.privateRow 7 19, 716332333403458371600⟩, ⟨.privateRow 7 20, 2673804688682803563888⟩, ⟨.privateRow 7 21, 674860461469573939560⟩, ⟨.privateRow 8 13, 41586119514969513120⟩, ⟨.privateRow 8 14, 133128897985742146488⟩, ⟨.privateRow 8 15, 260653740549666464000⟩, ⟨.privateRow 8 16, 416394350528092176240⟩, ⟨.privateRow 8 17, 589822178615245255680⟩, ⟨.privateRow 8 18, 621659171210954516640⟩, ⟨.privateRow 9 11, 23458836649469981760⟩, ⟨.privateRow 9 12, 75708063732380395680⟩, ⟨.privateRow 9 13, 152482438221554881440⟩, ⟨.privateRow 9 14, 248272687873557306960⟩, ⟨.privateRow 9 15, 213328795781117646630⟩, ⟨.privateRow 10 9, 13920628341443725440⟩, ⟨.privateRow 10 10, 49640573981467729260⟩, ⟨.privateRow 10 11, 105564764922614917920⟩, ⟨.privateRow 10 12, 67109029129376626392⟩, ⟨.privateRow 11 7, 9874255222353436200⟩, ⟨.privateRow 11 8, 38668412059565904000⟩, ⟨.privateRow 11 9, 26181737331997747500⟩, ⟨.privateRow 12 5, 7372777232690565696⟩, ⟨.privateRow 12 6, 13823957311294810680⟩, ⟨.privateRow 13 3, 5183983991735554005⟩, ⟨.hall 4 26, 3477493261419050153280⟩, ⟨.hall 3 27, 14364079071957543640140⟩, ⟨.hall 2 28, 38173189706499601353600⟩, ⟨.assumptionRow 16, 619220304302901840⟩]
  caps := #[0, 14481167842606746481200, 684518146947823502160, 0, 102581386473308613156, 32434610873105318592, 1539133204350661920, 7449325410751464240, 0, 12654344984037011640, 107245579920725831508, 1842514179957657360, 32954173457169328056, 0, 271408452054103481040, 56685867309867272400, 8261918217252398160] }

theorem case_47_31_16_checked :
    (Witness.linear .conditional case_47_31_16).check 47 31 16 = true := by
  change case_47_31_16.check 47 31 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_31_17 : Certificate := {
  objectiveScale := 986793169061700000
  eta := 18945180536837086244512800
  rows := #[⟨.count 2, 2631694401265815698772960⟩, ⟨.count 3, 356906929863009422136240⟩, ⟨.count 4, 45784946615008412972160⟩, ⟨.count 5, 5529582924517924272000⟩, ⟨.count 6, 603227228129228102400⟩, ⟨.count 7, 105564764922614917920⟩, ⟨.count 8, 46917673298939963520⟩, ⟨.path 6, 170590785490929323520⟩, ⟨.path 7, 16759241576603285760⟩, ⟨.privateRow 2 29, 233984301450975965569680⟩, ⟨.privateRow 3 25, 5121776183834727356940⟩, ⟨.privateRow 3 26, 46006129931989129943040⟩, ⟨.privateRow 3 27, 75658518364716498851640⟩, ⟨.privateRow 4 22, 787965566743804208760⟩, ⟨.privateRow 4 23, 8510028120833085454608⟩, ⟨.privateRow 4 24, 18703814242181878850040⟩, ⟨.privateRow 4 25, 29362085329190177884320⟩, ⟨.privateRow 4 26, 46863215285289408205200⟩, ⟨.privateRow 5 20, 1295502285172770829440⟩, ⟨.privateRow 5 21, 3893747976014705008200⟩, ⟨.privateRow 5 22, 7055747811684871371072⟩, ⟨.privateRow 5 23, 11176669486181854434780⟩, ⟨.privateRow 5 24, 18874309715687848181760⟩, ⟨.privateRow 5 25, 19712963125906400029680⟩, ⟨.privateRow 6 17, 83781559462392792000⟩, ⟨.privateRow 6 18, 689626961324820669150⟩, ⟨.privateRow 6 19, 1599629346021256664400⟩, ⟨.privateRow 6 20, 2854856638681034387400⟩, ⟨.privateRow 6 21, 4451314254236929038960⟩, ⟨.privateRow 6 22, 7637736414490382900700⟩, ⟨.privateRow 6 23, 8943681472610430546000⟩, ⟨.privateRow 6 24, 6208213556163305887200⟩, ⟨.privateRow 7 15, 59568688777761275112⟩, ⟨.privateRow 7 16, 317532110362468681680⟩, ⟨.privateRow 7 17, 701251652700227669040⟩, ⟨.privateRow 7 18, 1245233349495335154240⟩, ⟨.privateRow 7 19, 1946664534108696522120⟩, ⟨.privateRow 7 20, 2384255619180774074736⟩, ⟨.privateRow 7 21, 6132181790951184428460⟩, ⟨.privateRow 8 13, 30923011947028612320⟩, ⟨.privateRow 8 14, 150136554556607883264⟩, ⟨.privateRow 8 15, 339501497065940569360⟩, ⟨.privateRow 8 16, 606997398305035778040⟩, ⟨.privateRow 8 17, 676117184861509831440⟩, ⟨.privateRow 8 18, 2216860063374913276320⟩, ⟨.privateRow 8 19, 974714662785477742128⟩, ⟨.privateRow 9 11, 15150498669449363220⟩, ⟨.privateRow 9 12, 77307529867571530800⟩, ⟨.privateRow 9 13, 185324809530812855904⟩, ⟨.privateRow 9 14, 340804765768688901680⟩, ⟨.privateRow 9 15, 543951774809585202060⟩, ⟨.privateRow 9 16, 711305439835714804080⟩, ⟨.privateRow 10 9, 8120366532508839840⟩, ⟨.privateRow 10 10, 44613680413724161740⟩, ⟨.privateRow 10 11, 116532532706782701600⟩, ⟨.privateRow 10 12, 226210210548460538400⟩, ⟨.privateRow 10 13, 280668224199015853200⟩, ⟨.privateRow 11 7, 4488297828342471000⟩, ⟨.privateRow 11 8, 29968019346163575600⟩, ⟨.privateRow 11 9, 86923367942232521700⟩, ⟨.privateRow 11 10, 114247581085081080000⟩, ⟨.privateRow 12 5, 3686388616345282848⟩, ⟨.privateRow 12 6, 23698212533648246880⟩, ⟨.privateRow 12 7, 48915541255350868560⟩, ⟨.privateRow 13 3, 5183983991735554005⟩, ⟨.privateRow 13 4, 22118331698071697088⟩, ⟨.hall 4 26, 8994788223882490149120⟩, ⟨.hall 3 27, 29267292479055584896800⟩, ⟨.hall 2 28, 70967429954356077061920⟩, ⟨.assumptionRow 17, 668495983858212510⟩]
  caps := #[0, 0, 5030862122493354747600, 0, 0, 128300688931088178648, 36988525390065446340, 4081355445170659032, 0, 14413676399258553970, 90406709185371744060, 6052905956053517220, 339562777648107201408, 0, 1313886572186022394560, 364665412065893898960, 79452441441538024860] }

theorem case_47_31_17_checked :
    (Witness.linear .conditional case_47_31_17).check 47 31 17 = true := by
  change case_47_31_17.check 47 31 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_31_18 : Certificate := {
  objectiveScale := 1240539983963280000
  eta := 32984238623895644178693600
  rows := #[⟨.count 2, 4634398744867717511605920⟩, ⟨.count 3, 631865440784663206561440⟩, ⟨.count 4, 81284868990413486798400⟩, ⟨.count 5, 9400290971680471262400⟩, ⟨.count 6, 904840842193842153600⟩, ⟨.count 7, 52782382461307458960⟩, ⟨.path 6, 231516066023404081920⟩, ⟨.path 7, 49669403801439502080⟩, ⟨.privateRow 2 29, 425197278980805786895440⟩, ⟨.privateRow 3 25, 7817447859537215439540⟩, ⟨.privateRow 3 26, 80989957901105864170560⟩, ⟨.privateRow 3 27, 136041563900452231901880⟩, ⟨.privateRow 4 22, 1368571773818186257320⟩, ⟨.privateRow 4 23, 14465388930538889895552⟩, ⟨.privateRow 4 24, 32679835083900932447520⟩, ⟨.privateRow 4 25, 52420446124429922098560⟩, ⟨.privateRow 4 26, 85971190518942427618920⟩, ⟨.privateRow 5 19, 120959626473829593450⟩, ⟨.privateRow 5 20, 2203933765629286959840⟩, ⟨.privateRow 5 21, 6580203680176329883680⟩, ⟨.privateRow 5 22, 12137434519316843777040⟩, ⟨.privateRow 5 23, 19726787083217694840360⟩, ⟨.privateRow 5 24, 34495381477450984250160⟩, ⟨.privateRow 5 25, 37822347203702602020480⟩, ⟨.privateRow 6 17, 256930115684671228800⟩, ⟨.privateRow 6 18, 1159327329060860259300⟩, ⟨.privateRow 6 19, 2658867633510079820400⟩, ⟨.privateRow 6 20, 4815345130101025720200⟩, ⟨.privateRow 6 21, 7718795073270247926960⟩, ⟨.privateRow 6 22, 13798822843456092842400⟩, ⟨.privateRow 6 23, 17158463377898043801600⟩, ⟨.privateRow 6 24, 13905644331770643652200⟩, ⟨.privateRow 7 14, 15766166189741189040⟩, ⟨.privateRow 7 15, 160609249489406982264⟩, ⟨.privateRow 7 16, 534526349370066012960⟩, ⟨.privateRow 7 17, 1142361563269725718920⟩, ⟨.privateRow 7 18, 2054204150075782127280⟩, ⟨.privateRow 7 19, 3303925797399459752520⟩, ⟨.privateRow 7 20, 5462222550710160467232⟩, ⟨.privateRow 7 21, 8920222635960960564240⟩, ⟨.privateRow 7 22, 3941084557110956935680⟩, ⟨.privateRow 8 11, 451131474028268880⟩, ⟨.privateRow 8 12, 12218144088265615500⟩, ⟨.privateRow 8 13, 87970637435512431600⟩, ⟨.privateRow 8 14, 259806615892880047992⟩, ⟨.privateRow 8 15, 546721220802925408240⟩, ⟨.privateRow 8 16, 978673341470075801550⟩, ⟨.privateRow 8 17, 1580958027055351985040⟩, ⟨.privateRow 8 18, 2872730038033011516360⟩, ⟨.privateRow 8 19, 3819098606533713030528⟩, ⟨.privateRow 9 10, 8120366532508839840⟩, ⟨.privateRow 9 11, 50338753643654335860⟩, ⟨.privateRow 9 12, 142885641410408070720⟩, ⟨.privateRow 9 13, 301446050945689265616⟩, ⟨.privateRow 9 14, 541508145991932078960⟩, ⟨.privateRow 9 15, 395134779814510005270⟩, ⟨.privateRow 9 16, 2570418244306210858560⟩, ⟨.privateRow 10 8, 5924553133412061720⟩, ⟨.privateRow 10 9, 33061492310928847920⟩, ⟨.privateRow 10 10, 93625892699223945060⟩, ⟨.privateRow 10 11, 198790791088041079200⟩, ⟨.privateRow 10 12, 361182302842375326312⟩, ⟨.privateRow 10 13, 589822178615245255680⟩, ⟨.privateRow 10 14, 231865465812172051860⟩, ⟨.privateRow 11 6, 5026893567743567520⟩, ⟨.privateRow 11 7, 26032127404386331800⟩, ⟨.privateRow 11 8, 74436693214664365200⟩, ⟨.privateRow 11 9, 163374040951665944400⟩, ⟨.privateRow 11 10, 277621622036747024400⟩, ⟨.privateRow 12 4, 5183983991735554005⟩, ⟨.privateRow 12 5, 25804720314416979936⟩, ⟨.privateRow 12 6, 77019190734356802360⟩, ⟨.privateRow 12 7, 85070506531044988800⟩, ⟨.privateRow 13 2, 4879043756927580240⟩, ⟨.privateRow 13 3, 31103903950413324030⟩, ⟨.privateRow 13 4, 22118331698071697088⟩, ⟨.privateRow 14 0, 19967938338536948760⟩, ⟨.hall 5 25, 957043198474256124000⟩, ⟨.hall 4 26, 18542534740216772725440⟩, ⟨.hall 3 27, 55646365305572789705100⟩, ⟨.hall 2 28, 130135873999430459160000⟩, ⟨.assumptionRow 18, 210779020911579120⟩]
  caps := #[0, 19205991060150970595520, 0, 2603795517304845743880, 97616388843043270200, 5571288256396957380, 70826880389931043620, 78868909382384605536, 210779020911579120, 30730162369800491808, 1560687290174319120, 29858302366717320000, 0, 1153995482570967972936, 0, 1470337610592637987200, 415218882505105879200] }

theorem case_47_31_18_checked :
    (Witness.linear .conditional case_47_31_18).check 47 31 18 = true := by
  change case_47_31_18.check 47 31 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_31_19 : Certificate := {
  objectiveScale := 20565981166500000
  eta := 694057994663629115520000
  rows := #[⟨.count 2, 93553233864035007862800⟩, ⟨.count 3, 11929121783281125423000⟩, ⟨.count 4, 1382395731129481068000⟩, ⟨.count 5, 131089250365726653000⟩, ⟨.count 6, 8667057875419944000⟩, ⟨.path 6, 8288054456672390400⟩, ⟨.path 7, 20976583736908800⟩, ⟨.privateRow 7 14, 19697858807772600⟩, ⟨.privateRow 7 15, 86670578754199440⟩, ⟨.privateRow 8 12, 28087687559231300⟩, ⟨.privateRow 8 13, 137885011654408200⟩, ⟨.privateRow 9 10, 12963548104260600⟩, ⟨.privateRow 9 11, 70219218898078250⟩, ⟨.privateRow 9 12, 61282227401959200⟩, ⟨.privateRow 9 13, 84263062677693900⟩, ⟨.hall 11 6, 922384255317525⟩, ⟨.hall 13 6, 556358757175650⟩, ⟨.hall 10 7, 1009343040330625⟩, ⟨.hall 11 7, 614922836878350⟩, ⟨.hall 12 7, 756828106927200⟩, ⟨.hall 9 8, 1122107127130080⟩, ⟨.hall 10 8, 303468413004900⟩, ⟨.hall 8 10, 635766430462800⟩, ⟨.hall 7 12, 538579421942100⟩, ⟨.hall 6 14, 643797474436116⟩, ⟨.hall 5 18, 4656325099560750⟩, ⟨.hall 4 21, 56438403630722960⟩, ⟨.hall 3 23, 177370880845978391⟩]
  caps := #[0, 563803018074904608000, 47556973392007741200, 0, 0, 1897948948144649400, 0, 852084804900138768, 5086131443702400, 7854749889910560, 331152408942264000, 41004387960938600, 0, 0, 30865347755020178400, 52402120012242000000, 18715042861515000000] }

theorem case_47_31_19_checked :
    (Witness.linear .negative case_47_31_19).check 47 31 19 = true := by
  change case_47_31_19.check 47 31 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_31_20 : Certificate := {
  objectiveScale := 122004041544000
  eta := 4020875149266505530000
  rows := #[⟨.count 2, 480360551165705193984⟩, ⟨.count 3, 51926730499098871416⟩, ⟨.count 4, 4736679296718344976⟩, ⟨.count 5, 324026568805359420⟩, ⟨.count 6, 16067433163902120⟩, ⟨.path 5, 178226045393235840⟩, ⟨.path 6, 8531254190467008⟩, ⟨.hall 13 8, 1750265050534⟩, ⟨.hall 9 10, 1560412965816⟩, ⟨.hall 11 10, 2997417475206⟩, ⟨.hall 12 10, 3443841354492⟩, ⟨.hall 10 11, 2604139295835⟩, ⟨.hall 13 12, 4125624761973⟩]
  caps := #[0, 3429660173780720880, 439291735386489216, 62682168878755272, 11100807170882352, 0, 0, 0, 0, 10922890760712, 7303378710864600, 6830599605910080, 0, 0, 0, 444094711220160000, 199842620049072000] }

theorem case_47_31_20_checked :
    (Witness.linear .negative case_47_31_20).check 47 31 20 = true := by
  change case_47_31_20.check 47 31 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_32_1_checked :
    (Witness.rising).check 47 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_32_2_checked :
    (Witness.rising).check 47 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_32_3_checked :
    (Witness.rising).check 47 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_32_4_checked :
    (Witness.rising).check 47 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_32_5_checked :
    (Witness.rising).check 47 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_32_6_checked :
    (Witness.rising).check 47 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_32_7_checked :
    (Witness.rising).check 47 32 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_32_8_checked :
    (Witness.rising).check 47 32 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_32_9_checked :
    (Witness.rising).check 47 32 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_32_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_47_32_10_checked :
    (Witness.linear .positive case_47_32_10).check 47 32 10 = true := by
  change case_47_32_10.check 47 32 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_47_32_11_checked :
    (Witness.linear .positive case_47_32_11).check 47 32 11 = true := by
  change case_47_32_11.check 47 32 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_47_32_12_checked :
    (Witness.linear .positive case_47_32_12).check 47 32 12 = true := by
  change case_47_32_12.check 47 32 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_32_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_47_32_13_checked :
    (Witness.linear .positive case_47_32_13).check 47 32 13 = true := by
  change case_47_32_13.check 47 32 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_32_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_47_32_14_checked :
    (Witness.linear .positive case_47_32_14).check 47 32 14 = true := by
  change case_47_32_14.check 47 32 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_32_15 : Certificate := {
  objectiveScale := 13
  eta := 9152528
  rows := #[⟨.assumptionRow 15, 33⟩]
  caps := #[0, 0, 2615008, 764218, 226746, 68510, 21164, 6721, 2211, 762, 280, 33117, 16815, 5358, 1194, 175] }

theorem case_47_32_15_checked :
    (Witness.linear .conditional case_47_32_15).check 47 32 15 = true := by
  change case_47_32_15.check 47 32 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_32_16 : Certificate := {
  objectiveScale := 866711260800000
  eta := 24809649838864672541760
  rows := #[⟨.count 2, 3177962093992652366400⟩, ⟨.count 3, 410193282014696980800⟩, ⟨.count 4, 50549071116962658240⟩, ⟨.count 5, 5650045206814008000⟩, ⟨.count 6, 678005424817680960⟩, ⟨.count 7, 175779184211991360⟩, ⟨.path 6, 279944008617873600⟩, ⟨.privateRow 2 29, 142738975408144555440⟩, ⟨.privateRow 2 30, 344728091551745341440⟩, ⟨.privateRow 3 26, 44541189713717096400⟩, ⟨.privateRow 3 27, 87286920617268852480⟩, ⟨.privateRow 3 28, 106898855312921031360⟩, ⟨.privateRow 4 22, 1006246146356399520⟩, ⟨.privateRow 4 23, 8114092699785672600⟩, ⟨.privateRow 4 24, 22374179018983471680⟩, ⟨.privateRow 4 25, 31541377367039199660⟩, ⟨.privateRow 4 26, 41571777066135956640⟩, ⟨.privateRow 4 27, 55728279223208832240⟩, ⟨.privateRow 5 19, 226001808272560320⟩, ⟨.privateRow 5 20, 1478428495782998760⟩, ⟨.privateRow 5 21, 4875181864165229760⟩, ⟨.privateRow 5 22, 8814070522629852480⟩, ⟨.privateRow 5 23, 12369832306118134848⟩, ⟨.privateRow 5 24, 15876627031147362480⟩, ⟨.privateRow 5 25, 22273733770862333760⟩, ⟨.privateRow 5 26, 16008461419306356000⟩, ⟨.privateRow 6 16, 6848539644623040⟩, ⟨.privateRow 6 17, 237301898686188336⟩, ⟨.privateRow 6 18, 1012822918554807360⟩, ⟨.privateRow 6 19, 2316518534793743280⟩, ⟨.privateRow 6 20, 3750553818237489120⟩, ⟨.privateRow 6 21, 5298486838390025280⟩, ⟨.privateRow 6 22, 6697186918476870816⟩, ⟨.privateRow 6 23, 9284907623197686480⟩, ⟨.privateRow 6 24, 1770347498135055840⟩, ⟨.privateRow 7 15, 184910570404822080⟩, ⟨.privateRow 7 16, 587604701508656832⟩, ⟨.privateRow 7 17, 1166280936517656960⟩, ⟨.privateRow 7 18, 1833125778210767040⟩, ⟨.privateRow 7 19, 2554179166508935680⟩, ⟨.privateRow 7 20, 3239359251906697920⟩, ⟨.privateRow 7 21, 1361033112041418816⟩, ⟨.privateRow 8 13, 130003354990118610⟩, ⟨.privateRow 8 14, 363543312802073040⟩, ⟨.privateRow 8 15, 678947099018816628⟩, ⟨.privateRow 8 16, 1054675105271948160⟩, ⟨.privateRow 8 17, 1463911018515490545⟩, ⟨.privateRow 8 18, 56500452068140080⟩, ⟨.privateRow 9 11, 96581969347248000⟩, ⟨.privateRow 9 12, 261576166982130000⟩, ⟨.privateRow 9 13, 479397775123612800⟩, ⟨.privateRow 9 14, 426892304514836160⟩, ⟨.privateRow 10 9, 80714931525914400⟩, ⟨.privateRow 10 10, 228899267352977760⟩, ⟨.privateRow 10 11, 97306334117352360⟩, ⟨.privateRow 11 7, 80356198496910336⟩, ⟨.privateRow 11 8, 43047963480487680⟩, ⟨.privateRow 12 5, 38844060796846305⟩, ⟨.hall 4 27, 59190949785670560⟩, ⟨.hall 3 28, 21002581837743105600⟩, ⟨.hall 2 29, 76845637075076565696⟩, ⟨.assumptionRow 16, 893540789384320⟩]
  caps := #[0, 32469571340330826240, 0, 1500542384789788560, 0, 62869983623183840, 12817746456370960, 0, 83816137796537601, 19488753848847360, 7309303486580480, 391594894102463040, 893540789384320, 1806484085216912640, 454001559343516800, 88841987405050880] }

theorem case_47_32_16_checked :
    (Witness.linear .conditional case_47_32_16).check 47 32 16 = true := by
  change case_47_32_16.check 47 32 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_32_17 : Certificate := {
  objectiveScale := 1927869192960480000
  eta := 52308972384627051827173440
  rows := #[⟨.count 2, 6531965333404396020495360⟩, ⟨.count 3, 802841892985322922251520⟩, ⟨.count 4, 91480283724518088079680⟩, ⟨.count 5, 10550643306084175694400⟩, ⟨.count 6, 372375646097088553920⟩, ⟨.count 7, 289625502519957764160⟩, ⟨.path 5, 815301523343261354400⟩, ⟨.path 6, 417018653257232426400⟩, ⟨.privateRow 2 29, 417122786236422028482720⟩, ⟨.privateRow 2 30, 878620336966080442974240⟩, ⟨.privateRow 3 26, 98989859254142707250400⟩, ⟨.privateRow 3 27, 213909121146883091529600⟩, ⟨.privateRow 3 28, 272392785120020277192480⟩, ⟨.privateRow 4 22, 828979116906613804560⟩, ⟨.privateRow 4 23, 15986293362306954446760⟩, ⟨.privateRow 4 24, 49017047547913423314336⟩, ⟨.privateRow 4 25, 75693107895193604595780⟩, ⟨.privateRow 4 26, 107523467810534319944400⟩, ⟨.privateRow 4 27, 155311675726327351030800⟩, ⟨.privateRow 5 20, 2280800832344667392760⟩, ⟨.privateRow 5 21, 9433516367792910032640⟩, ⟨.privateRow 5 22, 19177345774000060526880⟩, ⟨.privateRow 5 23, 29442501084743134996608⟩, ⟨.privateRow 5 24, 41426790628301101623600⟩, ⟨.privateRow 5 25, 64089986200487796669120⟩, ⟨.privateRow 5 26, 55421908660783346441760⟩, ⟨.privateRow 6 15, 46546955762136069240⟩, ⟨.privateRow 6 17, 68268868451132901552⟩, ⟨.privateRow 6 18, 1565356882667390772960⟩, ⟨.privateRow 6 19, 4421960797402926577800⟩, ⟨.privateRow 6 20, 8014942477899239351040⟩, ⟨.privateRow 6 21, 12474584144252466556320⟩, ⟨.privateRow 6 22, 17439592758880313941920⟩, ⟨.privateRow 6 23, 27105843905483904320760⟩, ⟨.privateRow 6 24, 22445976445296726722400⟩, ⟨.privateRow 7 15, 90272883902324497920⟩, ⟨.privateRow 7 16, 893701550633012529408⟩, ⟨.privateRow 7 17, 2151503733005400533760⟩, ⟨.privateRow 7 18, 3806506604548016328960⟩, ⟨.privateRow 7 19, 5892992367599956956480⟩, ⟨.privateRow 7 20, 8281910203011173208480⟩, ⟨.privateRow 7 21, 12925572426747829360512⟩, ⟨.privateRow 7 22, 2110128661216835138880⟩, ⟨.privateRow 8 13, 54304781722492080780⟩, ⟨.privateRow 8 14, 516718226086742829240⟩, ⟨.privateRow 8 15, 1191084879113326305108⟩, ⟨.privateRow 8 16, 2103807469693582092440⟩, ⟨.privateRow 8 17, 3244710707918901826605⟩, ⟨.privateRow 8 18, 4571945432636476134240⟩, ⟨.privateRow 8 19, 1918768954194720187560⟩, ⟨.privateRow 9 11, 35009676128786103360⟩, ⟨.privateRow 9 12, 327552651659476042800⟩, ⟨.privateRow 9 13, 786126363982742502720⟩, ⟨.privateRow 9 14, 1228839632120392227936⟩, ⟨.privateRow 9 15, 2510087688506300622720⟩, ⟨.privateRow 10 9, 26598260435506325280⟩, ⟨.privateRow 10 10, 243476383986557900640⟩, ⟨.privateRow 10 11, 630969844775622271920⟩, ⟨.privateRow 10 12, 835024176096501605760⟩, ⟨.privateRow 11 7, 24825043073139236928⟩, ⟨.privateRow 11 8, 212786083484050602240⟩, ⟨.privateRow 11 9, 353279459117750679360⟩, ⟨.privateRow 12 5, 21334021390979031735⟩, ⟨.privateRow 12 6, 159294026385976770288⟩, ⟨.privateRow 13 3, 80316315824862237120⟩, ⟨.hall 4 27, 9167533763437846779840⟩, ⟨.hall 3 28, 67515556799258331603840⟩, ⟨.hall 2 29, 208265561354922771667968⟩, ⟨.assumptionRow 17, 1464894976399155840⟩]
  caps := #[0, 29105086612541989119840, 4351264425006173912160, 1358647926358660082112, 0, 94879387075559100960, 945782219507529466920, 0, 79498087082896255620, 701678781563003901888, 6936728365424315040, 1464894976399155840, 2534194174121015951853, 0, 3354913099650676798080, 874438338779001575040] }

theorem case_47_32_17_checked :
    (Witness.linear .conditional case_47_32_17).check 47 32 17 = true := by
  change case_47_32_17.check 47 32 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_32_18 : Certificate := {
  objectiveScale := 788707247328000
  eta := 23577965095091249082240
  rows := #[⟨.count 2, 3073825483003062627840⟩, ⟨.count 3, 391133796183711060480⟩, ⟨.count 4, 45300806902633201920⟩, ⟨.count 5, 4394479605299784000⟩, ⟨.count 6, 301335744363413760⟩, ⟨.path 6, 275773520593771200⟩, ⟨.privateRow 2 29, 237898292346907592400⟩, ⟨.privateRow 2 30, 474001125883649844480⟩, ⟨.privateRow 3 26, 49789453928046552720⟩, ⟨.privateRow 3 27, 112607493581139036480⟩, ⟨.privateRow 3 28, 145984612488058824480⟩, ⟨.privateRow 4 22, 355145698714023360⟩, ⟨.privateRow 4 23, 7688246699938764960⟩, ⟨.privateRow 4 24, 24404428596631971888⟩, ⟨.privateRow 4 25, 39137549256200254860⟩, ⟨.privateRow 4 26, 57638831546846309760⟩, ⟨.privateRow 4 27, 86527303428352746960⟩, ⟨.privateRow 5 19, 75333936090853440⟩, ⟨.privateRow 5 20, 1067230761287090400⟩, ⟨.privateRow 5 21, 4480575532260759360⟩, ⟨.privateRow 5 22, 9400001136669823680⟩, ⟨.privateRow 5 23, 14956297445237436288⟩, ⟨.privateRow 5 24, 22003787166536775600⟩, ⟨.privateRow 5 25, 35900805765963378240⟩, ⟨.privateRow 5 26, 33887715584868905760⟩, ⟨.privateRow 6 16, 7989962918726880⟩, ⟨.privateRow 6 17, 121789863346879728⟩, ⟨.privateRow 6 18, 717067465753679040⟩, ⟨.privateRow 6 19, 2055988672479541800⟩, ⟨.privateRow 6 20, 3845618070923566080⟩, ⟨.privateRow 6 21, 6217142336831265840⟩, ⟨.privateRow 6 22, 9122939660602351584⟩, ⟨.privateRow 6 23, 13509885872293050240⟩, ⟨.privateRow 6 24, 19733306037131887200⟩, ⟨.privateRow 7 13, 643879795648320⟩, ⟨.privateRow 7 14, 7672900898142480⟩, ⟨.privateRow 7 15, 92835759627112320⟩, ⟨.privateRow 7 16, 400106905015866048⟩, ⟨.privateRow 7 17, 977481071993666240⟩, ⟨.privateRow 7 18, 1779764240146412520⟩, ⟨.privateRow 7 19, 2867472678505818240⟩, ⟨.privateRow 7 20, 3323063625340979520⟩, ⟨.privateRow 7 21, 8886056283783334656⟩, ⟨.privateRow 7 22, 4109884735623226560⟩, ⟨.privateRow 8 12, 6197343033115080⟩, ⟨.privateRow 8 13, 63475816520996880⟩, ⟨.privateRow 8 14, 233706415372761240⟩, ⟨.privateRow 8 15, 530267205706173936⟩, ⟨.privateRow 8 16, 958647587970952880⟩, ⟨.privateRow 8 17, 1537152345270486945⟩, ⟨.privateRow 8 18, 2271527434072816920⟩, ⟨.privateRow 8 19, 3142052917789345560⟩, ⟨.privateRow 9 10, 5380995435060960⟩, ⟨.privateRow 9 11, 47003225082327360⟩, ⟨.privateRow 9 12, 157643236634563680⟩, ⟨.privateRow 9 13, 346231726478164800⟩, ⟨.privateRow 9 14, 624434625819740736⟩, ⟨.privateRow 9 15, 999802238242808000⟩, ⟨.privateRow 9 16, 1134194260034515680⟩, ⟨.privateRow 10 8, 5022262406056896⟩, ⟨.privateRow 10 9, 41254298335467360⟩, ⟨.privateRow 10 10, 130385658618784800⟩, ⟨.privateRow 10 11, 198797886906418800⟩, ⟨.privateRow 10 12, 681429694639992480⟩, ⟨.privateRow 10 13, 168245790602906016⟩, ⟨.privateRow 11 6, 6277828007571120⟩, ⟨.privateRow 11 7, 43526274185826432⟩, ⟨.privateRow 11 8, 136318551021544320⟩, ⟨.privateRow 11 9, 251113120302844800⟩, ⟨.privateRow 12 4, 8124248009797920⟩, ⟨.privateRow 12 5, 60424094572872030⟩, ⟨.privateRow 12 6, 82867329699938784⟩, ⟨.privateRow 13 2, 15345801796284960⟩, ⟨.privateRow 13 3, 32496992039191680⟩, ⟨.hall 4 27, 7744149263625231600⟩, ⟨.hall 3 28, 40233517316384071680⟩, ⟨.hall 2 29, 115268455612614848544⟩, ⟨.assumptionRow 18, 279683390303856⟩]
  caps := #[0, 0, 1480346595887765760, 0, 102903065610927516, 23266607159093760, 0, 37202733500122704, 14694484504535759, 50328357856737472, 1535248991818080, 13336310276698464, 42676169654477898, 0, 3716589990440771136, 1188654556132302336] }

theorem case_47_32_18_checked :
    (Witness.linear .conditional case_47_32_18).check 47 32 18 = true := by
  change case_47_32_18.check 47 32 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_32_19 : Certificate := {
  objectiveScale := 4862174507819200000
  eta := 175191570219297251962742400
  rows := #[⟨.count 2, 23163627065469393496593600⟩, ⟨.count 3, 2908253796018261606115200⟩, ⟨.count 4, 331104011987994572527200⟩, ⟨.count 5, 31031303841424046160000⟩, ⟨.count 6, 1861878230485442769600⟩, ⟨.path 5, 544758525356983938000⟩, ⟨.path 6, 1961619669157990842000⟩, ⟨.privateRow 4 22, 121908693662737324200⟩, ⟨.privateRow 4 23, 56748496900004224415100⟩, ⟨.privateRow 5 20, 6710519455707949982100⟩, ⟨.privateRow 5 21, 32361216863199362424000⟩, ⟨.privateRow 5 22, 37754753007065922828000⟩, ⟨.privateRow 5 23, 18991157950951516249920⟩, ⟨.privateRow 6 16, 14105138109738202800⟩, ⟨.privateRow 6 17, 605110424907768900120⟩, ⟨.privateRow 6 18, 4499539057006486693200⟩, ⟨.privateRow 6 19, 14429556286262181464400⟩, ⟨.privateRow 6 21, 72897704607478655104200⟩, ⟨.privateRow 6 22, 18680844912537275788320⟩, ⟨.privateRow 7 13, 7956744574724114400⟩, ⟨.privateRow 7 14, 43099033113088953000⟩, ⟨.privateRow 7 15, 479574695731098895200⟩, ⟨.privateRow 7 17, 11539047798811015683200⟩, ⟨.privateRow 7 19, 22460753256649785792000⟩, ⟨.privateRow 7 22, 180317734738541561561400⟩, ⟨.privateRow 8 11, 6464854966963342950⟩, ⟨.privateRow 8 12, 34810757514418000500⟩, ⟨.privateRow 8 13, 324320224175994371325⟩, ⟨.privateRow 8 14, 148103950152251129400⟩, ⟨.privateRow 8 15, 18101593907497360260⟩, ⟨.privateRow 9 10, 14776811353059069600⟩, ⟨.privateRow 9 11, 198918614368102860000⟩, ⟨.privateRow 9 12, 112057486094031277800⟩, ⟨.privateRow 9 15, 229861509936474416000⟩, ⟨.privateRow 9 21, 49615606919788002693600⟩, ⟨.privateRow 10 10, 11935116862086171600⟩, ⟨.privateRow 11 18, 1241252153656961846400⟩, ⟨.hall 10 6, 220425274897869600⟩, ⟨.hall 11 6, 597591635601653550⟩, ⟨.hall 10 7, 311142752420695650⟩, ⟨.hall 12 7, 176132271545750520⟩, ⟨.hall 8 8, 170879314830588000⟩, ⟨.hall 9 8, 342707959188012600⟩, ⟨.hall 8 9, 36865629958821300⟩, ⟨.hall 7 12, 151104780786581622⟩, ⟨.hall 6 13, 19443172832972460⟩, ⟨.hall 5 17, 186656035616751120⟩, ⟨.hall 4 21, 4776929623303571580⟩, ⟨.hall 3 24, 138038151593499493248⟩, ⟨.hall 2 28, 148170909026266323397200⟩]
  caps := #[0, 0, 0, 10437623226108754275600, 2313522919866157728300, 393703241647594450000, 941600607619458430400, 235456171188447580, 11153593500009310350, 1223980966028493233000, 617108965096175336400, 0, 0, 0, 48602296380160723200000, 18515160525775513600000] }

theorem case_47_32_19_checked :
    (Witness.linear .negative case_47_32_19).check 47 32 19 = true := by
  change case_47_32_19.check 47 32 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_32_20 : Certificate := {
  objectiveScale := 622
  eta := 2734424
  rows := #[⟨.assumptionRow 20, 245⟩]
  caps := #[0, 0, 1067605, 623770, 306945, 137394, 78132, 35020, 18991, 10530, 4560, 14407092, 14247530, 9972948, 5798700, 2915976] }

theorem case_47_32_20_checked :
    (Witness.linear .conditional case_47_32_20).check 47 32 20 = true := by
  change case_47_32_20.check 47 32 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_33_1_checked :
    (Witness.rising).check 47 33 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_33_2_checked :
    (Witness.rising).check 47 33 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_33_3_checked :
    (Witness.rising).check 47 33 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_33_4_checked :
    (Witness.rising).check 47 33 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_33_5_checked :
    (Witness.rising).check 47 33 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_33_6_checked :
    (Witness.rising).check 47 33 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_33_7_checked :
    (Witness.rising).check 47 33 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_33_8_checked :
    (Witness.rising).check 47 33 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_33_9_checked :
    (Witness.rising).check 47 33 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_33_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_47_33_10_checked :
    (Witness.linear .positive case_47_33_10).check 47 33 10 = true := by
  change case_47_33_10.check 47 33 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_33_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_47_33_11_checked :
    (Witness.linear .positive case_47_33_11).check 47 33 11 = true := by
  change case_47_33_11.check 47 33 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_33_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_47_33_12_checked :
    (Witness.linear .positive case_47_33_12).check 47 33 12 = true := by
  change case_47_33_12.check 47 33 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_33_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_47_33_13_checked :
    (Witness.linear .positive case_47_33_13).check 47 33 13 = true := by
  change case_47_33_13.check 47 33 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_33_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_47_33_14_checked :
    (Witness.linear .positive case_47_33_14).check 47 33 14 = true := by
  change case_47_33_14.check 47 33 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_33_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_47_33_15_checked :
    (Witness.linear .positive case_47_33_15).check 47 33 15 = true := by
  change case_47_33_15.check 47 33 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_33_16 : Certificate := {
  objectiveScale := 909
  eta := 1036754095
  rows := #[⟨.assumptionRow 16, 1673⟩]
  caps := #[0, 0, 300607056, 88171248, 26208220, 7912242, 2432976, 764764, 246906, 82395, 18497336, 12066824, 5269061, 1778495, 471086] }

theorem case_47_33_16_checked :
    (Witness.linear .conditional case_47_33_16).check 47 33 16 = true := by
  change case_47_33_16.check 47 33 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_33_17 : Certificate := {
  objectiveScale := 715284135508800000
  eta := 42008063640225459668892000
  rows := #[⟨.count 2, 4452136659305946152942400⟩, ⟨.count 3, 428090063394802514706000⟩, ⟨.count 4, 36155407113695930860800⟩, ⟨.count 5, 2510792160673328532000⟩, ⟨.count 6, 334772288089777137600⟩, ⟨.path 4, 2544284922357290112000⟩, ⟨.path 5, 1614863561058824076000⟩, ⟨.privateRow 2 30, 389423864120433255313200⟩, ⟨.privateRow 2 31, 585516731869020213662400⟩, ⟨.privateRow 3 26, 28907587076552255831760⟩, ⟨.privateRow 3 27, 77562554496800240567700⟩, ⟨.privateRow 3 28, 161416038240620876512800⟩, ⟨.privateRow 3 29, 185505694137747756372600⟩, ⟨.privateRow 3 30, 260536533205869057337200⟩, ⟨.privateRow 4 23, 9002983318985792307600⟩, ⟨.privateRow 4 24, 16027223292298080462600⟩, ⟨.privateRow 4 25, 38766630960796192534080⟩, ⟨.privateRow 4 26, 54798038906695395210900⟩, ⟨.privateRow 4 27, 70971725075032753171200⟩, ⟨.privateRow 4 28, 93401468377047821390400⟩, ⟨.privateRow 5 20, 1696179592988204163840⟩, ⟨.privateRow 5 21, 3803850123420092725980⟩, ⟨.privateRow 5 22, 9010157010873430389120⟩, ⟨.privateRow 5 23, 15466479709747703757120⟩, ⟨.privateRow 5 24, 21753503280073718401248⟩, ⟨.privateRow 5 25, 27970224669900879846480⟩, ⟨.privateRow 5 26, 39034448791268014244160⟩, ⟨.privateRow 5 27, 15064752964039971192000⟩, ⟨.privateRow 6 17, 213036910602585451200⟩, ⟨.privateRow 6 18, 809033029550294749200⟩, ⟨.privateRow 6 19, 2318608069362530545600⟩, ⟨.privateRow 6 20, 4338090899830028741400⟩, ⟨.privateRow 6 21, 6886744212132558259200⟩, ⟨.privateRow 6 22, 9745593275502401116800⟩, ⟨.privateRow 6 23, 12464688193209368756640⟩, ⟨.privateRow 6 24, 14227822243815528348000⟩, ⟨.privateRow 7 13, 2989038286515867300⟩, ⟨.privateRow 7 14, 3218964308555549400⟩, ⟨.privateRow 7 15, 122052396699397914750⟩, ⟨.privateRow 7 16, 578243043064160510400⟩, ⟨.privateRow 7 17, 1360012420364719621500⟩, ⟨.privateRow 7 18, 2352705246853155994800⟩, ⟨.privateRow 7 19, 3604032913966506996975⟩, ⟨.privateRow 7 20, 5051474704211815737000⟩, ⟨.privateRow 7 21, 5781796392217192647300⟩, ⟨.privateRow 8 13, 106225822182333130200⟩, ⟨.privateRow 8 14, 432414205449295469400⟩, ⟨.privateRow 8 15, 924428022793361868600⟩, ⟨.privateRow 8 16, 1539952525212974832960⟩, ⟨.privateRow 8 17, 2306209095729575836800⟩, ⟨.privateRow 8 18, 1506475296403997119200⟩, ⟨.privateRow 9 11, 103619993932550066400⟩, ⟨.privateRow 9 12, 386275717026665928000⟩, ⟨.privateRow 9 13, 781135338876146654400⟩, ⟨.privateRow 9 14, 1115907626965923792000⟩, ⟨.privateRow 10 9, 120518023712319769536⟩, ⟨.privateRow 10 10, 430421513258284891200⟩, ⟨.privateRow 10 11, 270393001918666149600⟩, ⟨.privateRow 11 7, 188309412050499639900⟩, ⟨.privateRow 11 8, 83693072022444284400⟩, ⟨.privateRow 12 5, 108308681440810250400⟩, ⟨.hall 3 29, 20437848187880894250480⟩, ⟨.assumptionRow 17, 596355492953449152⟩]
  caps := #[0, 42300069679727501146560, 0, 2172441077647825891500, 0, 363838955022401943696, 93769250919614945480, 50954927465701935852, 316969975522720862520, 10379325225672727104, 334061050261601054304, 1118429748814639655592, 0, 5414716498995770091840, 1603439298547229176704] }

theorem case_47_33_17_checked :
    (Witness.linear .conditional case_47_33_17).check 47 33 17 = true := by
  change case_47_33_17.check 47 33 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_33_18 : Certificate := {
  objectiveScale := 417249079046800000
  eta := 28101120634543982707281600
  rows := #[⟨.count 2, 2964408611034976553448000⟩, ⟨.count 3, 278949009050806799905200⟩, ⟨.count 4, 22429743302015068219200⟩, ⟨.count 5, 1171703008314219981600⟩, ⟨.path 4, 1703257406355852547200⟩, ⟨.path 5, 1086740799888513369600⟩, ⟨.privateRow 2 30, 273425266297325477134800⟩, ⟨.privateRow 2 31, 425328192018061853320800⟩, ⟨.privateRow 3 26, 17614601891657107056720⟩, ⟨.privateRow 3 27, 51861806963241308233200⟩, ⟨.privateRow 3 28, 113236726446367116793200⟩, ⟨.privateRow 3 29, 136252321252539295003200⟩, ⟨.privateRow 3 30, 199468488320158877820000⟩, ⟨.privateRow 4 23, 5440049681458878486000⟩, ⟨.privateRow 4 24, 10001322106682091985800⟩, ⟨.privateRow 4 25, 25727250339699373024560⟩, ⟨.privateRow 4 26, 38373273522290704397400⟩, ⟨.privateRow 4 27, 52308170014027677750000⟩, ⟨.privateRow 4 28, 73105898411605082423400⟩, ⟨.privateRow 5 19, 56911288975262113392⟩, ⟨.privateRow 5 20, 993157787999672174880⟩, ⟨.privateRow 5 21, 2242974330201506821920⟩, ⟨.privateRow 5 22, 5562002443548725871840⟩, ⟨.privateRow 5 23, 10160338943524736126160⟩, ⟨.privateRow 5 24, 15091534747087153363008⟩, ⟨.privateRow 5 25, 20647080867937004961480⟩, ⟨.privateRow 5 26, 31022232029652681417600⟩, ⟨.privateRow 5 27, 19969166984555206257840⟩, ⟨.privateRow 6 16, 12398973632954708800⟩, ⟨.privateRow 6 17, 158932298386055812800⟩, ⟨.privateRow 6 18, 455662281011085548400⟩, ⟨.privateRow 6 19, 1339089152359108550400⟩, ⟨.privateRow 6 20, 2636331768706994958600⟩, ⟨.privateRow 6 21, 4437061278650220792000⟩, ⟨.privateRow 6 22, 6658248840896678625600⟩, ⟨.privateRow 6 23, 9102086543952051730080⟩, ⟨.privateRow 6 24, 13944195721961689384200⟩, ⟨.privateRow 6 25, 3502710051309705236000⟩, ⟨.privateRow 7 13, 996346095505289100⟩, ⟨.privateRow 7 14, 24678726365592545400⟩, ⟨.privateRow 7 15, 86017879578623292300⟩, ⟨.privateRow 7 16, 319555365903878176800⟩, ⟨.privateRow 7 17, 769976262606487416480⟩, ⟨.privateRow 7 18, 1399534148819762755800⟩, ⟨.privateRow 7 19, 2264943761607398446575⟩, ⟨.privateRow 7 20, 3371635187189898314400⟩, ⟨.privateRow 7 21, 4637991074577120760500⟩, ⟨.privateRow 7 22, 3651807709245985609320⟩, ⟨.privateRow 8 11, 3719692089886412640⟩, ⟨.privateRow 8 12, 16937883623589914700⟩, ⟨.privateRow 8 13, 75109167199629486000⟩, ⟨.privateRow 8 14, 237130370730258805800⟩, ⟨.privateRow 8 15, 516107277471739753800⟩, ⟨.privateRow 8 16, 896910755173861247820⟩, ⟨.privateRow 8 17, 1408833379044478787400⟩, ⟨.privateRow 8 18, 2066172715554093271125⟩, ⟨.privateRow 8 19, 986382634550236209000⟩, ⟨.privateRow 9 8, 1094027085260709600⟩, ⟨.privateRow 9 9, 3487211334268511850⟩, ⟨.privateRow 9 10, 19838357812727534080⟩, ⟨.privateRow 9 11, 75722303258401971600⟩, ⟨.privateRow 9 12, 211736318962765027200⟩, ⟨.privateRow 9 13, 432414205449295469400⟩, ⟨.privateRow 9 14, 732103034054916669600⟩, ⟨.privateRow 9 15, 803453491415465130240⟩, ⟨.privateRow 10 6, 1859846044943206320⟩, ⟨.privateRow 10 7, 5907746260407831840⟩, ⟨.privateRow 10 8, 27200248407294392430⟩, ⟨.privateRow 10 9, 93736240665137598528⟩, ⟨.privateRow 10 10, 241514293550482077840⟩, ⟨.privateRow 10 11, 448079831750932476480⟩, ⟨.privateRow 11 4, 4404898527497067600⟩, ⟨.privateRow 11 5, 9299230224716031600⟩, ⟨.privateRow 11 6, 49231218836731932000⟩, ⟨.privateRow 11 7, 151693693040680265475⟩, ⟨.privateRow 11 8, 72533995752785046480⟩, ⟨.privateRow 12 2, 15343729870781452140⟩, ⟨.privateRow 12 3, 32302589201645162400⟩, ⟨.privateRow 12 4, 51145766235938173800⟩, ⟨.hall 3 29, 18964850120285874845040⟩, ⟨.assumptionRow 18, 206335630289771840⟩]
  caps := #[0, 18891823989893074334400, 389312475730273695600, 554578857209033514000, 0, 43532534997910135216, 9374480533398588800, 137973031861842569250, 256645554745341675595, 2195268109063081910, 880979705499413520, 231492264236308556910, 0, 7504213099053702757440, 2634697183518426861120] }

theorem case_47_33_18_checked :
    (Witness.linear .conditional case_47_33_18).check 47 33 18 = true := by
  change case_47_33_18.check 47 33 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_33_19 : Certificate := {
  objectiveScale := 324080713756800000
  eta := 31720118070744672846076800
  rows := #[⟨.count 2, 3483752344226479650124800⟩, ⟨.count 3, 341290222214647683978000⟩, ⟨.count 4, 28277210586253893264000⟩, ⟨.count 5, 1570956143680771848000⟩, ⟨.path 5, 1534232009723083070400⟩, ⟨.privateRow 2 30, 330921911666354589781200⟩, ⟨.privateRow 3 26, 17510924481561670199040⟩, ⟨.privateRow 3 27, 61273835254148771954700⟩, ⟨.privateRow 3 28, 133636002622444325203200⟩, ⟨.privateRow 4 23, 5610557656002756600000⟩, ⟨.privateRow 4 26, 140777307425593167228900⟩, ⟨.privateRow 4 27, 15866657051175795664800⟩, ⟨.privateRow 4 28, 70221739622530501605600⟩, ⟨.privateRow 5 20, 1256764914944617478400⟩, ⟨.privateRow 5 24, 52872099971720057316288⟩, ⟨.privateRow 6 16, 8727534131559843600⟩, ⟨.privateRow 6 17, 203113521607210905600⟩, ⟨.privateRow 6 18, 546343636635646209360⟩, ⟨.privateRow 6 20, 885844714353324125400⟩, ⟨.privateRow 6 21, 2700548418422660176800⟩, ⟨.privateRow 6 22, 8416252080867542511600⟩, ⟨.privateRow 6 23, 6776057499743062571040⟩, ⟨.privateRow 6 24, 35634521859158841418800⟩, ⟨.privateRow 7 13, 1870185885334252200⟩, ⟨.privateRow 7 14, 30210695070784074000⟩, ⟨.privateRow 7 15, 108003234878053064550⟩, ⟨.privateRow 7 16, 365366315234846179800⟩, ⟨.privateRow 7 17, 70693026465634733160⟩, ⟨.privateRow 7 18, 503287801586617647600⟩, ⟨.privateRow 7 21, 14358975529948832682900⟩, ⟨.privateRow 8 13, 126884919297293110800⟩, ⟨.privateRow 8 15, 512940983277585353400⟩, ⟨.privateRow 8 19, 1114630787659214311200⟩, ⟨.privateRow 8 20, 4008120049918858173300⟩, ⟨.privateRow 9 11, 1246790590222834800⟩, ⟨.privateRow 10 10, 2244223062401102640⟩, ⟨.privateRow 10 11, 2416855605662725920⟩, ⟨.hall 10 6, 84813921989362800⟩, ⟨.hall 11 6, 3860032787067600⟩, ⟨.hall 12 6, 31845270493307700⟩, ⟨.hall 7 8, 494398726628184⟩, ⟨.hall 9 8, 23495851747368000⟩, ⟨.hall 11 8, 11708766120771720⟩, ⟨.hall 7 9, 15682495201434684⟩, ⟨.hall 8 9, 23854697483145984⟩, ⟨.hall 9 10, 2130646556181780⟩, ⟨.hall 6 12, 4079391952419630⟩, ⟨.hall 5 17, 1107900652906520⟩, ⟨.hall 4 21, 89818176613152960⟩, ⟨.hall 2 27, 66590267174137278000⟩, ⟨.hall 3 27, 154645025966604716400⟩, ⟨.hall 1 31, 254833632694766205805725⟩]
  caps := #[0, 3409438359010685601600, 0, 641052555180091334280, 0, 147240247557480229152, 100176049294841520, 149476417041680907660, 0, 99247970404055506176, 20867171556170879280, 58868329921870669200, 614250917948943475200, 0, 5024547386085427200000] }

theorem case_47_33_19_checked :
    (Witness.linear .negative case_47_33_19).check 47 33 19 = true := by
  change case_47_33_19.check 47 33 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_33_20 : Certificate := {
  objectiveScale := 2
  eta := 55660
  rows := #[⟨.assumptionRow 20, 1⟩]
  caps := #[0, 0, 27324, 10241, 5187, 1938, 1020, 408, 210, 91, 89148, 120802, 93670, 58140, 31008] }

theorem case_47_33_20_checked :
    (Witness.linear .conditional case_47_33_20).check 47 33 20 = true := by
  change case_47_33_20.check 47 33 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_33_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58786, 58786, 41990, 25194] }

theorem case_47_33_21_checked :
    (Witness.linear .negative case_47_33_21).check 47 33 21 = true := by
  change case_47_33_21.check 47 33 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_34_1_checked :
    (Witness.rising).check 47 34 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_34_2_checked :
    (Witness.rising).check 47 34 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_34_3_checked :
    (Witness.rising).check 47 34 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_34_4_checked :
    (Witness.rising).check 47 34 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_34_5_checked :
    (Witness.rising).check 47 34 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_34_6_checked :
    (Witness.rising).check 47 34 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_34_7_checked :
    (Witness.rising).check 47 34 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_34_8_checked :
    (Witness.rising).check 47 34 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_34_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_47_34_9_checked :
    (Witness.linear .positive case_47_34_9).check 47 34 9 = true := by
  change case_47_34_9.check 47 34 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_34_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_47_34_10_checked :
    (Witness.linear .positive case_47_34_10).check 47 34 10 = true := by
  change case_47_34_10.check 47 34 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_34_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_47_34_11_checked :
    (Witness.linear .positive case_47_34_11).check 47 34 11 = true := by
  change case_47_34_11.check 47 34 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_34_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_47_34_12_checked :
    (Witness.linear .positive case_47_34_12).check 47 34 12 = true := by
  change case_47_34_12.check 47 34 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_34_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_47_34_13_checked :
    (Witness.linear .positive case_47_34_13).check 47 34 13 = true := by
  change case_47_34_13.check 47 34 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_34_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_47_34_14_checked :
    (Witness.linear .positive case_47_34_14).check 47 34 14 = true := by
  change case_47_34_14.check 47 34 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_34_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_47_34_15_checked :
    (Witness.linear .positive case_47_34_15).check 47 34 15 = true := by
  change case_47_34_15.check 47 34 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_34_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_47_34_16_checked :
    (Witness.linear .positive case_47_34_16).check 47 34 16 = true := by
  change case_47_34_16.check 47 34 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_34_17 : Certificate := {
  objectiveScale := 602
  eta := 1414995075
  rows := #[⟨.assumptionRow 17, 963⟩]
  caps := #[0, 0, 406737750, 121538440, 36759338, 11269470, 3509922, 1113736, 361361, 120461, 30716730, 22006446, 10748661, 4164363] }

theorem case_47_34_17_checked :
    (Witness.linear .conditional case_47_34_17).check 47 34 17 = true := by
  change case_47_34_17.check 47 34 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_34_18 : Certificate := {
  objectiveScale := 17377360000000
  eta := 2898742480430837040000
  rows := #[⟨.count 2, 244063664923118040000⟩, ⟨.count 3, 17360917146633060000⟩, ⟨.count 4, 818768144906712000⟩, ⟨.path 4, 789413790674500992⟩, ⟨.privateRow 2 31, 20639780319523365000⟩, ⟨.privateRow 2 32, 29048579708958810000⟩, ⟨.privateRow 3 26, 92658946440060000⟩, ⟨.privateRow 3 27, 2264247709371648000⟩, ⟨.privateRow 3 28, 4150699623485415000⟩, ⟨.privateRow 3 29, 8600434937754660000⟩, ⟨.privateRow 3 30, 9249047562835080000⟩, ⟨.privateRow 3 31, 11927733469011360000⟩, ⟨.privateRow 4 23, 162047862012786750⟩, ⟨.privateRow 4 24, 575087149398762000⟩, ⟨.privateRow 4 25, 936276536073879000⟩, ⟨.privateRow 4 26, 2121215990230537200⟩, ⟨.privateRow 4 27, 2935814482547446500⟩, ⟨.privateRow 4 28, 3686983714255842000⟩, ⟨.privateRow 4 29, 4582827255519513000⟩, ⟨.privateRow 5 19, 2756795100696000⟩, ⟨.privateRow 5 20, 51215126759596800⟩, ⟨.privateRow 5 21, 126165918991112000⟩, ⟨.privateRow 5 22, 233332074217242000⟩, ⟨.privateRow 5 23, 530923729472136000⟩, ⟨.privateRow 5 24, 873240374026020000⟩, ⟨.privateRow 5 25, 1208272661578382400⟩, ⟨.privateRow 5 26, 1525503200026806000⟩, ⟨.privateRow 5 27, 1921690392229608000⟩, ⟨.privateRow 6 16, 323982330210000⟩, ⟨.privateRow 6 17, 13863743880236250⟩, ⟨.privateRow 6 18, 32736941820765000⟩, ⟨.privateRow 6 19, 60228315186039000⟩, ⟨.privateRow 6 20, 149049870914945000⟩, ⟨.privateRow 6 21, 268237120518241875⟩, ⟨.privateRow 6 22, 412452647952345000⟩, ⟨.privateRow 6 23, 574555664099917500⟩, ⟨.privateRow 6 24, 727793906583744000⟩, ⟨.privateRow 6 25, 304300403649742500⟩, ⟨.privateRow 7 14, 3867952309650000⟩, ⟨.privateRow 7 15, 10691416896930000⟩, ⟨.privateRow 7 16, 19705068155272500⟩, ⟨.privateRow 7 17, 46931154690420000⟩, ⟨.privateRow 7 18, 95486849350893000⟩, ⟨.privateRow 7 19, 158442787202700000⟩, ⟨.privateRow 7 20, 181632593873981250⟩, ⟨.privateRow 7 21, 434757839604660000⟩, ⟨.privateRow 8 11, 1316178216478125⟩, ⟨.privateRow 8 12, 4352162635821000⟩, ⟨.privateRow 8 13, 8874801688252500⟩, ⟨.privateRow 8 14, 19924913307915000⟩, ⟨.privateRow 8 15, 40187308209798750⟩, ⟨.privateRow 8 16, 23739068922660000⟩, ⟨.privateRow 8 17, 220486174824415500⟩, ⟨.privateRow 8 18, 31354289956990000⟩, ⟨.privateRow 9 8, 561569372364000⟩, ⟨.privateRow 9 9, 2180210504472000⟩, ⟨.privateRow 9 10, 5264712865912500⟩, ⟨.privateRow 9 11, 12354526192008000⟩, ⟨.privateRow 9 12, 24067258815600000⟩, ⟨.privateRow 9 13, 44579968636896000⟩, ⟨.privateRow 9 14, 36221224517478000⟩, ⟨.privateRow 10 5, 379059326345700⟩, ⟨.privateRow 10 6, 1197029451618000⟩, ⟨.privateRow 10 7, 3790593263457000⟩, ⟨.privateRow 10 8, 10256899418766000⟩, ⟨.privateRow 10 9, 21795911264877750⟩, ⟨.privateRow 10 10, 6064949221531200⟩, ⟨.privateRow 11 3, 1203362940780000⟩, ⟨.privateRow 11 4, 3790593263457000⟩, ⟨.privateRow 11 5, 9310229068140000⟩, ⟨.hall 3 30, 423079119082620000⟩, ⟨.assumptionRow 18, 10573751188000⟩]
  caps := #[0, 0, 29143046628888192, 22510015880628276, 16024365219204342, 5676888096880000, 576630363694000, 13016987598730500, 20210272509496125, 393098560654800, 0, 0, 1156537388554548000, 437471802335568000] }

theorem case_47_34_18_checked :
    (Witness.linear .conditional case_47_34_18).check 47 34 18 = true := by
  change case_47_34_18.check 47 34 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_34_19 : Certificate := {
  objectiveScale := 15995299320000000
  eta := 5179705897434434205840000
  rows := #[⟨.count 2, 317484575585399902680000⟩, ⟨.count 3, 13120911145860598080000⟩, ⟨.path 3, 13062536009603360280000⟩, ⟨.path 4, 1990758932475401088⟩, ⟨.privateRow 2 30, 11612760439439839680000⟩, ⟨.privateRow 2 31, 33127472860723471230000⟩, ⟨.privateRow 2 32, 46036300313493650160000⟩, ⟨.privateRow 3 25, 207370722132854280000⟩, ⟨.privateRow 3 26, 1781503021959520860000⟩, ⟨.privateRow 3 27, 4565926263688846056000⟩, ⟨.privateRow 3 28, 6320094054094490670000⟩, ⟨.privateRow 3 29, 13221454526288648640000⟩, ⟨.privateRow 3 30, 14101209105034091040000⟩, ⟨.privateRow 3 31, 18286327315351695600000⟩, ⟨.privateRow 4 20, 22108118310031572000⟩, ⟨.privateRow 4 21, 52596755886423949200⟩, ⟨.privateRow 4 22, 120023660385985356000⟩, ⟨.privateRow 4 23, 595248231940443081000⟩, ⟨.privateRow 4 24, 979220708668906704000⟩, ⟨.privateRow 4 25, 1502495141271680556000⟩, ⟨.privateRow 4 26, 3164854257423961502400⟩, ⟨.privateRow 4 27, 4411340816280718320000⟩, ⟨.privateRow 4 28, 5599009497587065560000⟩, ⟨.privateRow 4 29, 7035523045452837936000⟩, ⟨.privateRow 5 16, 5027169021402528000⟩, ⟨.privateRow 5 17, 9087574769458416000⟩, ⟨.privateRow 5 18, 14662576312424040000⟩, ⟨.privateRow 5 19, 49814674848443232000⟩, ⟨.privateRow 5 20, 159863974880600390400⟩, ⟨.privateRow 5 21, 243817697538022608000⟩, ⟨.privateRow 5 22, 372638903711462388000⟩, ⟨.privateRow 5 23, 816555882476382048000⟩, ⟨.privateRow 5 24, 1284441684968345904000⟩, ⟨.privateRow 5 25, 1792688473032141484800⟩, ⟨.privateRow 5 26, 2300558223419331876000⟩, ⟨.privateRow 5 27, 2998706321266607952000⟩, ⟨.privateRow 6 12, 1293756733449180000⟩, ⟨.privateRow 6 14, 8273882347724994000⟩, ⟨.privateRow 6 15, 5049611740248075000⟩, ⟨.privateRow 6 16, 19335265466932800000⟩, ⟨.privateRow 6 17, 48700699894836990000⟩, ⟨.privateRow 6 18, 77978246752436940000⟩, ⟨.privateRow 6 19, 111383213630449761000⟩, ⟨.privateRow 6 20, 232855676199686540000⟩, ⟨.privateRow 6 21, 403155390661694921250⟩, ⟨.privateRow 6 22, 603933564133669770000⟩, ⟨.privateRow 6 23, 843621801404111730000⟩, ⟨.privateRow 6 24, 1088067895069809654000⟩, ⟨.privateRow 6 25, 517641310172541555000⟩, ⟨.privateRow 7 8, 336640782683205000⟩, ⟨.privateRow 7 9, 566973949782240000⟩, ⟨.privateRow 7 11, 5861510098484040000⟩, ⟨.privateRow 7 12, 2945606848478043750⟩, ⟨.privateRow 7 13, 9066858413600988000⟩, ⟨.privateRow 7 14, 19621348476392520000⟩, ⟨.privateRow 7 15, 32628260475449100000⟩, ⟨.privateRow 7 16, 46680855198737760000⟩, ⟨.privateRow 7 17, 85445551386500760000⟩, ⟨.privateRow 7 18, 147179350189097226000⟩, ⟨.privateRow 7 19, 236247020380791420000⟩, ⟨.privateRow 7 20, 274362237886812075000⟩, ⟨.privateRow 7 21, 617110646198698080000⟩, ⟨.privateRow 8 4, 136607853842460000⟩, ⟨.privateRow 8 5, 357043254360975000⟩, ⟨.privateRow 8 6, 448854376910940000⟩, ⟨.privateRow 8 9, 12742477033416130000⟩, ⟨.privateRow 8 10, 554467171478220000⟩, ⟨.privateRow 8 11, 11095119129267298125⟩, ⟨.privateRow 8 12, 18537685766421822000⟩, ⟨.privateRow 8 13, 27380116991567340000⟩, ⟨.privateRow 8 14, 47250554984817030000⟩, ⟨.privateRow 8 15, 72920133982323127500⟩, ⟨.privateRow 8 16, 64696237690208670000⟩, ⟨.privateRow 8 17, 280893069070866252000⟩, ⟨.privateRow 9 3, 765003981517776000⟩, ⟨.privateRow 9 6, 13196318681181636000⟩, ⟨.privateRow 9 8, 15919368567774672000⟩, ⟨.privateRow 9 9, 9315048480834096000⟩, ⟨.privateRow 9 10, 22308062532473718000⟩, ⟨.privateRow 9 11, 38374056863372630400⟩, ⟨.privateRow 9 12, 56735193241542816000⟩, ⟨.privateRow 9 13, 29776308819076512000⟩, ⟨.privateRow 10 0, 1357335635778682560⟩, ⟨.privateRow 10 1, 235648547878243500⟩, ⟨.privateRow 10 3, 4113138290238432000⟩, ⟨.privateRow 10 4, 5116939896784716000⟩, ⟨.privateRow 10 5, 51182864599154488200⟩, ⟨.privateRow 11 0, 21993864468636060000⟩, ⟨.privateRow 12 0, 9016118353602360000⟩, ⟨.hall 3 30, 631234045671269040000⟩]
  caps := #[0, 1169493952248750256128, 311793722540101449648, 0, 15937717453894578888, 1725764999791728000, 2763523930943942250, 11475664013129026500, 0, 593365379492580240, 0, 56779329756469320000, 0, 991964482629120000000] }

theorem case_47_34_19_checked :
    (Witness.linear .negative case_47_34_19).check 47 34 19 = true := by
  change case_47_34_19.check 47 34 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_34_20 : Certificate := {
  objectiveScale := 997
  eta := 208736385
  rows := #[⟨.assumptionRow 20, 623⟩]
  caps := #[0, 0, 71655925, 31702165, 11630850, 4822713, 1930248, 736032, 331184, 148580, 125995840, 122251624, 84149252, 48312402] }

theorem case_47_34_20_checked :
    (Witness.linear .conditional case_47_34_20).check 47 34 20 = true := by
  change case_47_34_20.check 47 34 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_34_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208012, 208012, 149226, 90440] }

theorem case_47_34_21_checked :
    (Witness.linear .negative case_47_34_21).check 47 34 21 = true := by
  change case_47_34_21.check 47 34 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_34_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58786, 58786] }

theorem case_47_34_22_checked :
    (Witness.linear .negative case_47_34_22).check 47 34 22 = true := by
  change case_47_34_22.check 47 34 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_35_1_checked :
    (Witness.rising).check 47 35 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_35_2_checked :
    (Witness.rising).check 47 35 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_35_3_checked :
    (Witness.rising).check 47 35 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_35_4_checked :
    (Witness.rising).check 47 35 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_35_5_checked :
    (Witness.rising).check 47 35 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_35_6_checked :
    (Witness.rising).check 47 35 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_35_7_checked :
    (Witness.rising).check 47 35 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_35_8_checked :
    (Witness.rising).check 47 35 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_35_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_47_35_9_checked :
    (Witness.linear .positive case_47_35_9).check 47 35 9 = true := by
  change case_47_35_9.check 47 35 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_35_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_47_35_10_checked :
    (Witness.linear .positive case_47_35_10).check 47 35 10 = true := by
  change case_47_35_10.check 47 35 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_35_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_47_35_11_checked :
    (Witness.linear .positive case_47_35_11).check 47 35 11 = true := by
  change case_47_35_11.check 47 35 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_35_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_47_35_12_checked :
    (Witness.linear .positive case_47_35_12).check 47 35 12 = true := by
  change case_47_35_12.check 47 35 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_35_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_47_35_13_checked :
    (Witness.linear .positive case_47_35_13).check 47 35 13 = true := by
  change case_47_35_13.check 47 35 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_35_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_47_35_14_checked :
    (Witness.linear .positive case_47_35_14).check 47 35 14 = true := by
  change case_47_35_14.check 47 35 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_35_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_47_35_15_checked :
    (Witness.linear .positive case_47_35_15).check 47 35 15 = true := by
  change case_47_35_15.check 47 35 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_35_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_47_35_16_checked :
    (Witness.linear .positive case_47_35_16).check 47 35 16 = true := by
  change case_47_35_16.check 47 35 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_35_17 : Certificate := {
  objectiveScale := 13
  eta := 115354890
  rows := #[⟨.assumptionRow 17, 33⟩]
  caps := #[0, 0, 32353295, 9152528, 2615008, 764218, 226746, 68510, 21164, 6721, 2211, 762, 56672] }

theorem case_47_35_17_checked :
    (Witness.linear .conditional case_47_35_17).check 47 35 17 = true := by
  change case_47_35_17.check 47 35 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_35_18 : Certificate := {
  objectiveScale := 207
  eta := 544012560
  rows := #[⟨.assumptionRow 18, 254⟩]
  caps := #[0, 0, 160516655, 48177065, 15363172, 4919290, 1585284, 515372, 170430, 55929445, 46387550, 26875937, 12757778] }

theorem case_47_35_18_checked :
    (Witness.linear .conditional case_47_35_18).check 47 35 18 = true := by
  change case_47_35_18.check 47 35 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_35_19 : Certificate := {
  objectiveScale := 287
  eta := 507123435
  rows := #[⟨.assumptionRow 19, 271⟩]
  caps := #[0, 0, 170941290, 56265935, 18223337, 5835318, 2005830, 724608, 255645, 100212840, 91260895, 58655014, 31279149] }

theorem case_47_35_19_checked :
    (Witness.linear .conditional case_47_35_19).check 47 35 19 = true := by
  change case_47_35_19.check 47 35 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_35_20 : Certificate := {
  objectiveScale := 993
  eta := 184463565
  rows := #[⟨.assumptionRow 20, 611⟩]
  caps := #[0, 0, 65659825, 27875793, 10672794, 4214181, 1775208, 638588, 334305, 442805545, 431364885, 299663573, 174796941] }

theorem case_47_35_20_checked :
    (Witness.linear .conditional case_47_35_20).check 47 35 20 = true := by
  change case_47_35_20.check 47 35 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_35_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900, 534888, 326876] }

theorem case_47_35_21_checked :
    (Witness.linear .negative case_47_35_21).check 47 35 21 = true := by
  change case_47_35_21.check 47 35 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_35_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208012, 208012] }

theorem case_47_35_22_checked :
    (Witness.linear .negative case_47_35_22).check 47 35 22 = true := by
  change case_47_35_22.check 47 35 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_36_1_checked :
    (Witness.rising).check 47 36 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_36_2_checked :
    (Witness.rising).check 47 36 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_36_3_checked :
    (Witness.rising).check 47 36 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_36_4_checked :
    (Witness.rising).check 47 36 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_36_5_checked :
    (Witness.rising).check 47 36 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_36_6_checked :
    (Witness.rising).check 47 36 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_36_7_checked :
    (Witness.rising).check 47 36 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_36_8_checked :
    (Witness.rising).check 47 36 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_36_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_47_36_9_checked :
    (Witness.linear .positive case_47_36_9).check 47 36 9 = true := by
  change case_47_36_9.check 47 36 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_36_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_47_36_10_checked :
    (Witness.linear .positive case_47_36_10).check 47 36 10 = true := by
  change case_47_36_10.check 47 36 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_36_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_47_36_11_checked :
    (Witness.linear .positive case_47_36_11).check 47 36 11 = true := by
  change case_47_36_11.check 47 36 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_36_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_47_36_12_checked :
    (Witness.linear .positive case_47_36_12).check 47 36 12 = true := by
  change case_47_36_12.check 47 36 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_36_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_47_36_13_checked :
    (Witness.linear .positive case_47_36_13).check 47 36 13 = true := by
  change case_47_36_13.check 47 36 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_36_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_47_36_14_checked :
    (Witness.linear .positive case_47_36_14).check 47 36 14 = true := by
  change case_47_36_14.check 47 36 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_36_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_47_36_15_checked :
    (Witness.linear .positive case_47_36_15).check 47 36 15 = true := by
  change case_47_36_15.check 47 36 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_36_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_47_36_16_checked :
    (Witness.linear .positive case_47_36_16).check 47 36 16 = true := by
  change case_47_36_16.check 47 36 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_36_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_47_36_17_checked :
    (Witness.linear .positive case_47_36_17).check 47 36 17 = true := by
  change case_47_36_17.check 47 36 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_36_18 : Certificate := {
  objectiveScale := 973
  eta := 4038568275
  rows := #[⟨.assumptionRow 18, 1307⟩]
  caps := #[0, 0, 1202809725, 360863675, 109176584, 33349750, 10300470, 3222180, 1022840, 424182330, 337944750, 187846175] }

theorem case_47_36_18_checked :
    (Witness.linear .conditional case_47_36_18).check 47 36 18 = true := by
  change case_47_36_18.check 47 36 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_36_19 : Certificate := {
  objectiveScale := 32
  eta := 104702325
  rows := #[⟨.assumptionRow 19, 33⟩]
  caps := #[0, 0, 31870410, 9686105, 3268760, 1087218, 358530, 117708, 10737090, 23519340, 18434845, 10935925] }

theorem case_47_36_19_checked :
    (Witness.linear .conditional case_47_36_19).check 47 36 19 = true := by
  change case_47_36_19.check 47 36 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_36_20 : Certificate := {
  objectiveScale := 45
  eta := 27972945
  rows := #[⟨.assumptionRow 20, 32⟩]
  caps := #[0, 0, 9291425, 3725425, 1355574, 458337, 193800, 72012, 29595825, 48316905, 38659205, 24395525] }

theorem case_47_36_20_checked :
    (Witness.linear .conditional case_47_36_20).check 47 36 20 = true := by
  change case_47_36_20.check 47 36 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_36_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 2674440, 2674440, 1931540, 1188640] }

theorem case_47_36_21_checked :
    (Witness.linear .negative case_47_36_21).check 47 36 21 = true := by
  change case_47_36_21.check 47 36 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_36_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900] }

theorem case_47_36_22_checked :
    (Witness.linear .negative case_47_36_22).check 47 36 22 = true := by
  change case_47_36_22.check 47 36 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_36_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_36_23_checked :
    (Witness.linear .negative case_47_36_23).check 47 36 23 = true := by
  change case_47_36_23.check 47 36 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_37_1_checked :
    (Witness.rising).check 47 37 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_37_2_checked :
    (Witness.rising).check 47 37 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_37_3_checked :
    (Witness.rising).check 47 37 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_37_4_checked :
    (Witness.rising).check 47 37 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_37_5_checked :
    (Witness.rising).check 47 37 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_37_6_checked :
    (Witness.rising).check 47 37 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_37_7_checked :
    (Witness.rising).check 47 37 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_37_8_checked :
    (Witness.rising).check 47 37 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_37_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_47_37_9_checked :
    (Witness.linear .positive case_47_37_9).check 47 37 9 = true := by
  change case_47_37_9.check 47 37 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_37_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_47_37_10_checked :
    (Witness.linear .positive case_47_37_10).check 47 37 10 = true := by
  change case_47_37_10.check 47 37 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_37_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_47_37_11_checked :
    (Witness.linear .positive case_47_37_11).check 47 37 11 = true := by
  change case_47_37_11.check 47 37 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_37_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_47_37_12_checked :
    (Witness.linear .positive case_47_37_12).check 47 37 12 = true := by
  change case_47_37_12.check 47 37 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_37_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_47_37_13_checked :
    (Witness.linear .positive case_47_37_13).check 47 37 13 = true := by
  change case_47_37_13.check 47 37 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_37_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_47_37_14_checked :
    (Witness.linear .positive case_47_37_14).check 47 37 14 = true := by
  change case_47_37_14.check 47 37 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_37_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_47_37_15_checked :
    (Witness.linear .positive case_47_37_15).check 47 37 15 = true := by
  change case_47_37_15.check 47 37 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_37_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_47_37_16_checked :
    (Witness.linear .positive case_47_37_16).check 47 37 16 = true := by
  change case_47_37_16.check 47 37 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_37_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_47_37_17_checked :
    (Witness.linear .positive case_47_37_17).check 47 37 17 = true := by
  change case_47_37_17.check 47 37 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_37_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_47_37_18_checked :
    (Witness.linear .positive case_47_37_18).check 47 37 18 = true := by
  change case_47_37_18.check 47 37 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_37_19 : Certificate := {
  objectiveScale := 365
  eta := 1273726545
  rows := #[⟨.assumptionRow 19, 381⟩]
  caps := #[0, 0, 384660510, 121573400, 40287467, 13217160, 4312050, 1403520, 763871745, 679764540, 428721150] }

theorem case_47_37_19_checked :
    (Witness.linear .conditional case_47_37_19).check 47 37 19 = true := by
  change case_47_37_19.check 47 37 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_37_20 : Certificate := {
  objectiveScale := 398
  eta := 486182970
  rows := #[⟨.assumptionRow 20, 307⟩]
  caps := #[0, 0, 169317720, 56001550, 20646065, 7631844, 2643432, 969000, 1044572025, 997356360, 680356560] }

theorem case_47_37_20_checked :
    (Witness.linear .conditional case_47_37_20).check 47 37 20 = true := by
  change case_47_37_20.check 47 37 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_37_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 9694845, 9694845, 7020405, 4345965] }

theorem case_47_37_21_checked :
    (Witness.linear .negative case_47_37_21).check 47 37 21 = true := by
  change case_47_37_21.check 47 37 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_37_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440, 2674440] }

theorem case_47_37_22_checked :
    (Witness.linear .negative case_47_37_22).check 47 37 22 = true := by
  change case_47_37_22.check 47 37 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_37_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_37_23_checked :
    (Witness.linear .negative case_47_37_23).check 47 37 23 = true := by
  change case_47_37_23.check 47 37 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_37_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_37_24_checked :
    (Witness.linear .negative case_47_37_24).check 47 37 24 = true := by
  change case_47_37_24.check 47 37 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_38_1_checked :
    (Witness.rising).check 47 38 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_38_2_checked :
    (Witness.rising).check 47 38 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_38_3_checked :
    (Witness.rising).check 47 38 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_38_4_checked :
    (Witness.rising).check 47 38 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_38_5_checked :
    (Witness.rising).check 47 38 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_38_6_checked :
    (Witness.rising).check 47 38 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_38_7_checked :
    (Witness.rising).check 47 38 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_38_8_checked :
    (Witness.rising).check 47 38 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_38_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_47_38_9_checked :
    (Witness.linear .positive case_47_38_9).check 47 38 9 = true := by
  change case_47_38_9.check 47 38 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_38_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_47_38_10_checked :
    (Witness.linear .positive case_47_38_10).check 47 38 10 = true := by
  change case_47_38_10.check 47 38 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_38_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_47_38_11_checked :
    (Witness.linear .positive case_47_38_11).check 47 38 11 = true := by
  change case_47_38_11.check 47 38 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_38_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_47_38_12_checked :
    (Witness.linear .positive case_47_38_12).check 47 38 12 = true := by
  change case_47_38_12.check 47 38 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_38_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_47_38_13_checked :
    (Witness.linear .positive case_47_38_13).check 47 38 13 = true := by
  change case_47_38_13.check 47 38 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_38_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_47_38_14_checked :
    (Witness.linear .positive case_47_38_14).check 47 38 14 = true := by
  change case_47_38_14.check 47 38 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_38_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_47_38_15_checked :
    (Witness.linear .positive case_47_38_15).check 47 38 15 = true := by
  change case_47_38_15.check 47 38 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_38_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_47_38_16_checked :
    (Witness.linear .positive case_47_38_16).check 47 38 16 = true := by
  change case_47_38_16.check 47 38 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_38_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_47_38_17_checked :
    (Witness.linear .positive case_47_38_17).check 47 38 17 = true := by
  change case_47_38_17.check 47 38 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_38_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_47_38_18_checked :
    (Witness.linear .positive case_47_38_18).check 47 38 18 = true := by
  change case_47_38_18.check 47 38 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_38_19 : Certificate := {
  objectiveScale := 5
  eta := 145772850
  rows := #[⟨.assumptionRow 19, 8⟩]
  caps := #[0, 0, 41250615, 11759670, 3380195, 1010344, 305558, 93670, 29172, 9256] }

theorem case_47_38_19_checked :
    (Witness.linear .conditional case_47_38_19).check 47 38 19 = true := by
  change case_47_38_19.check 47 38 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_38_20 : Certificate := {
  objectiveScale := 19
  eta := 42791385
  rows := #[⟨.assumptionRow 20, 16⟩]
  caps := #[0, 0, 15509130, 5311735, 1754555, 572033, 217056, 77538750, 122211075, 95597775] }

theorem case_47_38_20_checked :
    (Witness.linear .conditional case_47_38_20).check 47 38 20 = true := by
  change case_47_38_20.check 47 38 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_38_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 35357670, 35357670, 25662825, 15967980] }

theorem case_47_38_21_checked :
    (Witness.linear .negative case_47_38_21).check 47 38 21 = true := by
  change case_47_38_21.check 47 38 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_38_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 9694845, 9694845] }

theorem case_47_38_22_checked :
    (Witness.linear .negative case_47_38_22).check 47 38 22 = true := by
  change case_47_38_22.check 47 38 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_38_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_38_23_checked :
    (Witness.linear .negative case_47_38_23).check 47 38 23 = true := by
  change case_47_38_23.check 47 38 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_38_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_38_24_checked :
    (Witness.linear .negative case_47_38_24).check 47 38 24 = true := by
  change case_47_38_24.check 47 38 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_39_1_checked :
    (Witness.rising).check 47 39 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_39_2_checked :
    (Witness.rising).check 47 39 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_39_3_checked :
    (Witness.rising).check 47 39 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_39_4_checked :
    (Witness.rising).check 47 39 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_39_5_checked :
    (Witness.rising).check 47 39 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_39_6_checked :
    (Witness.rising).check 47 39 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_39_7_checked :
    (Witness.rising).check 47 39 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_39_8_checked :
    (Witness.rising).check 47 39 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_39_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1] }

theorem case_47_39_9_checked :
    (Witness.linear .positive case_47_39_9).check 47 39 9 = true := by
  change case_47_39_9.check 47 39 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_39_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_47_39_10_checked :
    (Witness.linear .positive case_47_39_10).check 47 39 10 = true := by
  change case_47_39_10.check 47 39 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_39_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_47_39_11_checked :
    (Witness.linear .positive case_47_39_11).check 47 39 11 = true := by
  change case_47_39_11.check 47 39 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_39_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_47_39_12_checked :
    (Witness.linear .positive case_47_39_12).check 47 39 12 = true := by
  change case_47_39_12.check 47 39 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_39_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_47_39_13_checked :
    (Witness.linear .positive case_47_39_13).check 47 39 13 = true := by
  change case_47_39_13.check 47 39 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_39_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_47_39_14_checked :
    (Witness.linear .positive case_47_39_14).check 47 39 14 = true := by
  change case_47_39_14.check 47 39 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_39_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_47_39_15_checked :
    (Witness.linear .positive case_47_39_15).check 47 39 15 = true := by
  change case_47_39_15.check 47 39 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_39_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_47_39_16_checked :
    (Witness.linear .positive case_47_39_16).check 47 39 16 = true := by
  change case_47_39_16.check 47 39 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_39_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_47_39_17_checked :
    (Witness.linear .positive case_47_39_17).check 47 39 17 = true := by
  change case_47_39_17.check 47 39 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_39_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_47_39_18_checked :
    (Witness.linear .positive case_47_39_18).check 47 39 18 = true := by
  change case_47_39_18.check 47 39 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_39_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_47_39_19_checked :
    (Witness.linear .positive case_47_39_19).check 47 39 19 = true := by
  change case_47_39_19.check 47 39 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_39_20 : Certificate := {
  objectiveScale := 15
  eta := 77388675
  rows := #[⟨.assumptionRow 20, 14⟩]
  caps := #[0, 0, 23671830, 8180640, 2739990, 898909, 290700, 158799360, 186713310] }

theorem case_47_39_20_checked :
    (Witness.linear .conditional case_47_39_20).check 47 39 20 = true := by
  change case_47_39_20.check 47 39 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_39_21 : Certificate := {
  objectiveScale := 32
  eta := 10607025
  rows := #[⟨.assumptionRow 21, 19⟩]
  caps := #[0, 0, 4242810, 1701425, 629717, 277761, 100776, 660009840, 648223950] }

theorem case_47_39_21_checked :
    (Witness.linear .conditional case_47_39_21).check 47 39 21 = true := by
  change case_47_39_21.check 47 39 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_39_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 35357670, 35357670] }

theorem case_47_39_22_checked :
    (Witness.linear .negative case_47_39_22).check 47 39 22 = true := by
  change case_47_39_22.check 47 39 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_39_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_39_23_checked :
    (Witness.linear .negative case_47_39_23).check 47 39 23 = true := by
  change case_47_39_23.check 47 39 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_39_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_39_24_checked :
    (Witness.linear .negative case_47_39_24).check 47 39 24 = true := by
  change case_47_39_24.check 47 39 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_39_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_39_25_checked :
    (Witness.linear .negative case_47_39_25).check 47 39 25 = true := by
  change case_47_39_25.check 47 39 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_40_1_checked :
    (Witness.rising).check 47 40 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_40_2_checked :
    (Witness.rising).check 47 40 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_40_3_checked :
    (Witness.rising).check 47 40 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_40_4_checked :
    (Witness.rising).check 47 40 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_40_5_checked :
    (Witness.rising).check 47 40 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_40_6_checked :
    (Witness.rising).check 47 40 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_40_7_checked :
    (Witness.rising).check 47 40 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_40_8_checked :
    (Witness.rising).check 47 40 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_40_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_47_40_9_checked :
    (Witness.linear .positive case_47_40_9).check 47 40 9 = true := by
  change case_47_40_9.check 47 40 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_40_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_47_40_10_checked :
    (Witness.linear .positive case_47_40_10).check 47 40 10 = true := by
  change case_47_40_10.check 47 40 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_40_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_47_40_11_checked :
    (Witness.linear .positive case_47_40_11).check 47 40 11 = true := by
  change case_47_40_11.check 47 40 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_40_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_47_40_12_checked :
    (Witness.linear .positive case_47_40_12).check 47 40 12 = true := by
  change case_47_40_12.check 47 40 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_40_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42] }

theorem case_47_40_13_checked :
    (Witness.linear .positive case_47_40_13).check 47 40 13 = true := by
  change case_47_40_13.check 47 40 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_40_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_47_40_14_checked :
    (Witness.linear .positive case_47_40_14).check 47 40 14 = true := by
  change case_47_40_14.check 47 40 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_40_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_47_40_15_checked :
    (Witness.linear .positive case_47_40_15).check 47 40 15 = true := by
  change case_47_40_15.check 47 40 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_40_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_47_40_16_checked :
    (Witness.linear .positive case_47_40_16).check 47 40 16 = true := by
  change case_47_40_16.check 47 40 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_40_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_47_40_17_checked :
    (Witness.linear .positive case_47_40_17).check 47 40 17 = true := by
  change case_47_40_17.check 47 40 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_40_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_47_40_18_checked :
    (Witness.linear .positive case_47_40_18).check 47 40 18 = true := by
  change case_47_40_18.check 47 40 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_40_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_47_40_19_checked :
    (Witness.linear .positive case_47_40_19).check 47 40 19 = true := by
  change case_47_40_19.check 47 40 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_40_20 : Certificate := {
  objectiveScale := 3
  eta := 1391975640
  rows := #[⟨.assumptionRow 20, 8⟩]
  caps := #[0, 0, 382110960, 106073010, 29654820, 8357625, 2377280, 683468] }

theorem case_47_40_20_checked :
    (Witness.linear .conditional case_47_40_20).check 47 40 20 = true := by
  change case_47_40_20.check 47 40 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_40_21 : Certificate := {
  objectiveScale := 17
  eta := 5278845
  rows := #[⟨.assumptionRow 21, 10⟩]
  caps := #[0, 0, 2022735, 847550, 298034, 138567, 1275977670, 1255507440] }

theorem case_47_40_21_checked :
    (Witness.linear .conditional case_47_40_21).check 47 40 21 = true := by
  change case_47_40_21.check 47 40 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_40_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 129644790, 129644790] }

theorem case_47_40_22_checked :
    (Witness.linear .negative case_47_40_22).check 47 40 22 = true := by
  change case_47_40_22.check 47 40 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_40_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_40_23_checked :
    (Witness.linear .negative case_47_40_23).check 47 40 23 = true := by
  change case_47_40_23.check 47 40 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_40_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_40_24_checked :
    (Witness.linear .negative case_47_40_24).check 47 40 24 = true := by
  change case_47_40_24.check 47 40 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_40_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_40_25_checked :
    (Witness.linear .negative case_47_40_25).check 47 40 25 = true := by
  change case_47_40_25.check 47 40 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_40_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_47_40_26_checked :
    (Witness.linear .negative case_47_40_26).check 47 40 26 = true := by
  change case_47_40_26.check 47 40 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_41_1_checked :
    (Witness.rising).check 47 41 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_41_2_checked :
    (Witness.rising).check 47 41 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_41_3_checked :
    (Witness.rising).check 47 41 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_41_4_checked :
    (Witness.rising).check 47 41 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_41_5_checked :
    (Witness.rising).check 47 41 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_41_6_checked :
    (Witness.rising).check 47 41 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_41_7_checked :
    (Witness.rising).check 47 41 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_41_8_checked :
    (Witness.rising).check 47 41 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_41_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_47_41_9_checked :
    (Witness.linear .positive case_47_41_9).check 47 41 9 = true := by
  change case_47_41_9.check 47 41 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_41_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_47_41_10_checked :
    (Witness.linear .positive case_47_41_10).check 47 41 10 = true := by
  change case_47_41_10.check 47 41 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_41_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_47_41_11_checked :
    (Witness.linear .positive case_47_41_11).check 47 41 11 = true := by
  change case_47_41_11.check 47 41 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_41_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_47_41_12_checked :
    (Witness.linear .positive case_47_41_12).check 47 41 12 = true := by
  change case_47_41_12.check 47 41 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_41_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_47_41_13_checked :
    (Witness.linear .positive case_47_41_13).check 47 41 13 = true := by
  change case_47_41_13.check 47 41 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_41_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429] }

theorem case_47_41_14_checked :
    (Witness.linear .positive case_47_41_14).check 47 41 14 = true := by
  change case_47_41_14.check 47 41 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_41_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430] }

theorem case_47_41_15_checked :
    (Witness.linear .positive case_47_41_15).check 47 41 15 = true := by
  change case_47_41_15.check 47 41 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_41_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862] }

theorem case_47_41_16_checked :
    (Witness.linear .positive case_47_41_16).check 47 41 16 = true := by
  change case_47_41_16.check 47 41 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_41_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796] }

theorem case_47_41_17_checked :
    (Witness.linear .positive case_47_41_17).check 47 41 17 = true := by
  change case_47_41_17.check 47 41 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_41_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_47_41_18_checked :
    (Witness.linear .positive case_47_41_18).check 47 41 18 = true := by
  change case_47_41_18.check 47 41 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_41_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_47_41_19_checked :
    (Witness.linear .positive case_47_41_19).check 47 41 19 = true := by
  change case_47_41_19.check 47 41 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_41_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_47_41_20_checked :
    (Witness.linear .positive case_47_41_20).check 47 41 20 = true := by
  change case_47_41_20.check 47 41 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_41_21 : Certificate := {
  objectiveScale := 19
  eta := 137088510
  rows := #[⟨.assumptionRow 21, 16⟩]
  caps := #[0, 0, 42791385, 15509130, 5311735, 1754555, 579989850] }

theorem case_47_41_21_checked :
    (Witness.linear .conditional case_47_41_21).check 47 41 21 = true := by
  change case_47_41_21.check 47 41 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_41_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 477638700, 477638700] }

theorem case_47_41_22_checked :
    (Witness.linear .negative case_47_41_22).check 47 41 22 = true := by
  change case_47_41_22.check 47 41 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_41_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_47_41_23_checked :
    (Witness.linear .negative case_47_41_23).check 47 41 23 = true := by
  change case_47_41_23.check 47 41 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_41_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_47_41_24_checked :
    (Witness.linear .negative case_47_41_24).check 47 41 24 = true := by
  change case_47_41_24.check 47 41 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_41_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_47_41_25_checked :
    (Witness.linear .negative case_47_41_25).check 47 41 25 = true := by
  change case_47_41_25.check 47 41 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_41_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_47_41_26_checked :
    (Witness.linear .negative case_47_41_26).check 47 41 26 = true := by
  change case_47_41_26.check 47 41 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_42_1_checked :
    (Witness.rising).check 47 42 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_42_2_checked :
    (Witness.rising).check 47 42 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_42_3_checked :
    (Witness.rising).check 47 42 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_42_4_checked :
    (Witness.rising).check 47 42 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_42_5_checked :
    (Witness.rising).check 47 42 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_42_6_checked :
    (Witness.rising).check 47 42 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_42_7_checked :
    (Witness.rising).check 47 42 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_42_8_checked :
    (Witness.rising).check 47 42 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_42_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_47_42_9_checked :
    (Witness.linear .positive case_47_42_9).check 47 42 9 = true := by
  change case_47_42_9.check 47 42 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_42_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_47_42_10_checked :
    (Witness.linear .positive case_47_42_10).check 47 42 10 = true := by
  change case_47_42_10.check 47 42 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_42_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_47_42_11_checked :
    (Witness.linear .positive case_47_42_11).check 47 42 11 = true := by
  change case_47_42_11.check 47 42 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_42_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_47_42_12_checked :
    (Witness.linear .positive case_47_42_12).check 47 42 12 = true := by
  change case_47_42_12.check 47 42 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_42_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_47_42_13_checked :
    (Witness.linear .positive case_47_42_13).check 47 42 13 = true := by
  change case_47_42_13.check 47 42 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_42_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_47_42_14_checked :
    (Witness.linear .positive case_47_42_14).check 47 42 14 = true := by
  change case_47_42_14.check 47 42 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_42_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862] }

theorem case_47_42_15_checked :
    (Witness.linear .positive case_47_42_15).check 47 42 15 = true := by
  change case_47_42_15.check 47 42 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_42_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796] }

theorem case_47_42_16_checked :
    (Witness.linear .positive case_47_42_16).check 47 42 16 = true := by
  change case_47_42_16.check 47 42 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_42_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786] }

theorem case_47_42_17_checked :
    (Witness.linear .positive case_47_42_17).check 47 42 17 = true := by
  change case_47_42_17.check 47 42 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_42_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012] }

theorem case_47_42_18_checked :
    (Witness.linear .positive case_47_42_18).check 47 42 18 = true := by
  change case_47_42_18.check 47 42 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_42_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900] }

theorem case_47_42_19_checked :
    (Witness.linear .positive case_47_42_19).check 47 42 19 = true := by
  change case_47_42_19.check 47 42 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_42_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440] }

theorem case_47_42_20_checked :
    (Witness.linear .positive case_47_42_20).check 47 42 20 = true := by
  change case_47_42_20.check 47 42 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_42_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845] }

theorem case_47_42_21_checked :
    (Witness.linear .positive case_47_42_21).check 47 42 21 = true := by
  change case_47_42_21.check 47 42 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_42_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 1767263190, 1767263190] }

theorem case_47_42_22_checked :
    (Witness.linear .negative case_47_42_22).check 47 42 22 = true := by
  change case_47_42_22.check 47 42 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_42_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_47_42_23_checked :
    (Witness.linear .negative case_47_42_23).check 47 42 23 = true := by
  change case_47_42_23.check 47 42 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_42_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_47_42_24_checked :
    (Witness.linear .negative case_47_42_24).check 47 42 24 = true := by
  change case_47_42_24.check 47 42 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_42_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_47_42_25_checked :
    (Witness.linear .negative case_47_42_25).check 47 42 25 = true := by
  change case_47_42_25.check 47 42 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_42_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_47_42_26_checked :
    (Witness.linear .negative case_47_42_26).check 47 42 26 = true := by
  change case_47_42_26.check 47 42 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_42_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_47_42_27_checked :
    (Witness.linear .negative case_47_42_27).check 47 42 27 = true := by
  change case_47_42_27.check 47 42 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_43_1_checked :
    (Witness.rising).check 47 43 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_43_2_checked :
    (Witness.rising).check 47 43 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_43_3_checked :
    (Witness.rising).check 47 43 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_43_4_checked :
    (Witness.rising).check 47 43 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_43_5_checked :
    (Witness.rising).check 47 43 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_43_6_checked :
    (Witness.rising).check 47 43 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_43_7_checked :
    (Witness.rising).check 47 43 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_43_8_checked :
    (Witness.rising).check 47 43 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_43_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_47_43_9_checked :
    (Witness.linear .positive case_47_43_9).check 47 43 9 = true := by
  change case_47_43_9.check 47 43 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_43_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_47_43_10_checked :
    (Witness.linear .positive case_47_43_10).check 47 43 10 = true := by
  change case_47_43_10.check 47 43 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_43_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_47_43_11_checked :
    (Witness.linear .positive case_47_43_11).check 47 43 11 = true := by
  change case_47_43_11.check 47 43 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_43_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_47_43_12_checked :
    (Witness.linear .positive case_47_43_12).check 47 43 12 = true := by
  change case_47_43_12.check 47 43 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_43_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_47_43_13_checked :
    (Witness.linear .positive case_47_43_13).check 47 43 13 = true := by
  change case_47_43_13.check 47 43 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_43_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_47_43_14_checked :
    (Witness.linear .positive case_47_43_14).check 47 43 14 = true := by
  change case_47_43_14.check 47 43 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_43_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796] }

theorem case_47_43_15_checked :
    (Witness.linear .positive case_47_43_15).check 47 43 15 = true := by
  change case_47_43_15.check 47 43 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_43_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786] }

theorem case_47_43_16_checked :
    (Witness.linear .positive case_47_43_16).check 47 43 16 = true := by
  change case_47_43_16.check 47 43 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_43_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012] }

theorem case_47_43_17_checked :
    (Witness.linear .positive case_47_43_17).check 47 43 17 = true := by
  change case_47_43_17.check 47 43 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_43_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900] }

theorem case_47_43_18_checked :
    (Witness.linear .positive case_47_43_18).check 47 43 18 = true := by
  change case_47_43_18.check 47 43 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_43_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440] }

theorem case_47_43_19_checked :
    (Witness.linear .positive case_47_43_19).check 47 43 19 = true := by
  change case_47_43_19.check 47 43 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_43_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845] }

theorem case_47_43_20_checked :
    (Witness.linear .positive case_47_43_20).check 47 43 20 = true := by
  change case_47_43_20.check 47 43 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_43_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670] }

theorem case_47_43_21_checked :
    (Witness.linear .positive case_47_43_21).check 47 43 21 = true := by
  change case_47_43_21.check 47 43 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_43_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 6564120420, 6564120420] }

theorem case_47_43_22_checked :
    (Witness.linear .negative case_47_43_22).check 47 43 22 = true := by
  change case_47_43_22.check 47 43 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_43_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_47_43_23_checked :
    (Witness.linear .negative case_47_43_23).check 47 43 23 = true := by
  change case_47_43_23.check 47 43 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_43_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_47_43_24_checked :
    (Witness.linear .negative case_47_43_24).check 47 43 24 = true := by
  change case_47_43_24.check 47 43 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_43_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_47_43_25_checked :
    (Witness.linear .negative case_47_43_25).check 47 43 25 = true := by
  change case_47_43_25.check 47 43 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_43_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_47_43_26_checked :
    (Witness.linear .negative case_47_43_26).check 47 43 26 = true := by
  change case_47_43_26.check 47 43 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_43_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_47_43_27_checked :
    (Witness.linear .negative case_47_43_27).check 47 43 27 = true := by
  change case_47_43_27.check 47 43 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_43_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_47_43_28_checked :
    (Witness.linear .negative case_47_43_28).check 47 43 28 = true := by
  change case_47_43_28.check 47 43 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_44_1_checked :
    (Witness.rising).check 47 44 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_44_2_checked :
    (Witness.rising).check 47 44 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_44_3_checked :
    (Witness.rising).check 47 44 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_44_4_checked :
    (Witness.rising).check 47 44 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_44_5_checked :
    (Witness.rising).check 47 44 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_44_6_checked :
    (Witness.rising).check 47 44 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_44_7_checked :
    (Witness.rising).check 47 44 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_44_8_checked :
    (Witness.rising).check 47 44 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_44_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_47_44_9_checked :
    (Witness.linear .positive case_47_44_9).check 47 44 9 = true := by
  change case_47_44_9.check 47 44 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_44_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_47_44_10_checked :
    (Witness.linear .positive case_47_44_10).check 47 44 10 = true := by
  change case_47_44_10.check 47 44 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_44_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_47_44_11_checked :
    (Witness.linear .positive case_47_44_11).check 47 44 11 = true := by
  change case_47_44_11.check 47 44 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_44_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_47_44_12_checked :
    (Witness.linear .positive case_47_44_12).check 47 44 12 = true := by
  change case_47_44_12.check 47 44 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_44_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_47_44_13_checked :
    (Witness.linear .positive case_47_44_13).check 47 44 13 = true := by
  change case_47_44_13.check 47 44 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_44_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_47_44_14_checked :
    (Witness.linear .positive case_47_44_14).check 47 44 14 = true := by
  change case_47_44_14.check 47 44 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_44_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_47_44_15_checked :
    (Witness.linear .positive case_47_44_15).check 47 44 15 = true := by
  change case_47_44_15.check 47 44 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_44_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012] }

theorem case_47_44_16_checked :
    (Witness.linear .positive case_47_44_16).check 47 44 16 = true := by
  change case_47_44_16.check 47 44 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_44_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900] }

theorem case_47_44_17_checked :
    (Witness.linear .positive case_47_44_17).check 47 44 17 = true := by
  change case_47_44_17.check 47 44 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_44_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440] }

theorem case_47_44_18_checked :
    (Witness.linear .positive case_47_44_18).check 47 44 18 = true := by
  change case_47_44_18.check 47 44 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_44_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845] }

theorem case_47_44_19_checked :
    (Witness.linear .positive case_47_44_19).check 47 44 19 = true := by
  change case_47_44_19.check 47 44 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_44_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670] }

theorem case_47_44_20_checked :
    (Witness.linear .positive case_47_44_20).check 47 44 20 = true := by
  change case_47_44_20.check 47 44 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_44_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790] }

theorem case_47_44_21_checked :
    (Witness.linear .positive case_47_44_21).check 47 44 21 = true := by
  change case_47_44_21.check 47 44 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_44_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700] }

theorem case_47_44_22_checked :
    (Witness.linear .positive case_47_44_22).check 47 44 22 = true := by
  change case_47_44_22.check 47 44 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_44_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_47_44_23_checked :
    (Witness.linear .negative case_47_44_23).check 47 44 23 = true := by
  change case_47_44_23.check 47 44 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_44_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_47_44_24_checked :
    (Witness.linear .negative case_47_44_24).check 47 44 24 = true := by
  change case_47_44_24.check 47 44 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_44_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_47_44_25_checked :
    (Witness.linear .negative case_47_44_25).check 47 44 25 = true := by
  change case_47_44_25.check 47 44 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_44_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_47_44_26_checked :
    (Witness.linear .negative case_47_44_26).check 47 44 26 = true := by
  change case_47_44_26.check 47 44 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_44_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_47_44_27_checked :
    (Witness.linear .negative case_47_44_27).check 47 44 27 = true := by
  change case_47_44_27.check 47 44 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_44_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_47_44_28_checked :
    (Witness.linear .negative case_47_44_28).check 47 44 28 = true := by
  change case_47_44_28.check 47 44 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_45_1_checked :
    (Witness.rising).check 47 45 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_45_2_checked :
    (Witness.rising).check 47 45 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_45_3_checked :
    (Witness.rising).check 47 45 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_45_4_checked :
    (Witness.rising).check 47 45 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_45_5_checked :
    (Witness.rising).check 47 45 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_45_6_checked :
    (Witness.rising).check 47 45 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_45_7_checked :
    (Witness.rising).check 47 45 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_45_8_checked :
    (Witness.rising).check 47 45 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_45_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_47_45_9_checked :
    (Witness.linear .positive case_47_45_9).check 47 45 9 = true := by
  change case_47_45_9.check 47 45 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_45_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_47_45_10_checked :
    (Witness.linear .positive case_47_45_10).check 47 45 10 = true := by
  change case_47_45_10.check 47 45 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_45_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_47_45_11_checked :
    (Witness.linear .positive case_47_45_11).check 47 45 11 = true := by
  change case_47_45_11.check 47 45 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_45_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_47_45_12_checked :
    (Witness.linear .positive case_47_45_12).check 47 45 12 = true := by
  change case_47_45_12.check 47 45 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_45_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_47_45_13_checked :
    (Witness.linear .positive case_47_45_13).check 47 45 13 = true := by
  change case_47_45_13.check 47 45 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_45_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_47_45_14_checked :
    (Witness.linear .positive case_47_45_14).check 47 45 14 = true := by
  change case_47_45_14.check 47 45 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_45_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_47_45_15_checked :
    (Witness.linear .positive case_47_45_15).check 47 45 15 = true := by
  change case_47_45_15.check 47 45 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_45_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900] }

theorem case_47_45_16_checked :
    (Witness.linear .positive case_47_45_16).check 47 45 16 = true := by
  change case_47_45_16.check 47 45 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_45_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440] }

theorem case_47_45_17_checked :
    (Witness.linear .positive case_47_45_17).check 47 45 17 = true := by
  change case_47_45_17.check 47 45 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_45_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845] }

theorem case_47_45_18_checked :
    (Witness.linear .positive case_47_45_18).check 47 45 18 = true := by
  change case_47_45_18.check 47 45 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_45_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670] }

theorem case_47_45_19_checked :
    (Witness.linear .positive case_47_45_19).check 47 45 19 = true := by
  change case_47_45_19.check 47 45 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_45_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790] }

theorem case_47_45_20_checked :
    (Witness.linear .positive case_47_45_20).check 47 45 20 = true := by
  change case_47_45_20.check 47 45 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_45_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700] }

theorem case_47_45_21_checked :
    (Witness.linear .positive case_47_45_21).check 47 45 21 = true := by
  change case_47_45_21.check 47 45 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_45_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190] }

theorem case_47_45_22_checked :
    (Witness.linear .positive case_47_45_22).check 47 45 22 = true := by
  change case_47_45_22.check 47 45 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_45_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_47_45_23_checked :
    (Witness.linear .negative case_47_45_23).check 47 45 23 = true := by
  change case_47_45_23.check 47 45 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_45_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_47_45_24_checked :
    (Witness.linear .negative case_47_45_24).check 47 45 24 = true := by
  change case_47_45_24.check 47 45 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_45_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_47_45_25_checked :
    (Witness.linear .negative case_47_45_25).check 47 45 25 = true := by
  change case_47_45_25.check 47 45 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_45_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_47_45_26_checked :
    (Witness.linear .negative case_47_45_26).check 47 45 26 = true := by
  change case_47_45_26.check 47 45 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_45_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_47_45_27_checked :
    (Witness.linear .negative case_47_45_27).check 47 45 27 = true := by
  change case_47_45_27.check 47 45 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_45_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_47_45_28_checked :
    (Witness.linear .negative case_47_45_28).check 47 45 28 = true := by
  change case_47_45_28.check 47 45 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_45_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_47_45_29_checked :
    (Witness.linear .negative case_47_45_29).check 47 45 29 = true := by
  change case_47_45_29.check 47 45 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_46_1_checked :
    (Witness.rising).check 47 46 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_46_2_checked :
    (Witness.rising).check 47 46 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_46_3_checked :
    (Witness.rising).check 47 46 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_46_4_checked :
    (Witness.rising).check 47 46 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_46_5_checked :
    (Witness.rising).check 47 46 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_46_6_checked :
    (Witness.rising).check 47 46 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_46_7_checked :
    (Witness.rising).check 47 46 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_47_46_8_checked :
    (Witness.rising).check 47 46 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_46_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_47_46_9_checked :
    (Witness.linear .positive case_47_46_9).check 47 46 9 = true := by
  change case_47_46_9.check 47 46 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_46_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_47_46_10_checked :
    (Witness.linear .positive case_47_46_10).check 47 46 10 = true := by
  change case_47_46_10.check 47 46 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_46_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_47_46_11_checked :
    (Witness.linear .positive case_47_46_11).check 47 46 11 = true := by
  change case_47_46_11.check 47 46 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_46_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_47_46_12_checked :
    (Witness.linear .positive case_47_46_12).check 47 46 12 = true := by
  change case_47_46_12.check 47 46 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_46_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_47_46_13_checked :
    (Witness.linear .positive case_47_46_13).check 47 46 13 = true := by
  change case_47_46_13.check 47 46 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_46_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_47_46_14_checked :
    (Witness.linear .positive case_47_46_14).check 47 46 14 = true := by
  change case_47_46_14.check 47 46 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_46_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_47_46_15_checked :
    (Witness.linear .positive case_47_46_15).check 47 46 15 = true := by
  change case_47_46_15.check 47 46 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_46_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_47_46_16_checked :
    (Witness.linear .positive case_47_46_16).check 47 46 16 = true := by
  change case_47_46_16.check 47 46 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_46_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0] }

theorem case_47_46_17_checked :
    (Witness.linear .positive case_47_46_17).check 47 46 17 = true := by
  change case_47_46_17.check 47 46 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_46_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0] }

theorem case_47_46_18_checked :
    (Witness.linear .positive case_47_46_18).check 47 46 18 = true := by
  change case_47_46_18.check 47 46 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_46_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0] }

theorem case_47_46_19_checked :
    (Witness.linear .positive case_47_46_19).check 47 46 19 = true := by
  change case_47_46_19.check 47 46 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_46_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0] }

theorem case_47_46_20_checked :
    (Witness.linear .positive case_47_46_20).check 47 46 20 = true := by
  change case_47_46_20.check 47 46 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_46_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0] }

theorem case_47_46_21_checked :
    (Witness.linear .positive case_47_46_21).check 47 46 21 = true := by
  change case_47_46_21.check 47 46 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_46_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0] }

theorem case_47_46_22_checked :
    (Witness.linear .positive case_47_46_22).check 47 46 22 = true := by
  change case_47_46_22.check 47 46 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_46_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0] }

theorem case_47_46_23_checked :
    (Witness.linear .positive case_47_46_23).check 47 46 23 = true := by
  change case_47_46_23.check 47 46 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_46_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_47_46_24_checked :
    (Witness.linear .negative case_47_46_24).check 47 46 24 = true := by
  change case_47_46_24.check 47 46 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_46_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_47_46_25_checked :
    (Witness.linear .negative case_47_46_25).check 47 46 25 = true := by
  change case_47_46_25.check 47 46 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_46_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_47_46_26_checked :
    (Witness.linear .negative case_47_46_26).check 47 46 26 = true := by
  change case_47_46_26.check 47 46 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_46_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_47_46_27_checked :
    (Witness.linear .negative case_47_46_27).check 47 46 27 = true := by
  change case_47_46_27.check 47 46 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_46_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_47_46_28_checked :
    (Witness.linear .negative case_47_46_28).check 47 46 28 = true := by
  change case_47_46_28.check 47 46 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_46_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_47_46_29_checked :
    (Witness.linear .negative case_47_46_29).check 47 46 29 = true := by
  change case_47_46_29.check 47 46 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_47_46_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_47_46_30_checked :
    (Witness.linear .negative case_47_46_30).check 47 46 30 = true := by
  change case_47_46_30.check 47 46 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_47 (a k : ℕ) (h : Domain 47 a k) :
    ∃ w : Witness, w.check 47 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 24 ≤ a := by omega
  have haHi : a ≤ 46 := by omega
  interval_cases a

  · have hkHi : k ≤ 15 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_47_24_1_checked⟩

    · exact ⟨Witness.rising, case_47_24_2_checked⟩

    · exact ⟨Witness.rising, case_47_24_3_checked⟩

    · exact ⟨Witness.rising, case_47_24_4_checked⟩

    · exact ⟨Witness.rising, case_47_24_5_checked⟩

    · exact ⟨Witness.rising, case_47_24_6_checked⟩

    · exact ⟨Witness.rising, case_47_24_7_checked⟩

    · exact ⟨Witness.rising, case_47_24_8_checked⟩

    · exact ⟨Witness.rising, case_47_24_9_checked⟩

    · exact ⟨Witness.linear .positive case_47_24_10, case_47_24_10_checked⟩

    · exact ⟨Witness.linear .positive case_47_24_11, case_47_24_11_checked⟩

    · exact ⟨Witness.linear .positive case_47_24_12, case_47_24_12_checked⟩

    · exact ⟨Witness.linear .positive case_47_24_13, case_47_24_13_checked⟩

    · exact ⟨Witness.linear .conditional case_47_24_14, case_47_24_14_checked⟩

    · exact ⟨Witness.linear .conditional case_47_24_15, case_47_24_15_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_47_25_1_checked⟩

    · exact ⟨Witness.rising, case_47_25_2_checked⟩

    · exact ⟨Witness.rising, case_47_25_3_checked⟩

    · exact ⟨Witness.rising, case_47_25_4_checked⟩

    · exact ⟨Witness.rising, case_47_25_5_checked⟩

    · exact ⟨Witness.rising, case_47_25_6_checked⟩

    · exact ⟨Witness.rising, case_47_25_7_checked⟩

    · exact ⟨Witness.rising, case_47_25_8_checked⟩

    · exact ⟨Witness.rising, case_47_25_9_checked⟩

    · exact ⟨Witness.linear .positive case_47_25_10, case_47_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_47_25_11, case_47_25_11_checked⟩

    · exact ⟨Witness.linear .positive case_47_25_12, case_47_25_12_checked⟩

    · exact ⟨Witness.linear .positive case_47_25_13, case_47_25_13_checked⟩

    · exact ⟨Witness.linear .conditional case_47_25_14, case_47_25_14_checked⟩

    · exact ⟨Witness.linear .conditional case_47_25_15, case_47_25_15_checked⟩

    · exact ⟨Witness.linear .conditional case_47_25_16, case_47_25_16_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_47_26_1_checked⟩

    · exact ⟨Witness.rising, case_47_26_2_checked⟩

    · exact ⟨Witness.rising, case_47_26_3_checked⟩

    · exact ⟨Witness.rising, case_47_26_4_checked⟩

    · exact ⟨Witness.rising, case_47_26_5_checked⟩

    · exact ⟨Witness.rising, case_47_26_6_checked⟩

    · exact ⟨Witness.rising, case_47_26_7_checked⟩

    · exact ⟨Witness.rising, case_47_26_8_checked⟩

    · exact ⟨Witness.rising, case_47_26_9_checked⟩

    · exact ⟨Witness.linear .positive case_47_26_10, case_47_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_47_26_11, case_47_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_47_26_12, case_47_26_12_checked⟩

    · exact ⟨Witness.linear .positive case_47_26_13, case_47_26_13_checked⟩

    · exact ⟨Witness.linear .conditional case_47_26_14, case_47_26_14_checked⟩

    · exact ⟨Witness.linear .conditional case_47_26_15, case_47_26_15_checked⟩

    · exact ⟨Witness.linear .conditional case_47_26_16, case_47_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_47_27_1_checked⟩

    · exact ⟨Witness.rising, case_47_27_2_checked⟩

    · exact ⟨Witness.rising, case_47_27_3_checked⟩

    · exact ⟨Witness.rising, case_47_27_4_checked⟩

    · exact ⟨Witness.rising, case_47_27_5_checked⟩

    · exact ⟨Witness.rising, case_47_27_6_checked⟩

    · exact ⟨Witness.rising, case_47_27_7_checked⟩

    · exact ⟨Witness.rising, case_47_27_8_checked⟩

    · exact ⟨Witness.rising, case_47_27_9_checked⟩

    · exact ⟨Witness.linear .positive case_47_27_10, case_47_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_47_27_11, case_47_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_47_27_12, case_47_27_12_checked⟩

    · exact ⟨Witness.linear .positive case_47_27_13, case_47_27_13_checked⟩

    · exact ⟨Witness.linear .conditional case_47_27_14, case_47_27_14_checked⟩

    · exact ⟨Witness.linear .conditional case_47_27_15, case_47_27_15_checked⟩

    · exact ⟨Witness.linear .conditional case_47_27_16, case_47_27_16_checked⟩

    · exact ⟨Witness.linear .negative case_47_27_17, case_47_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_47_28_1_checked⟩

    · exact ⟨Witness.rising, case_47_28_2_checked⟩

    · exact ⟨Witness.rising, case_47_28_3_checked⟩

    · exact ⟨Witness.rising, case_47_28_4_checked⟩

    · exact ⟨Witness.rising, case_47_28_5_checked⟩

    · exact ⟨Witness.rising, case_47_28_6_checked⟩

    · exact ⟨Witness.rising, case_47_28_7_checked⟩

    · exact ⟨Witness.rising, case_47_28_8_checked⟩

    · exact ⟨Witness.rising, case_47_28_9_checked⟩

    · exact ⟨Witness.linear .positive case_47_28_10, case_47_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_47_28_11, case_47_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_47_28_12, case_47_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_47_28_13, case_47_28_13_checked⟩

    · exact ⟨Witness.linear .conditional case_47_28_14, case_47_28_14_checked⟩

    · exact ⟨Witness.linear .conditional case_47_28_15, case_47_28_15_checked⟩

    · exact ⟨Witness.linear .conditional case_47_28_16, case_47_28_16_checked⟩

    · exact ⟨Witness.linear .conditional case_47_28_17, case_47_28_17_checked⟩

    · exact ⟨Witness.linear .negative case_47_28_18, case_47_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_47_29_1_checked⟩

    · exact ⟨Witness.rising, case_47_29_2_checked⟩

    · exact ⟨Witness.rising, case_47_29_3_checked⟩

    · exact ⟨Witness.rising, case_47_29_4_checked⟩

    · exact ⟨Witness.rising, case_47_29_5_checked⟩

    · exact ⟨Witness.rising, case_47_29_6_checked⟩

    · exact ⟨Witness.rising, case_47_29_7_checked⟩

    · exact ⟨Witness.rising, case_47_29_8_checked⟩

    · exact ⟨Witness.rising, case_47_29_9_checked⟩

    · exact ⟨Witness.linear .positive case_47_29_10, case_47_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_47_29_11, case_47_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_47_29_12, case_47_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_47_29_13, case_47_29_13_checked⟩

    · exact ⟨Witness.linear .positive case_47_29_14, case_47_29_14_checked⟩

    · exact ⟨Witness.linear .conditional case_47_29_15, case_47_29_15_checked⟩

    · exact ⟨Witness.linear .conditional case_47_29_16, case_47_29_16_checked⟩

    · exact ⟨Witness.linear .conditional case_47_29_17, case_47_29_17_checked⟩

    · exact ⟨Witness.linear .negative case_47_29_18, case_47_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_47_30_1_checked⟩

    · exact ⟨Witness.rising, case_47_30_2_checked⟩

    · exact ⟨Witness.rising, case_47_30_3_checked⟩

    · exact ⟨Witness.rising, case_47_30_4_checked⟩

    · exact ⟨Witness.rising, case_47_30_5_checked⟩

    · exact ⟨Witness.rising, case_47_30_6_checked⟩

    · exact ⟨Witness.rising, case_47_30_7_checked⟩

    · exact ⟨Witness.rising, case_47_30_8_checked⟩

    · exact ⟨Witness.rising, case_47_30_9_checked⟩

    · exact ⟨Witness.linear .positive case_47_30_10, case_47_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_47_30_11, case_47_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_47_30_12, case_47_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_47_30_13, case_47_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_47_30_14, case_47_30_14_checked⟩

    · exact ⟨Witness.linear .conditional case_47_30_15, case_47_30_15_checked⟩

    · exact ⟨Witness.linear .conditional case_47_30_16, case_47_30_16_checked⟩

    · exact ⟨Witness.linear .conditional case_47_30_17, case_47_30_17_checked⟩

    · exact ⟨Witness.linear .negative case_47_30_18, case_47_30_18_checked⟩

    · exact ⟨Witness.linear .negative case_47_30_19, case_47_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_47_31_1_checked⟩

    · exact ⟨Witness.rising, case_47_31_2_checked⟩

    · exact ⟨Witness.rising, case_47_31_3_checked⟩

    · exact ⟨Witness.rising, case_47_31_4_checked⟩

    · exact ⟨Witness.rising, case_47_31_5_checked⟩

    · exact ⟨Witness.rising, case_47_31_6_checked⟩

    · exact ⟨Witness.rising, case_47_31_7_checked⟩

    · exact ⟨Witness.rising, case_47_31_8_checked⟩

    · exact ⟨Witness.rising, case_47_31_9_checked⟩

    · exact ⟨Witness.linear .positive case_47_31_10, case_47_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_47_31_11, case_47_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_47_31_12, case_47_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_47_31_13, case_47_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_47_31_14, case_47_31_14_checked⟩

    · exact ⟨Witness.linear .positive case_47_31_15, case_47_31_15_checked⟩

    · exact ⟨Witness.linear .conditional case_47_31_16, case_47_31_16_checked⟩

    · exact ⟨Witness.linear .conditional case_47_31_17, case_47_31_17_checked⟩

    · exact ⟨Witness.linear .conditional case_47_31_18, case_47_31_18_checked⟩

    · exact ⟨Witness.linear .negative case_47_31_19, case_47_31_19_checked⟩

    · exact ⟨Witness.linear .negative case_47_31_20, case_47_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_47_32_1_checked⟩

    · exact ⟨Witness.rising, case_47_32_2_checked⟩

    · exact ⟨Witness.rising, case_47_32_3_checked⟩

    · exact ⟨Witness.rising, case_47_32_4_checked⟩

    · exact ⟨Witness.rising, case_47_32_5_checked⟩

    · exact ⟨Witness.rising, case_47_32_6_checked⟩

    · exact ⟨Witness.rising, case_47_32_7_checked⟩

    · exact ⟨Witness.rising, case_47_32_8_checked⟩

    · exact ⟨Witness.rising, case_47_32_9_checked⟩

    · exact ⟨Witness.linear .positive case_47_32_10, case_47_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_47_32_11, case_47_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_47_32_12, case_47_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_47_32_13, case_47_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_47_32_14, case_47_32_14_checked⟩

    · exact ⟨Witness.linear .conditional case_47_32_15, case_47_32_15_checked⟩

    · exact ⟨Witness.linear .conditional case_47_32_16, case_47_32_16_checked⟩

    · exact ⟨Witness.linear .conditional case_47_32_17, case_47_32_17_checked⟩

    · exact ⟨Witness.linear .conditional case_47_32_18, case_47_32_18_checked⟩

    · exact ⟨Witness.linear .negative case_47_32_19, case_47_32_19_checked⟩

    · exact ⟨Witness.linear .conditional case_47_32_20, case_47_32_20_checked⟩

  · have hkHi : k ≤ 21 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_47_33_1_checked⟩

    · exact ⟨Witness.rising, case_47_33_2_checked⟩

    · exact ⟨Witness.rising, case_47_33_3_checked⟩

    · exact ⟨Witness.rising, case_47_33_4_checked⟩

    · exact ⟨Witness.rising, case_47_33_5_checked⟩

    · exact ⟨Witness.rising, case_47_33_6_checked⟩

    · exact ⟨Witness.rising, case_47_33_7_checked⟩

    · exact ⟨Witness.rising, case_47_33_8_checked⟩

    · exact ⟨Witness.rising, case_47_33_9_checked⟩

    · exact ⟨Witness.linear .positive case_47_33_10, case_47_33_10_checked⟩

    · exact ⟨Witness.linear .positive case_47_33_11, case_47_33_11_checked⟩

    · exact ⟨Witness.linear .positive case_47_33_12, case_47_33_12_checked⟩

    · exact ⟨Witness.linear .positive case_47_33_13, case_47_33_13_checked⟩

    · exact ⟨Witness.linear .positive case_47_33_14, case_47_33_14_checked⟩

    · exact ⟨Witness.linear .positive case_47_33_15, case_47_33_15_checked⟩

    · exact ⟨Witness.linear .conditional case_47_33_16, case_47_33_16_checked⟩

    · exact ⟨Witness.linear .conditional case_47_33_17, case_47_33_17_checked⟩

    · exact ⟨Witness.linear .conditional case_47_33_18, case_47_33_18_checked⟩

    · exact ⟨Witness.linear .negative case_47_33_19, case_47_33_19_checked⟩

    · exact ⟨Witness.linear .conditional case_47_33_20, case_47_33_20_checked⟩

    · exact ⟨Witness.linear .negative case_47_33_21, case_47_33_21_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_47_34_1_checked⟩

    · exact ⟨Witness.rising, case_47_34_2_checked⟩

    · exact ⟨Witness.rising, case_47_34_3_checked⟩

    · exact ⟨Witness.rising, case_47_34_4_checked⟩

    · exact ⟨Witness.rising, case_47_34_5_checked⟩

    · exact ⟨Witness.rising, case_47_34_6_checked⟩

    · exact ⟨Witness.rising, case_47_34_7_checked⟩

    · exact ⟨Witness.rising, case_47_34_8_checked⟩

    · exact ⟨Witness.linear .positive case_47_34_9, case_47_34_9_checked⟩

    · exact ⟨Witness.linear .positive case_47_34_10, case_47_34_10_checked⟩

    · exact ⟨Witness.linear .positive case_47_34_11, case_47_34_11_checked⟩

    · exact ⟨Witness.linear .positive case_47_34_12, case_47_34_12_checked⟩

    · exact ⟨Witness.linear .positive case_47_34_13, case_47_34_13_checked⟩

    · exact ⟨Witness.linear .positive case_47_34_14, case_47_34_14_checked⟩

    · exact ⟨Witness.linear .positive case_47_34_15, case_47_34_15_checked⟩

    · exact ⟨Witness.linear .positive case_47_34_16, case_47_34_16_checked⟩

    · exact ⟨Witness.linear .conditional case_47_34_17, case_47_34_17_checked⟩

    · exact ⟨Witness.linear .conditional case_47_34_18, case_47_34_18_checked⟩

    · exact ⟨Witness.linear .negative case_47_34_19, case_47_34_19_checked⟩

    · exact ⟨Witness.linear .conditional case_47_34_20, case_47_34_20_checked⟩

    · exact ⟨Witness.linear .negative case_47_34_21, case_47_34_21_checked⟩

    · exact ⟨Witness.linear .negative case_47_34_22, case_47_34_22_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_47_35_1_checked⟩

    · exact ⟨Witness.rising, case_47_35_2_checked⟩

    · exact ⟨Witness.rising, case_47_35_3_checked⟩

    · exact ⟨Witness.rising, case_47_35_4_checked⟩

    · exact ⟨Witness.rising, case_47_35_5_checked⟩

    · exact ⟨Witness.rising, case_47_35_6_checked⟩

    · exact ⟨Witness.rising, case_47_35_7_checked⟩

    · exact ⟨Witness.rising, case_47_35_8_checked⟩

    · exact ⟨Witness.linear .positive case_47_35_9, case_47_35_9_checked⟩

    · exact ⟨Witness.linear .positive case_47_35_10, case_47_35_10_checked⟩

    · exact ⟨Witness.linear .positive case_47_35_11, case_47_35_11_checked⟩

    · exact ⟨Witness.linear .positive case_47_35_12, case_47_35_12_checked⟩

    · exact ⟨Witness.linear .positive case_47_35_13, case_47_35_13_checked⟩

    · exact ⟨Witness.linear .positive case_47_35_14, case_47_35_14_checked⟩

    · exact ⟨Witness.linear .positive case_47_35_15, case_47_35_15_checked⟩

    · exact ⟨Witness.linear .positive case_47_35_16, case_47_35_16_checked⟩

    · exact ⟨Witness.linear .conditional case_47_35_17, case_47_35_17_checked⟩

    · exact ⟨Witness.linear .conditional case_47_35_18, case_47_35_18_checked⟩

    · exact ⟨Witness.linear .conditional case_47_35_19, case_47_35_19_checked⟩

    · exact ⟨Witness.linear .conditional case_47_35_20, case_47_35_20_checked⟩

    · exact ⟨Witness.linear .negative case_47_35_21, case_47_35_21_checked⟩

    · exact ⟨Witness.linear .negative case_47_35_22, case_47_35_22_checked⟩

  · have hkHi : k ≤ 23 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_47_36_1_checked⟩

    · exact ⟨Witness.rising, case_47_36_2_checked⟩

    · exact ⟨Witness.rising, case_47_36_3_checked⟩

    · exact ⟨Witness.rising, case_47_36_4_checked⟩

    · exact ⟨Witness.rising, case_47_36_5_checked⟩

    · exact ⟨Witness.rising, case_47_36_6_checked⟩

    · exact ⟨Witness.rising, case_47_36_7_checked⟩

    · exact ⟨Witness.rising, case_47_36_8_checked⟩

    · exact ⟨Witness.linear .positive case_47_36_9, case_47_36_9_checked⟩

    · exact ⟨Witness.linear .positive case_47_36_10, case_47_36_10_checked⟩

    · exact ⟨Witness.linear .positive case_47_36_11, case_47_36_11_checked⟩

    · exact ⟨Witness.linear .positive case_47_36_12, case_47_36_12_checked⟩

    · exact ⟨Witness.linear .positive case_47_36_13, case_47_36_13_checked⟩

    · exact ⟨Witness.linear .positive case_47_36_14, case_47_36_14_checked⟩

    · exact ⟨Witness.linear .positive case_47_36_15, case_47_36_15_checked⟩

    · exact ⟨Witness.linear .positive case_47_36_16, case_47_36_16_checked⟩

    · exact ⟨Witness.linear .positive case_47_36_17, case_47_36_17_checked⟩

    · exact ⟨Witness.linear .conditional case_47_36_18, case_47_36_18_checked⟩

    · exact ⟨Witness.linear .conditional case_47_36_19, case_47_36_19_checked⟩

    · exact ⟨Witness.linear .conditional case_47_36_20, case_47_36_20_checked⟩

    · exact ⟨Witness.linear .negative case_47_36_21, case_47_36_21_checked⟩

    · exact ⟨Witness.linear .negative case_47_36_22, case_47_36_22_checked⟩

    · exact ⟨Witness.linear .negative case_47_36_23, case_47_36_23_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_47_37_1_checked⟩

    · exact ⟨Witness.rising, case_47_37_2_checked⟩

    · exact ⟨Witness.rising, case_47_37_3_checked⟩

    · exact ⟨Witness.rising, case_47_37_4_checked⟩

    · exact ⟨Witness.rising, case_47_37_5_checked⟩

    · exact ⟨Witness.rising, case_47_37_6_checked⟩

    · exact ⟨Witness.rising, case_47_37_7_checked⟩

    · exact ⟨Witness.rising, case_47_37_8_checked⟩

    · exact ⟨Witness.linear .positive case_47_37_9, case_47_37_9_checked⟩

    · exact ⟨Witness.linear .positive case_47_37_10, case_47_37_10_checked⟩

    · exact ⟨Witness.linear .positive case_47_37_11, case_47_37_11_checked⟩

    · exact ⟨Witness.linear .positive case_47_37_12, case_47_37_12_checked⟩

    · exact ⟨Witness.linear .positive case_47_37_13, case_47_37_13_checked⟩

    · exact ⟨Witness.linear .positive case_47_37_14, case_47_37_14_checked⟩

    · exact ⟨Witness.linear .positive case_47_37_15, case_47_37_15_checked⟩

    · exact ⟨Witness.linear .positive case_47_37_16, case_47_37_16_checked⟩

    · exact ⟨Witness.linear .positive case_47_37_17, case_47_37_17_checked⟩

    · exact ⟨Witness.linear .positive case_47_37_18, case_47_37_18_checked⟩

    · exact ⟨Witness.linear .conditional case_47_37_19, case_47_37_19_checked⟩

    · exact ⟨Witness.linear .conditional case_47_37_20, case_47_37_20_checked⟩

    · exact ⟨Witness.linear .negative case_47_37_21, case_47_37_21_checked⟩

    · exact ⟨Witness.linear .negative case_47_37_22, case_47_37_22_checked⟩

    · exact ⟨Witness.linear .negative case_47_37_23, case_47_37_23_checked⟩

    · exact ⟨Witness.linear .negative case_47_37_24, case_47_37_24_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_47_38_1_checked⟩

    · exact ⟨Witness.rising, case_47_38_2_checked⟩

    · exact ⟨Witness.rising, case_47_38_3_checked⟩

    · exact ⟨Witness.rising, case_47_38_4_checked⟩

    · exact ⟨Witness.rising, case_47_38_5_checked⟩

    · exact ⟨Witness.rising, case_47_38_6_checked⟩

    · exact ⟨Witness.rising, case_47_38_7_checked⟩

    · exact ⟨Witness.rising, case_47_38_8_checked⟩

    · exact ⟨Witness.linear .positive case_47_38_9, case_47_38_9_checked⟩

    · exact ⟨Witness.linear .positive case_47_38_10, case_47_38_10_checked⟩

    · exact ⟨Witness.linear .positive case_47_38_11, case_47_38_11_checked⟩

    · exact ⟨Witness.linear .positive case_47_38_12, case_47_38_12_checked⟩

    · exact ⟨Witness.linear .positive case_47_38_13, case_47_38_13_checked⟩

    · exact ⟨Witness.linear .positive case_47_38_14, case_47_38_14_checked⟩

    · exact ⟨Witness.linear .positive case_47_38_15, case_47_38_15_checked⟩

    · exact ⟨Witness.linear .positive case_47_38_16, case_47_38_16_checked⟩

    · exact ⟨Witness.linear .positive case_47_38_17, case_47_38_17_checked⟩

    · exact ⟨Witness.linear .positive case_47_38_18, case_47_38_18_checked⟩

    · exact ⟨Witness.linear .conditional case_47_38_19, case_47_38_19_checked⟩

    · exact ⟨Witness.linear .conditional case_47_38_20, case_47_38_20_checked⟩

    · exact ⟨Witness.linear .negative case_47_38_21, case_47_38_21_checked⟩

    · exact ⟨Witness.linear .negative case_47_38_22, case_47_38_22_checked⟩

    · exact ⟨Witness.linear .negative case_47_38_23, case_47_38_23_checked⟩

    · exact ⟨Witness.linear .negative case_47_38_24, case_47_38_24_checked⟩

  · have hkHi : k ≤ 25 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_47_39_1_checked⟩

    · exact ⟨Witness.rising, case_47_39_2_checked⟩

    · exact ⟨Witness.rising, case_47_39_3_checked⟩

    · exact ⟨Witness.rising, case_47_39_4_checked⟩

    · exact ⟨Witness.rising, case_47_39_5_checked⟩

    · exact ⟨Witness.rising, case_47_39_6_checked⟩

    · exact ⟨Witness.rising, case_47_39_7_checked⟩

    · exact ⟨Witness.rising, case_47_39_8_checked⟩

    · exact ⟨Witness.linear .positive case_47_39_9, case_47_39_9_checked⟩

    · exact ⟨Witness.linear .positive case_47_39_10, case_47_39_10_checked⟩

    · exact ⟨Witness.linear .positive case_47_39_11, case_47_39_11_checked⟩

    · exact ⟨Witness.linear .positive case_47_39_12, case_47_39_12_checked⟩

    · exact ⟨Witness.linear .positive case_47_39_13, case_47_39_13_checked⟩

    · exact ⟨Witness.linear .positive case_47_39_14, case_47_39_14_checked⟩

    · exact ⟨Witness.linear .positive case_47_39_15, case_47_39_15_checked⟩

    · exact ⟨Witness.linear .positive case_47_39_16, case_47_39_16_checked⟩

    · exact ⟨Witness.linear .positive case_47_39_17, case_47_39_17_checked⟩

    · exact ⟨Witness.linear .positive case_47_39_18, case_47_39_18_checked⟩

    · exact ⟨Witness.linear .positive case_47_39_19, case_47_39_19_checked⟩

    · exact ⟨Witness.linear .conditional case_47_39_20, case_47_39_20_checked⟩

    · exact ⟨Witness.linear .conditional case_47_39_21, case_47_39_21_checked⟩

    · exact ⟨Witness.linear .negative case_47_39_22, case_47_39_22_checked⟩

    · exact ⟨Witness.linear .negative case_47_39_23, case_47_39_23_checked⟩

    · exact ⟨Witness.linear .negative case_47_39_24, case_47_39_24_checked⟩

    · exact ⟨Witness.linear .negative case_47_39_25, case_47_39_25_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_47_40_1_checked⟩

    · exact ⟨Witness.rising, case_47_40_2_checked⟩

    · exact ⟨Witness.rising, case_47_40_3_checked⟩

    · exact ⟨Witness.rising, case_47_40_4_checked⟩

    · exact ⟨Witness.rising, case_47_40_5_checked⟩

    · exact ⟨Witness.rising, case_47_40_6_checked⟩

    · exact ⟨Witness.rising, case_47_40_7_checked⟩

    · exact ⟨Witness.rising, case_47_40_8_checked⟩

    · exact ⟨Witness.linear .positive case_47_40_9, case_47_40_9_checked⟩

    · exact ⟨Witness.linear .positive case_47_40_10, case_47_40_10_checked⟩

    · exact ⟨Witness.linear .positive case_47_40_11, case_47_40_11_checked⟩

    · exact ⟨Witness.linear .positive case_47_40_12, case_47_40_12_checked⟩

    · exact ⟨Witness.linear .positive case_47_40_13, case_47_40_13_checked⟩

    · exact ⟨Witness.linear .positive case_47_40_14, case_47_40_14_checked⟩

    · exact ⟨Witness.linear .positive case_47_40_15, case_47_40_15_checked⟩

    · exact ⟨Witness.linear .positive case_47_40_16, case_47_40_16_checked⟩

    · exact ⟨Witness.linear .positive case_47_40_17, case_47_40_17_checked⟩

    · exact ⟨Witness.linear .positive case_47_40_18, case_47_40_18_checked⟩

    · exact ⟨Witness.linear .positive case_47_40_19, case_47_40_19_checked⟩

    · exact ⟨Witness.linear .conditional case_47_40_20, case_47_40_20_checked⟩

    · exact ⟨Witness.linear .conditional case_47_40_21, case_47_40_21_checked⟩

    · exact ⟨Witness.linear .negative case_47_40_22, case_47_40_22_checked⟩

    · exact ⟨Witness.linear .negative case_47_40_23, case_47_40_23_checked⟩

    · exact ⟨Witness.linear .negative case_47_40_24, case_47_40_24_checked⟩

    · exact ⟨Witness.linear .negative case_47_40_25, case_47_40_25_checked⟩

    · exact ⟨Witness.linear .negative case_47_40_26, case_47_40_26_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_47_41_1_checked⟩

    · exact ⟨Witness.rising, case_47_41_2_checked⟩

    · exact ⟨Witness.rising, case_47_41_3_checked⟩

    · exact ⟨Witness.rising, case_47_41_4_checked⟩

    · exact ⟨Witness.rising, case_47_41_5_checked⟩

    · exact ⟨Witness.rising, case_47_41_6_checked⟩

    · exact ⟨Witness.rising, case_47_41_7_checked⟩

    · exact ⟨Witness.rising, case_47_41_8_checked⟩

    · exact ⟨Witness.linear .positive case_47_41_9, case_47_41_9_checked⟩

    · exact ⟨Witness.linear .positive case_47_41_10, case_47_41_10_checked⟩

    · exact ⟨Witness.linear .positive case_47_41_11, case_47_41_11_checked⟩

    · exact ⟨Witness.linear .positive case_47_41_12, case_47_41_12_checked⟩

    · exact ⟨Witness.linear .positive case_47_41_13, case_47_41_13_checked⟩

    · exact ⟨Witness.linear .positive case_47_41_14, case_47_41_14_checked⟩

    · exact ⟨Witness.linear .positive case_47_41_15, case_47_41_15_checked⟩

    · exact ⟨Witness.linear .positive case_47_41_16, case_47_41_16_checked⟩

    · exact ⟨Witness.linear .positive case_47_41_17, case_47_41_17_checked⟩

    · exact ⟨Witness.linear .positive case_47_41_18, case_47_41_18_checked⟩

    · exact ⟨Witness.linear .positive case_47_41_19, case_47_41_19_checked⟩

    · exact ⟨Witness.linear .positive case_47_41_20, case_47_41_20_checked⟩

    · exact ⟨Witness.linear .conditional case_47_41_21, case_47_41_21_checked⟩

    · exact ⟨Witness.linear .negative case_47_41_22, case_47_41_22_checked⟩

    · exact ⟨Witness.linear .negative case_47_41_23, case_47_41_23_checked⟩

    · exact ⟨Witness.linear .negative case_47_41_24, case_47_41_24_checked⟩

    · exact ⟨Witness.linear .negative case_47_41_25, case_47_41_25_checked⟩

    · exact ⟨Witness.linear .negative case_47_41_26, case_47_41_26_checked⟩

  · have hkHi : k ≤ 27 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_47_42_1_checked⟩

    · exact ⟨Witness.rising, case_47_42_2_checked⟩

    · exact ⟨Witness.rising, case_47_42_3_checked⟩

    · exact ⟨Witness.rising, case_47_42_4_checked⟩

    · exact ⟨Witness.rising, case_47_42_5_checked⟩

    · exact ⟨Witness.rising, case_47_42_6_checked⟩

    · exact ⟨Witness.rising, case_47_42_7_checked⟩

    · exact ⟨Witness.rising, case_47_42_8_checked⟩

    · exact ⟨Witness.linear .positive case_47_42_9, case_47_42_9_checked⟩

    · exact ⟨Witness.linear .positive case_47_42_10, case_47_42_10_checked⟩

    · exact ⟨Witness.linear .positive case_47_42_11, case_47_42_11_checked⟩

    · exact ⟨Witness.linear .positive case_47_42_12, case_47_42_12_checked⟩

    · exact ⟨Witness.linear .positive case_47_42_13, case_47_42_13_checked⟩

    · exact ⟨Witness.linear .positive case_47_42_14, case_47_42_14_checked⟩

    · exact ⟨Witness.linear .positive case_47_42_15, case_47_42_15_checked⟩

    · exact ⟨Witness.linear .positive case_47_42_16, case_47_42_16_checked⟩

    · exact ⟨Witness.linear .positive case_47_42_17, case_47_42_17_checked⟩

    · exact ⟨Witness.linear .positive case_47_42_18, case_47_42_18_checked⟩

    · exact ⟨Witness.linear .positive case_47_42_19, case_47_42_19_checked⟩

    · exact ⟨Witness.linear .positive case_47_42_20, case_47_42_20_checked⟩

    · exact ⟨Witness.linear .positive case_47_42_21, case_47_42_21_checked⟩

    · exact ⟨Witness.linear .negative case_47_42_22, case_47_42_22_checked⟩

    · exact ⟨Witness.linear .negative case_47_42_23, case_47_42_23_checked⟩

    · exact ⟨Witness.linear .negative case_47_42_24, case_47_42_24_checked⟩

    · exact ⟨Witness.linear .negative case_47_42_25, case_47_42_25_checked⟩

    · exact ⟨Witness.linear .negative case_47_42_26, case_47_42_26_checked⟩

    · exact ⟨Witness.linear .negative case_47_42_27, case_47_42_27_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_47_43_1_checked⟩

    · exact ⟨Witness.rising, case_47_43_2_checked⟩

    · exact ⟨Witness.rising, case_47_43_3_checked⟩

    · exact ⟨Witness.rising, case_47_43_4_checked⟩

    · exact ⟨Witness.rising, case_47_43_5_checked⟩

    · exact ⟨Witness.rising, case_47_43_6_checked⟩

    · exact ⟨Witness.rising, case_47_43_7_checked⟩

    · exact ⟨Witness.rising, case_47_43_8_checked⟩

    · exact ⟨Witness.linear .positive case_47_43_9, case_47_43_9_checked⟩

    · exact ⟨Witness.linear .positive case_47_43_10, case_47_43_10_checked⟩

    · exact ⟨Witness.linear .positive case_47_43_11, case_47_43_11_checked⟩

    · exact ⟨Witness.linear .positive case_47_43_12, case_47_43_12_checked⟩

    · exact ⟨Witness.linear .positive case_47_43_13, case_47_43_13_checked⟩

    · exact ⟨Witness.linear .positive case_47_43_14, case_47_43_14_checked⟩

    · exact ⟨Witness.linear .positive case_47_43_15, case_47_43_15_checked⟩

    · exact ⟨Witness.linear .positive case_47_43_16, case_47_43_16_checked⟩

    · exact ⟨Witness.linear .positive case_47_43_17, case_47_43_17_checked⟩

    · exact ⟨Witness.linear .positive case_47_43_18, case_47_43_18_checked⟩

    · exact ⟨Witness.linear .positive case_47_43_19, case_47_43_19_checked⟩

    · exact ⟨Witness.linear .positive case_47_43_20, case_47_43_20_checked⟩

    · exact ⟨Witness.linear .positive case_47_43_21, case_47_43_21_checked⟩

    · exact ⟨Witness.linear .negative case_47_43_22, case_47_43_22_checked⟩

    · exact ⟨Witness.linear .negative case_47_43_23, case_47_43_23_checked⟩

    · exact ⟨Witness.linear .negative case_47_43_24, case_47_43_24_checked⟩

    · exact ⟨Witness.linear .negative case_47_43_25, case_47_43_25_checked⟩

    · exact ⟨Witness.linear .negative case_47_43_26, case_47_43_26_checked⟩

    · exact ⟨Witness.linear .negative case_47_43_27, case_47_43_27_checked⟩

    · exact ⟨Witness.linear .negative case_47_43_28, case_47_43_28_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_47_44_1_checked⟩

    · exact ⟨Witness.rising, case_47_44_2_checked⟩

    · exact ⟨Witness.rising, case_47_44_3_checked⟩

    · exact ⟨Witness.rising, case_47_44_4_checked⟩

    · exact ⟨Witness.rising, case_47_44_5_checked⟩

    · exact ⟨Witness.rising, case_47_44_6_checked⟩

    · exact ⟨Witness.rising, case_47_44_7_checked⟩

    · exact ⟨Witness.rising, case_47_44_8_checked⟩

    · exact ⟨Witness.linear .positive case_47_44_9, case_47_44_9_checked⟩

    · exact ⟨Witness.linear .positive case_47_44_10, case_47_44_10_checked⟩

    · exact ⟨Witness.linear .positive case_47_44_11, case_47_44_11_checked⟩

    · exact ⟨Witness.linear .positive case_47_44_12, case_47_44_12_checked⟩

    · exact ⟨Witness.linear .positive case_47_44_13, case_47_44_13_checked⟩

    · exact ⟨Witness.linear .positive case_47_44_14, case_47_44_14_checked⟩

    · exact ⟨Witness.linear .positive case_47_44_15, case_47_44_15_checked⟩

    · exact ⟨Witness.linear .positive case_47_44_16, case_47_44_16_checked⟩

    · exact ⟨Witness.linear .positive case_47_44_17, case_47_44_17_checked⟩

    · exact ⟨Witness.linear .positive case_47_44_18, case_47_44_18_checked⟩

    · exact ⟨Witness.linear .positive case_47_44_19, case_47_44_19_checked⟩

    · exact ⟨Witness.linear .positive case_47_44_20, case_47_44_20_checked⟩

    · exact ⟨Witness.linear .positive case_47_44_21, case_47_44_21_checked⟩

    · exact ⟨Witness.linear .positive case_47_44_22, case_47_44_22_checked⟩

    · exact ⟨Witness.linear .negative case_47_44_23, case_47_44_23_checked⟩

    · exact ⟨Witness.linear .negative case_47_44_24, case_47_44_24_checked⟩

    · exact ⟨Witness.linear .negative case_47_44_25, case_47_44_25_checked⟩

    · exact ⟨Witness.linear .negative case_47_44_26, case_47_44_26_checked⟩

    · exact ⟨Witness.linear .negative case_47_44_27, case_47_44_27_checked⟩

    · exact ⟨Witness.linear .negative case_47_44_28, case_47_44_28_checked⟩

  · have hkHi : k ≤ 29 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_47_45_1_checked⟩

    · exact ⟨Witness.rising, case_47_45_2_checked⟩

    · exact ⟨Witness.rising, case_47_45_3_checked⟩

    · exact ⟨Witness.rising, case_47_45_4_checked⟩

    · exact ⟨Witness.rising, case_47_45_5_checked⟩

    · exact ⟨Witness.rising, case_47_45_6_checked⟩

    · exact ⟨Witness.rising, case_47_45_7_checked⟩

    · exact ⟨Witness.rising, case_47_45_8_checked⟩

    · exact ⟨Witness.linear .positive case_47_45_9, case_47_45_9_checked⟩

    · exact ⟨Witness.linear .positive case_47_45_10, case_47_45_10_checked⟩

    · exact ⟨Witness.linear .positive case_47_45_11, case_47_45_11_checked⟩

    · exact ⟨Witness.linear .positive case_47_45_12, case_47_45_12_checked⟩

    · exact ⟨Witness.linear .positive case_47_45_13, case_47_45_13_checked⟩

    · exact ⟨Witness.linear .positive case_47_45_14, case_47_45_14_checked⟩

    · exact ⟨Witness.linear .positive case_47_45_15, case_47_45_15_checked⟩

    · exact ⟨Witness.linear .positive case_47_45_16, case_47_45_16_checked⟩

    · exact ⟨Witness.linear .positive case_47_45_17, case_47_45_17_checked⟩

    · exact ⟨Witness.linear .positive case_47_45_18, case_47_45_18_checked⟩

    · exact ⟨Witness.linear .positive case_47_45_19, case_47_45_19_checked⟩

    · exact ⟨Witness.linear .positive case_47_45_20, case_47_45_20_checked⟩

    · exact ⟨Witness.linear .positive case_47_45_21, case_47_45_21_checked⟩

    · exact ⟨Witness.linear .positive case_47_45_22, case_47_45_22_checked⟩

    · exact ⟨Witness.linear .negative case_47_45_23, case_47_45_23_checked⟩

    · exact ⟨Witness.linear .negative case_47_45_24, case_47_45_24_checked⟩

    · exact ⟨Witness.linear .negative case_47_45_25, case_47_45_25_checked⟩

    · exact ⟨Witness.linear .negative case_47_45_26, case_47_45_26_checked⟩

    · exact ⟨Witness.linear .negative case_47_45_27, case_47_45_27_checked⟩

    · exact ⟨Witness.linear .negative case_47_45_28, case_47_45_28_checked⟩

    · exact ⟨Witness.linear .negative case_47_45_29, case_47_45_29_checked⟩

  · have hkHi : k ≤ 30 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_47_46_1_checked⟩

    · exact ⟨Witness.rising, case_47_46_2_checked⟩

    · exact ⟨Witness.rising, case_47_46_3_checked⟩

    · exact ⟨Witness.rising, case_47_46_4_checked⟩

    · exact ⟨Witness.rising, case_47_46_5_checked⟩

    · exact ⟨Witness.rising, case_47_46_6_checked⟩

    · exact ⟨Witness.rising, case_47_46_7_checked⟩

    · exact ⟨Witness.rising, case_47_46_8_checked⟩

    · exact ⟨Witness.linear .positive case_47_46_9, case_47_46_9_checked⟩

    · exact ⟨Witness.linear .positive case_47_46_10, case_47_46_10_checked⟩

    · exact ⟨Witness.linear .positive case_47_46_11, case_47_46_11_checked⟩

    · exact ⟨Witness.linear .positive case_47_46_12, case_47_46_12_checked⟩

    · exact ⟨Witness.linear .positive case_47_46_13, case_47_46_13_checked⟩

    · exact ⟨Witness.linear .positive case_47_46_14, case_47_46_14_checked⟩

    · exact ⟨Witness.linear .positive case_47_46_15, case_47_46_15_checked⟩

    · exact ⟨Witness.linear .positive case_47_46_16, case_47_46_16_checked⟩

    · exact ⟨Witness.linear .positive case_47_46_17, case_47_46_17_checked⟩

    · exact ⟨Witness.linear .positive case_47_46_18, case_47_46_18_checked⟩

    · exact ⟨Witness.linear .positive case_47_46_19, case_47_46_19_checked⟩

    · exact ⟨Witness.linear .positive case_47_46_20, case_47_46_20_checked⟩

    · exact ⟨Witness.linear .positive case_47_46_21, case_47_46_21_checked⟩

    · exact ⟨Witness.linear .positive case_47_46_22, case_47_46_22_checked⟩

    · exact ⟨Witness.linear .positive case_47_46_23, case_47_46_23_checked⟩

    · exact ⟨Witness.linear .negative case_47_46_24, case_47_46_24_checked⟩

    · exact ⟨Witness.linear .negative case_47_46_25, case_47_46_25_checked⟩

    · exact ⟨Witness.linear .negative case_47_46_26, case_47_46_26_checked⟩

    · exact ⟨Witness.linear .negative case_47_46_27, case_47_46_27_checked⟩

    · exact ⟨Witness.linear .negative case_47_46_28, case_47_46_28_checked⟩

    · exact ⟨Witness.linear .negative case_47_46_29, case_47_46_29_checked⟩

    · exact ⟨Witness.linear .negative case_47_46_30, case_47_46_30_checked⟩


#print axioms coverage_47
end ForestUnimodality.FiniteRows.FiniteData
