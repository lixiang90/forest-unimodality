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

theorem case_45_23_1_checked :
    (Witness.rising).check 45 23 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_23_2_checked :
    (Witness.rising).check 45 23 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_23_3_checked :
    (Witness.rising).check 45 23 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_23_4_checked :
    (Witness.rising).check 45 23 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_23_5_checked :
    (Witness.rising).check 45 23 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_23_6_checked :
    (Witness.rising).check 45 23 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_23_7_checked :
    (Witness.rising).check 45 23 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_23_8_checked :
    (Witness.rising).check 45 23 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_23_9_checked :
    (Witness.rising).check 45 23 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_23_10 : Certificate := {
  objectiveScale := 3846250408000000
  eta := 225691729169277571200
  rows := #[⟨.count 2, 56030477439563827200⟩, ⟨.count 3, 9346463262547931520⟩, ⟨.count 4, 1403304153658767360⟩, ⟨.count 5, 245747708068262400⟩, ⟨.count 6, 50844353393433600⟩, ⟨.count 7, 13084943888016000⟩, ⟨.count 8, 4885045718192640⟩, ⟨.count 9, 3813326504507520⟩, ⟨.count 11, 632678605574400⟩, ⟨.path 10, 964787491261440⟩, ⟨.path 11, 663947353396800⟩, ⟨.privateRow 10 0, 41904686862720⟩, ⟨.hall 8 3, 5783577151968⟩, ⟨.hall 8 4, 1010891435904⟩, ⟨.hall 7 5, 3363283737450⟩, ⟨.hall 7 6, 461600480565⟩, ⟨.hall 6 8, 2563112160000⟩, ⟨.hall 6 9, 134563388400⟩, ⟨.hall 5 13, 28187520847200⟩, ⟨.hall 9 13, 32044760542080⟩, ⟨.hall 4 16, 482732766996480⟩]
  caps := #[0, 265380037415046400, 16676659468022400, 1318223122444800, 0, 0, 47385082528000, 107467743737200, 0, 132812188959296, 0, 31268747822400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_23_10_checked :
    (Witness.linear .positive case_45_23_10).check 45 23 10 = true := by
  change case_45_23_10.check 45 23 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_23_11 : Certificate := {
  objectiveScale := 1907334000000
  eta := 155187258520694400
  rows := #[⟨.count 2, 42462424478073600⟩, ⟨.count 3, 8058476689623360⟩, ⟨.count 4, 1407594181593600⟩, ⟨.count 5, 269583096182400⟩, ⟨.count 6, 59557648550400⟩, ⟨.count 7, 15252568531200⟩, ⟨.count 8, 4914716526720⟩, ⟨.count 9, 2069991443520⟩, ⟨.count 10, 1927522396800⟩, ⟨.path 11, 146215898400⟩, ⟨.path 12, 487808006400⟩, ⟨.privateRow 4 19, 7408390429440⟩, ⟨.privateRow 8 7, 287162555680⟩, ⟨.privateRow 8 8, 66200384250⟩, ⟨.privateRow 9 4, 68229383040⟩, ⟨.privateRow 9 5, 121052131200⟩, ⟨.privateRow 10 2, 52378326000⟩, ⟨.privateRow 11 0, 69300554400⟩, ⟨.privateRow 12 0, 40738698000⟩, ⟨.privateRow 13 3, 61806424680⟩, ⟨.hall 9 3, 7156103760⟩, ⟨.hall 8 5, 3476368896⟩, ⟨.hall 7 7, 3286872225⟩, ⟨.hall 13 7, 15736777056⟩, ⟨.hall 6 9, 1773954000⟩, ⟨.hall 6 10, 3942712800⟩, ⟨.hall 10 12, 19339689600⟩, ⟨.hall 5 15, 613667054000⟩, ⟨.hall 4 17, 4484025786240⟩]
  caps := #[0, 0, 73216364020800, 22999904928000, 0, 1754800819200, 201753552000, 421308888000, 107357119870, 0, 0, 40375790400, 14075146800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_23_11_checked :
    (Witness.linear .positive case_45_23_11).check 45 23 11 = true := by
  change case_45_23_11.check 45 23 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_23_12 : Certificate := {
  objectiveScale := 1173744000000
  eta := 125627780707228800
  rows := #[⟨.count 2, 39178038054355200⟩, ⟨.count 3, 8480754944101440⟩, ⟨.count 4, 1703929798771200⟩, ⟨.count 5, 376593180163200⟩, ⟨.count 6, 92241723974400⟩, ⟨.count 7, 23832138330000⟩, ⟨.count 8, 7456811281920⟩, ⟨.count 9, 2614726033920⟩, ⟨.count 10, 1173274502400⟩, ⟨.count 11, 1152323172000⟩, ⟨.path 13, 238867574400⟩, ⟨.path 14, 81245926125⟩, ⟨.privateRow 8 8, 47664276660⟩, ⟨.privateRow 8 9, 208814926320⟩, ⟨.privateRow 9 6, 129122273280⟩, ⟨.privateRow 9 7, 240591110760⟩, ⟨.privateRow 10 4, 107270811648⟩, ⟨.privateRow 10 5, 7449361920⟩, ⟨.privateRow 12 0, 57034177200⟩, ⟨.privateRow 13 0, 22094130240⟩, ⟨.privateRow 14 0, 8473649184⟩, ⟨.privateRow 16 0, 73766142450⟩, ⟨.hall 13 1, 12105213120⟩, ⟨.hall 14 1, 32953080160⟩, ⟨.hall 10 3, 11398695840⟩, ⟨.hall 9 5, 5550742080⟩, ⟨.hall 8 7, 5461454544⟩, ⟨.hall 7 9, 8987644575⟩, ⟨.hall 11 9, 814773960⟩, ⟨.hall 11 10, 1745944200⟩, ⟨.hall 6 12, 45142194240⟩, ⟨.hall 10 12, 19339689600⟩, ⟨.hall 5 15, 811217407000⟩, ⟨.hall 4 18, 89680515724800⟩]
  caps := #[0, 248614597331100, 0, 12017823699960, 878708773800, 0, 0, 37383746400, 0, 26834705898, 14181948099, 75002805900, 3517619625, 9093381570, 0, 176534358000, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_23_12_checked :
    (Witness.linear .positive case_45_23_12).check 45 23 12 = true := by
  change case_45_23_12.check 45 23 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_23_13 : Certificate := {
  objectiveScale := 846518400000
  eta := 115774621436073600
  rows := #[⟨.count 2, 35659052600371200⟩, ⟨.count 3, 8128856398703040⟩, ⟨.count 4, 1940998292513280⟩, ⟨.count 5, 502124240217600⟩, ⟨.count 6, 132188927270400⟩, ⟨.count 7, 40673516083200⟩, ⟨.count 8, 13727311678080⟩, ⟨.count 9, 5120505149760⟩, ⟨.count 10, 2346549004800⟩, ⟨.count 11, 1459609351200⟩, ⟨.count 12, 1424690467200⟩, ⟨.path 13, 241855286400⟩, ⟨.privateRow 4 19, 109273758834240⟩, ⟨.privateRow 10 5, 132226174080⟩, ⟨.privateRow 10 6, 315317522520⟩, ⟨.privateRow 11 3, 65647501920⟩, ⟨.privateRow 12 1, 36823550400⟩, ⟨.privateRow 13 0, 104375718720⟩, ⟨.privateRow 14 0, 84736491840⟩, ⟨.hall 11 2, 20020160160⟩, ⟨.hall 11 3, 9117708600⟩, ⟨.hall 10 4, 17529442560⟩, ⟨.hall 9 6, 12529983960⟩, ⟨.hall 8 7, 11370623264⟩, ⟨.hall 8 8, 5756325120⟩, ⟨.hall 7 9, 1924506675⟩, ⟨.hall 7 10, 32967923625⟩, ⟨.hall 12 10, 30474662400⟩, ⟨.hall 6 13, 317304084240⟩, ⟨.hall 5 15, 1739283746200⟩, ⟨.hall 4 17, 12130697779200⟩, ⟨.assumptionRow 13, 1454895301860⟩]
  caps := #[0, 0, 0, 0, 4112746157520, 952350939540, 0, 128518999245, 0, 65056619628, 0, 11780251560, 30204834660, 2052495900, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_23_13_checked :
    (Witness.linear .conditional case_45_23_13).check 45 23 13 = true := by
  change case_45_23_13.check 45 23 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_23_14 : Certificate := {
  objectiveScale := 544190400000
  eta := 18474673633416000
  rows := #[⟨.count 2, 5278478180976000⟩, ⟨.count 3, 1495568817943200⟩, ⟨.count 4, 451911816195840⟩, ⟨.count 5, 141994149897600⟩, ⟨.count 6, 47573487561600⟩, ⟨.count 7, 17000258675400⟩, ⟨.count 8, 6609446363520⟩, ⟨.count 9, 2778146411040⟩, ⟨.count 10, 1215177163200⟩, ⟨.count 11, 576161586000⟩, ⟨.count 12, 502831929600⟩, ⟨.count 13, 435787672320⟩, ⟨.count 15, 476642766600⟩, ⟨.path 12, 68869429200⟩, ⟨.privateRow 3 20, 187679224212480⟩, ⟨.privateRow 12 3, 38798760000⟩, ⟨.privateRow 14 0, 29657772144⟩, ⟨.hall 12 2, 15745242240⟩, ⟨.hall 11 3, 2793510720⟩, ⟨.hall 12 3, 5174343720⟩, ⟨.hall 11 4, 11348637300⟩, ⟨.hall 10 5, 14512906800⟩, ⟨.hall 9 6, 6414644340⟩, ⟨.hall 10 6, 833727600⟩, ⟨.hall 9 7, 10006300980⟩, ⟨.hall 8 8, 9686051648⟩, ⟨.hall 8 9, 13832110656⟩, ⟨.hall 13 9, 10894691808⟩, ⟨.hall 7 11, 74740961295⟩, ⟨.hall 6 13, 293233529160⟩, ⟨.hall 5 15, 1725413189500⟩, ⟨.hall 4 16, 877946509440⟩, ⟨.hall 4 17, 8523981385920⟩, ⟨.hall 3 19, 270961879956768⟩, ⟨.assumptionRow 14, 450093833280⟩]
  caps := #[0, 598303351039680, 9092200178880, 12520013182560, 966939732720, 520706197440, 87373503360, 158804628840, 16924410360, 0, 4130511840, 11671105680, 16131332880, 55235325600, 0, 67547633400, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_23_14_checked :
    (Witness.linear .conditional case_45_23_14).check 45 23 14 = true := by
  change case_45_23_14.check 45 23 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_24_1_checked :
    (Witness.rising).check 45 24 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_24_2_checked :
    (Witness.rising).check 45 24 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_24_3_checked :
    (Witness.rising).check 45 24 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_24_4_checked :
    (Witness.rising).check 45 24 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_24_5_checked :
    (Witness.rising).check 45 24 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_24_6_checked :
    (Witness.rising).check 45 24 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_24_7_checked :
    (Witness.rising).check 45 24 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_24_8_checked :
    (Witness.rising).check 45 24 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_24_9_checked :
    (Witness.rising).check 45 24 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_24_10 : Certificate := {
  objectiveScale := 21939918000000
  eta := 1763422260748948800
  rows := #[⟨.count 2, 398830081403033280⟩, ⟨.count 3, 58809655326502080⟩, ⟨.count 4, 8847470270358720⟩, ⟨.count 5, 1513696374590400⟩, ⟨.count 6, 312518773967400⟩, ⟨.count 7, 77385601172880⟩, ⟨.count 8, 27212519093760⟩, ⟨.count 9, 22371830601120⟩, ⟨.path 10, 6058057344885⟩, ⟨.path 11, 3488446962000⟩, ⟨.privateRow 4 20, 274676364602640⟩, ⟨.privateRow 5 15, 17007824433600⟩, ⟨.privateRow 6 11, 531494513550⟩, ⟨.privateRow 6 12, 16400402132400⟩, ⟨.privateRow 6 13, 20551121190600⟩, ⟨.privateRow 7 8, 1020469466016⟩, ⟨.privateRow 7 9, 7086593514000⟩, ⟨.privateRow 7 10, 6643681419375⟩, ⟨.privateRow 7 11, 9779499049320⟩, ⟨.privateRow 7 12, 9283437503340⟩, ⟨.privateRow 8 5, 1009839575745⟩, ⟨.privateRow 8 7, 6994467798318⟩, ⟨.privateRow 8 8, 1700782443360⟩, ⟨.privateRow 9 2, 485937840960⟩, ⟨.privateRow 9 3, 1076826754080⟩, ⟨.privateRow 9 4, 447000513960⟩, ⟨.privateRow 10 0, 503693262072⟩, ⟨.privateRow 11 0, 248490941400⟩, ⟨.hall 5 12, 12392437200⟩, ⟨.hall 5 13, 10865483200⟩, ⟨.hall 4 17, 3702931600368⟩, ⟨.hall 6 17, 30472352110200⟩]
  caps := #[0, 6542546777116350, 0, 0, 1117688131560, 719439190470, 0, 3000278157786, 793710612825, 0, 203251836333, 9573782400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_24_10_checked :
    (Witness.linear .positive case_45_24_10).check 45 24 10 = true := by
  change case_45_24_10.check 45 24 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_24_11 : Certificate := {
  objectiveScale := 78078000000
  eta := 9032062665225600
  rows := #[⟨.count 2, 2216960836009920⟩, ⟨.count 3, 368567423864640⟩, ⟨.count 4, 65029204880640⟩, ⟨.count 5, 12468369513600⟩, ⟨.count 6, 2678278402800⟩, ⟨.count 7, 677891934720⟩, ⟨.count 8, 205788623040⟩, ⟨.count 9, 83805321600⟩, ⟨.count 10, 76821544800⟩, ⟨.path 11, 8311960800⟩, ⟨.path 12, 18481663200⟩, ⟨.privateRow 4 20, 2983935034080⟩, ⟨.privateRow 6 13, 139966526700⟩, ⟨.privateRow 6 14, 201249168120⟩, ⟨.privateRow 7 10, 41611670100⟩, ⟨.privateRow 7 11, 73928265840⟩, ⟨.privateRow 7 12, 109451301960⟩, ⟨.privateRow 7 13, 87762795120⟩, ⟨.privateRow 8 7, 11046006972⟩, ⟨.privateRow 8 8, 25387321960⟩, ⟨.privateRow 8 9, 38207078910⟩, ⟨.privateRow 8 10, 44746055640⟩, ⟨.privateRow 8 11, 57499762320⟩, ⟨.privateRow 9 4, 2483120640⟩, ⟨.privateRow 9 5, 5587021440⟩, ⟨.privateRow 9 6, 21696266592⟩, ⟨.privateRow 9 7, 13657163520⟩, ⟨.privateRow 9 8, 581981400⟩, ⟨.privateRow 10 2, 4405151520⟩, ⟨.privateRow 10 3, 4946841900⟩, ⟨.privateRow 11 0, 2448856800⟩, ⟨.privateRow 12 0, 1396755360⟩, ⟨.privateRow 13 0, 1707145440⟩, ⟨.hall 6 11, 88642125⟩, ⟨.hall 5 14, 1153472320⟩, ⟨.hall 7 16, 27414747360⟩, ⟨.hall 4 17, 35621890304⟩]
  caps := #[0, 0, 0, 0, 0, 14027270400, 18875431575, 17975786400, 2096883360, 2584639200, 1364419980, 0, 323843520, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_24_11_checked :
    (Witness.linear .positive case_45_24_11).check 45 24 11 = true := by
  change case_45_24_11.check 45 24 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_24_12 : Certificate := {
  objectiveScale := 268983000000
  eta := 40991669019100800
  rows := #[⟨.count 2, 10907952603387840⟩, ⟨.count 3, 2051411803721280⟩, ⟨.count 4, 416864430702720⟩, ⟨.count 5, 92493139939200⟩, ⟨.count 6, 22316658764400⟩, ⟨.count 7, 5520908352960⟩, ⟨.count 8, 1720802603520⟩, ⟨.count 9, 595662439680⟩, ⟨.count 10, 289558130400⟩, ⟨.count 11, 289558130400⟩, ⟨.path 13, 61203288300⟩, ⟨.path 14, 12154018800⟩, ⟨.privateRow 4 20, 28034742415680⟩, ⟨.privateRow 7 11, 212539607280⟩, ⟨.privateRow 7 12, 687126039600⟩, ⟨.privateRow 7 13, 867571312608⟩, ⟨.privateRow 8 9, 198295612515⟩, ⟨.privateRow 8 10, 338014797120⟩, ⟨.privateRow 8 11, 596007151740⟩, ⟨.privateRow 8 12, 575393370552⟩, ⟨.privateRow 9 6, 27025425504⟩, ⟨.privateRow 9 7, 93148858880⟩, ⟨.privateRow 9 8, 102724193880⟩, ⟨.privateRow 9 9, 428624824320⟩, ⟨.privateRow 9 10, 239919593760⟩, ⟨.privateRow 9 11, 26473886208⟩, ⟨.privateRow 10 4, 27827664480⟩, ⟨.privateRow 10 5, 53775081360⟩, ⟨.privateRow 10 6, 82730894400⟩, ⟨.privateRow 10 7, 83765030580⟩, ⟨.privateRow 11 2, 23816469600⟩, ⟨.privateRow 11 3, 31109551200⟩, ⟨.privateRow 12 0, 12409634160⟩, ⟨.privateRow 13 0, 5055776880⟩, ⟨.privateRow 14 0, 814773960⟩, ⟨.privateRow 14 7, 13443770340⟩, ⟨.hall 14 7, 2091253164⟩, ⟨.hall 15 7, 14937522600⟩, ⟨.hall 7 11, 762084015⟩, ⟨.hall 6 12, 3109167600⟩, ⟨.hall 7 12, 888140484⟩, ⟨.hall 5 15, 54015561600⟩, ⟨.hall 8 15, 143400216960⟩, ⟨.hall 4 18, 2501956416960⟩]
  caps := #[0, 0, 0, 3212143797720, 0, 440504493000, 0, 61360608870, 3486145080, 3506848620, 0, 0, 14248650240, 533965740, 72039904860, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_24_12_checked :
    (Witness.linear .positive case_45_24_12).check 45 24 12 = true := by
  change case_45_24_12.check 45 24 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_24_13 : Certificate := {
  objectiveScale := 25346475000
  eta := 5855952717014400
  rows := #[⟨.count 2, 1449100163871360⟩, ⟨.count 3, 332237816951040⟩, ⟨.count 4, 75920172007680⟩, ⟨.count 5, 20076030374400⟩, ⟨.count 6, 5377508136000⟩, ⟨.count 7, 1505702278080⟩, ⟨.count 8, 491657886720⟩, ⟨.count 9, 184371707520⟩, ⟨.count 10, 76821544800⟩, ⟨.count 11, 47274796800⟩, ⟨.count 12, 49638536640⟩, ⟨.path 13, 8198981175⟩, ⟨.privateRow 7 12, 144253789680⟩, ⟨.privateRow 7 13, 300116168352⟩, ⟨.privateRow 8 9, 2240628390⟩, ⟨.privateRow 8 10, 71517200040⟩, ⟨.privateRow 8 11, 173915441700⟩, ⟨.privateRow 8 12, 240707507040⟩, ⟨.privateRow 9 7, 5427847040⟩, ⟨.privateRow 9 8, 31122574560⟩, ⟨.privateRow 9 9, 80254595520⟩, ⟨.privateRow 9 10, 124227660480⟩, ⟨.privateRow 9 11, 135048336192⟩, ⟨.privateRow 10 5, 4195638216⟩, ⟨.privateRow 10 6, 16480519440⟩, ⟨.privateRow 10 7, 11449364850⟩, ⟨.privateRow 10 8, 108985290480⟩, ⟨.privateRow 10 9, 17038624680⟩, ⟨.privateRow 11 3, 2734905600⟩, ⟨.privateRow 11 5, 38321236800⟩, ⟨.privateRow 11 6, 1074427200⟩, ⟨.privateRow 12 1, 1969783200⟩, ⟨.privateRow 12 2, 6500284560⟩, ⟨.privateRow 12 3, 1359150408⟩, ⟨.privateRow 13 0, 2889015360⟩, ⟨.privateRow 14 0, 2327925600⟩, ⟨.hall 7 12, 1220106888⟩, ⟨.hall 7 13, 1265296032⟩, ⟨.hall 6 14, 10814013210⟩, ⟨.hall 5 15, 18425807400⟩, ⟨.hall 6 15, 2714486775⟩, ⟨.hall 8 15, 522386504640⟩, ⟨.hall 4 18, 953126254080⟩, ⟨.hall 3 20, 13731302407680⟩, ⟨.assumptionRow 13, 48445079760⟩]
  caps := #[0, 0, 0, 138918960180, 163534491120, 0, 0, 2287072788, 6433176750, 0, 2921120895, 4732758450, 0, 2057892375, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_24_13_checked :
    (Witness.linear .conditional case_45_24_13).check 45 24 13 = true := by
  change case_45_24_13.check 45 24 13 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_24_14 : Certificate := {
  objectiveScale := 29845200000
  eta := 2977603076448000
  rows := #[⟨.count 2, 774176799876480⟩, ⟨.count 3, 200596417781760⟩, ⟨.count 4, 57810773180160⟩, ⟨.count 5, 17105597308800⟩, ⟨.count 6, 5300686591200⟩, ⟨.count 7, 1720802603520⟩, ⟨.count 8, 594086613120⟩, ⟨.count 9, 219827805120⟩, ⟨.count 10, 94549593600⟩, ⟨.count 11, 41365447200⟩, ⟨.count 12, 35456097600⟩, ⟨.count 13, 30728617920⟩, ⟨.count 15, 38410772400⟩, ⟨.path 12, 4722194400⟩, ⟨.privateRow 3 21, 19328300671680⟩, ⟨.privateRow 6 14, 156203807760⟩, ⟨.privateRow 7 12, 70846535760⟩, ⟨.privateRow 7 13, 429176363616⟩, ⟨.privateRow 8 10, 28716625080⟩, ⟨.privateRow 8 11, 170501150820⟩, ⟨.privateRow 8 12, 373864851360⟩, ⟨.privateRow 9 8, 10833807600⟩, ⟨.privateRow 9 9, 70461959040⟩, ⟨.privateRow 9 10, 163360686720⟩, ⟨.privateRow 9 11, 249138179136⟩, ⟨.privateRow 10 6, 3676928640⟩, ⟨.privateRow 10 7, 30137682960⟩, ⟨.privateRow 10 8, 74204547120⟩, ⟨.privateRow 10 9, 121634112600⟩, ⟨.privateRow 10 10, 148797422928⟩, ⟨.privateRow 11 3, 586051200⟩, ⟨.privateRow 11 4, 268606800⟩, ⟨.privateRow 11 5, 13609411200⟩, ⟨.privateRow 11 6, 35456097600⟩, ⟨.privateRow 11 7, 61165605600⟩, ⟨.privateRow 11 8, 31516531200⟩, ⟨.privateRow 12 3, 6323004072⟩, ⟨.privateRow 12 4, 18384643200⟩, ⟨.privateRow 12 5, 15142708350⟩, ⟨.privateRow 13 1, 3294910080⟩, ⟨.privateRow 13 2, 5830558272⟩, ⟨.privateRow 14 0, 1629547920⟩, ⟨.hall 8 10, 275854920⟩, ⟨.hall 8 11, 1121838432⟩, ⟨.hall 7 12, 3480722784⟩, ⟨.hall 7 13, 286197912⟩, ⟨.hall 6 14, 2093136045⟩, ⟨.hall 9 14, 269939089728⟩, ⟨.hall 6 15, 88071758775⟩, ⟨.hall 5 16, 148445897600⟩, ⟨.hall 4 17, 173314197056⟩, ⟨.hall 3 20, 27910364676480⟩, ⟨.assumptionRow 14, 30760482060⟩]
  caps := #[0, 50041882579920, 1254916047000, 363544381200, 204114733680, 28167899760, 0, 0, 1769676480, 12495366048, 6049091532, 0, 26578860, 31864140, 8080061220, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_24_14_checked :
    (Witness.linear .conditional case_45_24_14).check 45 24 14 = true := by
  change case_45_24_14.check 45 24 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_24_15 : Certificate := {
  objectiveScale := 58605120000
  eta := 4926579635577600
  rows := #[⟨.count 2, 1266834763434240⟩, ⟨.count 3, 357454838220480⟩, ⟨.count 4, 102894311520000⟩, ⟨.count 5, 30384084931200⟩, ⟨.count 6, 9169698938400⟩, ⟨.count 7, 2838672476640⟩, ⟨.count 8, 956311836480⟩, ⟨.count 9, 351982350720⟩, ⟨.count 10, 132691759200⟩, ⟨.count 11, 48886437600⟩, ⟨.count 12, 33522128640⟩, ⟨.count 13, 36315639360⟩, ⟨.count 14, 42368245920⟩, ⟨.path 11, 11765239200⟩, ⟨.privateRow 3 21, 53093464744320⟩, ⟨.privateRow 6 14, 172499286960⟩, ⟨.privateRow 7 12, 45898933080⟩, ⟨.privateRow 7 13, 760812644592⟩, ⟨.privateRow 8 10, 5187948480⟩, ⟨.privateRow 8 11, 260009890140⟩, ⟨.privateRow 8 12, 754760038032⟩, ⟨.privateRow 9 9, 81543908160⟩, ⟨.privateRow 9 10, 294094600800⟩, ⟨.privateRow 9 11, 555349931136⟩, ⟨.privateRow 10 7, 23832138330⟩, ⟨.privateRow 10 8, 114334403040⟩, ⟨.privateRow 10 9, 254675060640⟩, ⟨.privateRow 10 10, 379777782384⟩, ⟨.privateRow 11 5, 5572912800⟩, ⟨.privateRow 11 6, 43966049400⟩, ⟨.privateRow 11 7, 116275348800⟩, ⟨.privateRow 11 8, 202000453200⟩, ⟨.privateRow 11 9, 259542541440⟩, ⟨.privateRow 12 4, 16140284160⟩, ⟨.privateRow 12 5, 53862378570⟩, ⟨.privateRow 12 6, 106352943840⟩, ⟨.privateRow 12 7, 33405732360⟩, ⟨.privateRow 13 2, 2886627744⟩, ⟨.privateRow 13 3, 26176230080⟩, ⟨.privateRow 13 4, 33987713760⟩, ⟨.privateRow 14 1, 11046006972⟩, ⟨.privateRow 14 2, 4875710840⟩, ⟨.privateRow 15 0, 3328933608⟩, ⟨.hall 9 9, 1294335936⟩, ⟨.hall 8 10, 1424216820⟩, ⟨.hall 9 10, 433119744⟩, ⟨.hall 8 11, 3361081152⟩, ⟨.hall 7 12, 4534662132⟩, ⟨.hall 7 13, 18956674737⟩, ⟨.hall 10 13, 10974506400⟩, ⟨.hall 6 15, 252340288200⟩, ⟨.hall 5 16, 353079126400⟩, ⟨.hall 4 17, 403153150400⟩, ⟨.hall 3 19, 3373463499120⟩, ⟨.assumptionRow 15, 32329948560⟩]
  caps := #[0, 0, 7475685386400, 716194721760, 238552916160, 3809332800, 13917882000, 5594697360, 8965362120, 7175922468, 0, 1354690800, 0, 6465664128, 0, 0, 58605120000, 0, 0, 0, 0, 0] }

theorem case_45_24_15_checked :
    (Witness.linear .conditional case_45_24_15).check 45 24 15 = true := by
  change case_45_24_15.check 45 24 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_25_1_checked :
    (Witness.rising).check 45 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_25_2_checked :
    (Witness.rising).check 45 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_25_3_checked :
    (Witness.rising).check 45 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_25_4_checked :
    (Witness.rising).check 45 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_25_5_checked :
    (Witness.rising).check 45 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_25_6_checked :
    (Witness.rising).check 45 25 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_25_7_checked :
    (Witness.rising).check 45 25 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_25_8_checked :
    (Witness.rising).check 45 25 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_25_9_checked :
    (Witness.rising).check 45 25 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_25_10 : Certificate := {
  objectiveScale := 49686000000
  eta := 5131853787060000
  rows := #[⟨.count 2, 1028531537953920⟩, ⟨.count 3, 137569694502240⟩, ⟨.count 4, 20845176992640⟩, ⟨.count 5, 3548340595800⟩, ⟨.count 6, 720260180640⟩, ⟨.count 7, 180065045160⟩, ⟨.count 8, 65181916800⟩, ⟨.count 9, 48886437600⟩, ⟨.path 10, 14222688480⟩, ⟨.path 11, 7629782160⟩, ⟨.privateRow 5 15, 30010840860⟩, ⟨.privateRow 5 16, 180065045160⟩, ⟨.privateRow 5 17, 206545198860⟩, ⟨.privateRow 6 12, 38837558760⟩, ⟨.privateRow 6 13, 53969075160⟩, ⟨.privateRow 6 14, 70025295340⟩, ⟨.privateRow 6 15, 86148766704⟩, ⟨.privateRow 6 16, 89149850790⟩, ⟨.privateRow 7 8, 4401895680⟩, ⟨.privateRow 7 9, 11953897956⟩, ⟨.privateRow 7 10, 11600829240⟩, ⟨.privateRow 7 11, 46529412930⟩, ⟨.privateRow 7 12, 16860832560⟩, ⟨.privateRow 7 13, 10844253420⟩, ⟨.privateRow 8 5, 2318972040⟩, ⟨.privateRow 8 6, 5635519890⟩, ⟨.privateRow 8 7, 7777387800⟩, ⟨.privateRow 8 8, 7495920432⟩, ⟨.privateRow 9 2, 1122577456⟩, ⟨.privateRow 9 3, 2832309480⟩, ⟨.privateRow 9 4, 459616080⟩, ⟨.privateRow 10 0, 1027726245⟩, ⟨.privateRow 11 0, 503678448⟩, ⟨.hall 4 16, 53301248⟩, ⟨.hall 4 17, 750381632⟩, ⟨.hall 5 19, 97976568690⟩, ⟨.hall 3 21, 1767911352480⟩]
  caps := #[0, 6292693286880, 0, 267415162560, 0, 51951539640, 8077154904, 7936754436, 0, 2962248128, 0, 74605440, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_25_10_checked :
    (Witness.linear .positive case_45_25_10).check 45 25 10 = true := by
  change case_45_25_10.check 45 25 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_25_11 : Certificate := {
  objectiveScale := 45545500000
  eta := 6815101829215680
  rows := #[⟨.count 2, 1443401402002560⟩, ⟨.count 3, 223280655998400⟩, ⟨.count 4, 39656678181120⟩, ⟨.count 5, 7626284265600⟩, ⟨.count 6, 1652361590880⟩, ⟨.count 7, 402498336240⟩, ⟨.count 8, 117327450240⟩, ⟨.count 9, 48886437600⟩, ⟨.count 10, 44442216000⟩, ⟨.path 11, 5451796350⟩, ⟨.path 12, 10380274905⟩, ⟨.privateRow 5 16, 211841229600⟩, ⟨.privateRow 5 17, 566675289180⟩, ⟨.privateRow 6 13, 81710188560⟩, ⟨.privateRow 6 14, 165942296520⟩, ⟨.privateRow 6 15, 224551703376⟩, ⟨.privateRow 6 16, 323057875140⟩, ⟨.privateRow 7 10, 24210426240⟩, ⟨.privateRow 7 11, 53338595310⟩, ⟨.privateRow 7 12, 78251556240⟩, ⟨.privateRow 7 13, 95832937200⟩, ⟨.privateRow 7 14, 115604785296⟩, ⟨.privateRow 7 15, 76414157820⟩, ⟨.privateRow 8 7, 6370050960⟩, ⟨.privateRow 8 8, 17925027120⟩, ⟨.privateRow 8 9, 27340192880⟩, ⟨.privateRow 8 10, 34831586790⟩, ⟨.privateRow 8 11, 30961410480⟩, ⟨.privateRow 9 4, 1420631520⟩, ⟨.privateRow 9 5, 6518191680⟩, ⟨.privateRow 9 6, 10369850400⟩, ⟨.privateRow 9 7, 9016831824⟩, ⟨.privateRow 10 2, 2856999600⟩, ⟨.privateRow 10 3, 2529787680⟩, ⟨.privateRow 11 0, 1303638336⟩, ⟨.privateRow 12 0, 775975200⟩, ⟨.hall 5 14, 79704625⟩, ⟨.hall 5 15, 86080995⟩, ⟨.hall 4 18, 14526255744⟩, ⟨.hall 4 19, 65368150848⟩, ⟨.hall 3 21, 5172777660960⟩]
  caps := #[0, 12465679466240, 0, 624931627320, 17330895582, 254209475520, 0, 6300309015, 25151327110, 2173064355, 4801087795, 939078140, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_25_11_checked :
    (Witness.linear .positive case_45_25_11).check 45 25 11 = true := by
  change case_45_25_11.check 45 25 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_25_12 : Certificate := {
  objectiveScale := 11711700000
  eta := 2357720254169280
  rows := #[⟨.count 2, 503770549201920⟩, ⟨.count 3, 98161173190080⟩, ⟨.count 4, 20772545713920⟩, ⟨.count 5, 4584849469200⟩, ⟨.count 6, 1053153541440⟩, ⟨.count 7, 272367295200⟩, ⟨.count 8, 78218300160⟩, ⟨.count 9, 25141596480⟩, ⟨.count 10, 11427998400⟩, ⟨.count 11, 12570798240⟩, ⟨.path 13, 3194231040⟩, ⟨.privateRow 11 6, 761866560⟩, ⟨.privateRow 12 0, 166280400⟩, ⟨.privateRow 12 5, 413853440⟩, ⟨.privateRow 12 12, 465585120⟩, ⟨.privateRow 13 0, 268606800⟩, ⟨.privateRow 14 0, 432329040⟩, ⟨.hall 12 2, 17907120⟩, ⟨.hall 13 3, 5895396⟩, ⟨.hall 10 4, 11721024⟩, ⟨.hall 9 5, 21453660⟩, ⟨.hall 8 7, 16288776⟩, ⟨.hall 7 10, 18932550⟩, ⟨.hall 5 15, 724368645⟩, ⟨.hall 6 15, 201441240⟩]
  caps := #[0, 15530988432960, 1852097607360, 217893836160, 0, 0, 942701760, 0, 32672640, 1476034560, 1888955640, 0, 1454510640, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_25_12_checked :
    (Witness.linear .positive case_45_25_12).check 45 25 12 = true := by
  change case_45_25_12.check 45 25 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_25_13 : Certificate := {
  objectiveScale := 650650000
  eta := 134894442402720
  rows := #[⟨.count 2, 31794342259680⟩, ⟨.count 3, 8180097765840⟩, ⟨.count 4, 2106307082880⟩, ⟨.count 5, 540951711300⟩, ⟨.count 6, 139209950880⟩, ⟨.count 7, 40098518460⟩, ⟨.count 8, 12105213120⟩, ⟨.count 9, 3841077240⟩, ⟨.count 10, 1269777600⟩, ⟨.count 11, 698377680⟩, ⟨.count 12, 465585120⟩, ⟨.path 14, 108448340⟩, ⟨.privateRow 13 0, 8953560⟩, ⟨.privateRow 14 0, 9006855⟩, ⟨.privateRow 14 3, 12009140⟩, ⟨.privateRow 15 1, 50438388⟩, ⟨.hall 13 2, 1637610⟩, ⟨.hall 12 3, 610470⟩, ⟨.hall 11 4, 232560⟩, ⟨.hall 8 10, 8430300⟩]
  caps := #[0, 465222998240, 84232107960, 16644668040, 2796233440, 1832230400, 363062700, 242582340, 43563520, 62862800, 139970740, 0, 518146200, 59864525, 77497511, 0, 0, 0, 0, 0, 0] }

theorem case_45_25_13_checked :
    (Witness.linear .positive case_45_25_13).check 45 25 13 = true := by
  change case_45_25_13.check 45 25 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_25_14 : Certificate := {
  objectiveScale := 94217200000
  eta := 16560886928826240
  rows := #[⟨.count 2, 4266378073077120⟩, ⟨.count 3, 1108646631892800⟩, ⟨.count 4, 289642365492480⟩, ⟨.count 5, 77020582438800⟩, ⟨.count 6, 22937516521920⟩, ⟨.count 7, 7083644808240⟩, ⟨.count 8, 2352565797120⟩, ⟨.count 9, 830317340160⟩, ⟨.count 10, 330239851200⟩, ⟨.count 11, 155684501280⟩, ⟨.count 12, 138386223360⟩, ⟨.count 13, 112438806480⟩, ⟨.path 11, 14388454080⟩, ⟨.path 12, 6853371525⟩, ⟨.privateRow 5 17, 9163762728120⟩, ⟨.privateRow 6 15, 3815423499888⟩, ⟨.privateRow 6 16, 9744696561600⟩, ⟨.privateRow 7 12, 114733476000⟩, ⟨.privateRow 7 13, 1408162195440⟩, ⟨.privateRow 7 14, 3919295540160⟩, ⟨.privateRow 7 15, 6380902267740⟩, ⟨.privateRow 8 10, 78923393010⟩, ⟨.privateRow 8 11, 573314353920⟩, ⟨.privateRow 8 12, 1565494151760⟩, ⟨.privateRow 8 13, 2748696361488⟩, ⟨.privateRow 8 14, 3466142438220⟩, ⟨.privateRow 8 15, 487234828080⟩, ⟨.privateRow 9 8, 38440617600⟩, ⟨.privateRow 9 9, 245779698780⟩, ⟨.privateRow 9 10, 669690473760⟩, ⟨.privateRow 9 11, 1200308284560⟩, ⟨.privateRow 9 12, 1634110654176⟩, ⟨.privateRow 9 13, 1507833225360⟩, ⟨.privateRow 10 6, 16040221344⟩, ⟨.privateRow 10 7, 110079950400⟩, ⟨.privateRow 10 8, 306651290400⟩, ⟨.privateRow 10 9, 566799418080⟩, ⟨.privateRow 10 10, 746184806640⟩, ⟨.privateRow 11 4, 4717712160⟩, ⟨.privateRow 11 5, 51894833760⟩, ⟨.privateRow 11 6, 150442598880⟩, ⟨.privateRow 11 7, 291908439900⟩, ⟨.privateRow 11 8, 35719820640⟩, ⟨.privateRow 12 3, 25161131520⟩, ⟨.privateRow 12 4, 80725296960⟩, ⟨.privateRow 12 5, 37799940640⟩, ⟨.privateRow 13 1, 11532185280⟩, ⟨.privateRow 13 2, 19657134000⟩, ⟨.privateRow 14 0, 5354228880⟩, ⟨.hall 7 14, 18482588124⟩, ⟨.hall 6 15, 27892134270⟩, ⟨.hall 6 16, 139320461280⟩, ⟨.hall 5 18, 5197335883740⟩, ⟨.hall 4 19, 8960837453568⟩, ⟨.hall 3 20, 11584604304000⟩, ⟨.hall 2 22, 185494698829440⟩, ⟨.assumptionRow 14, 104722417800⟩]
  caps := #[0, 153427076011440, 15322510259980, 2092113203180, 0, 249269100080, 36438502100, 23707774860, 0, 126830604208, 0, 0, 0, 37379389320, 7544105800, 94217200000, 0, 0, 0, 0, 0] }

theorem case_45_25_14_checked :
    (Witness.linear .conditional case_45_25_14).check 45 25 14 = true := by
  change case_45_25_14.check 45 25 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_25_15 : Certificate := {
  objectiveScale := 264297600000
  eta := 29946566213403840
  rows := #[⟨.count 2, 7667684094470400⟩, ⟨.count 3, 2016316928545920⟩, ⟨.count 4, 547930366663680⟩, ⟨.count 5, 155567120108400⟩, ⟨.count 6, 45521653937760⟩, ⟨.count 7, 14199414989760⟩, ⟨.count 8, 4754555245440⟩, ⟨.count 9, 1638394037280⟩, ⟨.count 10, 613302580800⟩, ⟨.count 11, 289128359520⟩, ⟨.count 12, 128501493120⟩, ⟨.count 13, 208814926320⟩, ⟨.path 10, 43222196160⟩, ⟨.path 11, 18263224980⟩, ⟨.privateRow 2 23, 638973674539200⟩, ⟨.privateRow 5 17, 30486979242720⟩, ⟨.privateRow 6 14, 127609121640⟩, ⟨.privateRow 6 15, 10148405419152⟩, ⟨.privateRow 6 16, 30347769291840⟩, ⟨.privateRow 7 13, 3430530932400⟩, ⟨.privateRow 7 14, 11108954080224⟩, ⟨.privateRow 7 15, 21612344874120⟩, ⟨.privateRow 8 11, 1085378682960⟩, ⟨.privateRow 8 12, 4152204496440⟩, ⟨.privateRow 8 13, 8677063322928⟩, ⟨.privateRow 8 14, 13372186627800⟩, ⟨.privateRow 9 9, 330623633340⟩, ⟨.privateRow 9 10, 1540488137760⟩, ⟨.privateRow 9 11, 3621243465840⟩, ⟨.privateRow 9 12, 5951760823008⟩, ⟨.privateRow 9 13, 7495920432000⟩, ⟨.privateRow 10 7, 88588150560⟩, ⟨.privateRow 10 8, 574971169500⟩, ⟨.privateRow 10 9, 1547024469120⟩, ⟨.privateRow 10 10, 1886635558080⟩, ⟨.privateRow 10 11, 5698457122176⟩, ⟨.privateRow 11 5, 12266051616⟩, ⟨.privateRow 11 6, 211248666720⟩, ⟨.privateRow 11 7, 683394304320⟩, ⟨.privateRow 11 8, 1396827918720⟩, ⟨.privateRow 11 9, 1163814659280⟩, ⟨.privateRow 12 4, 61038209232⟩, ⟨.privateRow 12 5, 298646988640⟩, ⟨.privateRow 12 6, 757623386520⟩, ⟨.privateRow 13 2, 10221709680⟩, ⟨.privateRow 13 3, 133320299112⟩, ⟨.privateRow 13 4, 185613267840⟩, ⟨.privateRow 14 1, 54237643200⟩, ⟨.privateRow 14 2, 23864563008⟩, ⟨.privateRow 15 0, 12655450080⟩, ⟨.hall 7 15, 37276193955⟩, ⟨.hall 7 16, 4100551935480⟩, ⟨.hall 8 16, 17461085241600⟩, ⟨.hall 6 17, 10229489109840⟩, ⟨.hall 5 18, 19353846592080⟩, ⟨.hall 4 19, 31747823654976⟩, ⟨.hall 3 20, 43673958226080⟩, ⟨.hall 2 22, 892711046747520⟩, ⟨.assumptionRow 15, 182673691200⟩]
  caps := #[0, 0, 0, 0, 768088470240, 471658889520, 140867212200, 31933695420, 4667169936, 88888566624, 0, 67036200660, 168420243992, 0, 182673691200, 285031746720, 264297600000, 0, 0, 0, 0] }

theorem case_45_25_15_checked :
    (Witness.linear .conditional case_45_25_15).check 45 25 15 = true := by
  change case_45_25_15.check 45 25 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_25_16 : Certificate := {
  objectiveScale := 106240208536261800000
  eta := 73659396551172650766868320
  rows := #[⟨.count 2, 12376671523300568945260800⟩, ⟨.count 3, 2147716529043334022854080⟩, ⟨.count 4, 346889409476590340680320⟩, ⟨.count 5, 51747905734676542591200⟩, ⟨.count 6, 6602319007527696813360⟩, ⟨.count 7, 535323162772515957840⟩, ⟨.path 6, 1388458631495096261100⟩, ⟨.path 7, 523129593269191708800⟩, ⟨.privateRow 2 23, 254813825479717595931840⟩, ⟨.privateRow 4 18, 24892527068921992039560⟩, ⟨.privateRow 5 15, 1308567731221705674720⟩, ⟨.privateRow 5 16, 11848486002698353200192⟩, ⟨.privateRow 5 17, 26676937611497045232360⟩, ⟨.privateRow 6 13, 1100386501254616135560⟩, ⟨.privateRow 6 14, 3970313457229493353980⟩, ⟨.privateRow 6 15, 9427635699938197701960⟩, ⟨.privateRow 6 16, 21256790588425321159230⟩, ⟨.privateRow 7 10, 31156374552897754160⟩, ⟨.privateRow 7 11, 422204280162847407225⟩, ⟨.privateRow 7 12, 1354695350689632219840⟩, ⟨.privateRow 7 13, 3220436169694976952720⟩, ⟨.privateRow 7 14, 7706104386006265431192⟩, ⟨.privateRow 7 15, 13669859335083889637700⟩, ⟨.privateRow 8 8, 15098858437173527016⟩, ⟨.privateRow 8 9, 129636663349469676400⟩, ⟨.privateRow 8 10, 454681532483066438550⟩, ⟨.privateRow 8 11, 1133394828141077742240⟩, ⟨.privateRow 8 12, 2834467515705757571640⟩, ⟨.privateRow 8 13, 5391665085565237647168⟩, ⟨.privateRow 8 14, 8304372140445439858800⟩, ⟨.privateRow 9 6, 3743518620786824880⟩, ⟨.privateRow 9 7, 35688210851501063856⟩, ⟨.privateRow 9 8, 144888035508230814800⟩, ⟨.privateRow 9 9, 404352004359154681830⟩, ⟨.privateRow 9 10, 1086333451194043372320⟩, ⟨.privateRow 9 11, 2214499237452117295680⟩, ⟨.privateRow 9 12, 3651178494807416532960⟩, ⟨.privateRow 9 13, 4835066258631249901260⟩, ⟨.privateRow 10 4, 935879655196706220⟩, ⟨.privateRow 10 5, 8167676990807617920⟩, ⟨.privateRow 10 6, 42301760414891121144⟩, ⟨.privateRow 10 7, 140589921536216312160⟩, ⟨.privateRow 10 8, 429568761735288154980⟩, ⟨.privateRow 10 9, 961549497167815876320⟩, ⟨.privateRow 10 10, 1387597568771649755520⟩, ⟨.privateRow 10 11, 3117602307391267760064⟩, ⟨.privateRow 10 12, 1134286142098407938640⟩, ⟨.privateRow 11 2, 287962970829755760⟩, ⟨.privateRow 11 3, 2183719195458981180⟩, ⟨.privateRow 11 4, 9869276363892538320⟩, ⟨.privateRow 11 5, 44547871587363216072⟩, ⟨.privateRow 11 6, 168874284448827877920⟩, ⟨.privateRow 11 7, 438927558287255217180⟩, ⟨.privateRow 11 8, 864752801401756547280⟩, ⟨.privateRow 11 9, 1173593087616669599880⟩, ⟨.privateRow 12 1, 703909484250514080⟩, ⟨.privateRow 12 2, 3050274431752227680⟩, ⟨.privateRow 12 3, 9982716322098199680⟩, ⟨.privateRow 12 4, 61310516078219776368⟩, ⟨.privateRow 12 5, 167765093746372522400⟩, ⟨.privateRow 12 6, 541614353788004927430⟩, ⟨.privateRow 12 7, 205893524143275368400⟩, ⟨.privateRow 13 1, 7435043927396054970⟩, ⟨.privateRow 13 2, 11854475632491612120⟩, ⟨.privateRow 13 3, 89906838875896910868⟩, ⟨.privateRow 13 4, 222670033517912620640⟩, ⟨.privateRow 14 0, 12745789589821808520⟩, ⟨.privateRow 14 1, 18539330312468085120⟩, ⟨.privateRow 14 2, 70101842744019946860⟩, ⟨.privateRow 15 0, 27036523372349290800⟩, ⟨.privateRow 16 0, 8922052712875265964⟩, ⟨.hall 8 15, 865156514194194342120⟩, ⟨.hall 7 16, 2967894593606448766260⟩, ⟨.hall 6 17, 6677452083004541158320⟩, ⟨.hall 5 18, 12809015414497635122790⟩, ⟨.hall 4 19, 22272842448560616328416⟩, ⟨.hall 3 20, 33854362094759429102880⟩, ⟨.hall 2 22, 758110698166364772989760⟩]
  caps := #[0, 0, 0, 2704725722800184363280, 134752254531467292720, 291258030714826177002, 0, 0, 51969050630978579098, 10687439972626585168, 71990742707438940, 40168128333470560080, 13116166848738646000, 8417959020371997096, 0, 81994905188183387400, 0, 106240208536261800000, 0, 0, 0] }

theorem case_45_25_16_checked :
    (Witness.linear .negative case_45_25_16).check 45 25 16 = true := by
  change case_45_25_16.check 45 25 16 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_26_1_checked :
    (Witness.rising).check 45 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_26_2_checked :
    (Witness.rising).check 45 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_26_3_checked :
    (Witness.rising).check 45 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_26_4_checked :
    (Witness.rising).check 45 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_26_5_checked :
    (Witness.rising).check 45 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_26_6_checked :
    (Witness.rising).check 45 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_26_7_checked :
    (Witness.rising).check 45 26 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_26_8_checked :
    (Witness.rising).check 45 26 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_26_9_checked :
    (Witness.rising).check 45 26 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_26_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_26_10_checked :
    (Witness.linear .positive case_45_26_10).check 45 26 10 = true := by
  change case_45_26_10.check 45 26 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_26_11 : Certificate := {
  objectiveScale := 303903600000
  eta := 66862860661396800
  rows := #[⟨.count 2, 12195112950820800⟩, ⟨.count 3, 1978922994048000⟩, ⟨.count 4, 337035322423800⟩, ⟨.count 5, 63902721682800⟩, ⟨.count 6, 13251716478000⟩, ⟨.count 7, 3092067178200⟩, ⟨.count 8, 951405285600⟩, ⟨.count 9, 389211253200⟩, ⟨.count 10, 259474168800⟩, ⟨.path 11, 55262106900⟩, ⟨.path 12, 58013930975⟩, ⟨.privateRow 5 18, 15460335891000⟩, ⟨.privateRow 6 16, 9379270440540⟩, ⟨.privateRow 7 13, 2072704372200⟩, ⟨.privateRow 7 15, 2956152137400⟩, ⟨.privateRow 8 11, 723464435925⟩, ⟨.privateRow 9 11, 271830081600⟩, ⟨.privateRow 10 6, 8255996280⟩, ⟨.privateRow 10 10, 38921125320⟩, ⟨.privateRow 10 12, 18163191816⟩, ⟨.privateRow 11 2, 7207615800⟩, ⟨.privateRow 12 0, 3964188690⟩, ⟨.privateRow 13 0, 7281162900⟩, ⟨.hall 10 3, 25741485⟩, ⟨.hall 6 11, 81820200⟩, ⟨.hall 5 15, 1316915600⟩, ⟨.hall 4 18, 31808346570⟩, ⟨.hall 3 21, 3910915008000⟩]
  caps := #[0, 0, 0, 2335038706000, 0, 234247513500, 345793948500, 60399113775, 0, 1523414200, 112998800544, 0, 101620006565, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_26_11_checked :
    (Witness.linear .positive case_45_26_11).check 45 26 11 = true := by
  change case_45_26_11.check 45 26 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_26_12 : Certificate := {
  objectiveScale := 17079562500
  eta := 5056226468092800
  rows := #[⟨.count 2, 1130808483604800⟩, ⟨.count 3, 238956906988800⟩, ⟨.count 4, 55290560925600⟩, ⟨.count 5, 12180870702000⟩, ⟨.count 6, 2996040247200⟩, ⟨.count 7, 708853345200⟩, ⟨.count 8, 195545750400⟩, ⟨.count 9, 53330659200⟩, ⟨.count 10, 26665329600⟩, ⟨.count 11, 16295479200⟩, ⟨.path 12, 5693187500⟩, ⟨.privateRow 10 12, 4533106032⟩, ⟨.privateRow 12 9, 339489150⟩, ⟨.privateRow 12 11, 509233725⟩, ⟨.privateRow 13 0, 249420600⟩, ⟨.privateRow 13 10, 872972100⟩, ⟨.hall 10 3, 317444400⟩, ⟨.hall 13 3, 52907400⟩, ⟨.hall 14 3, 96291468⟩, ⟨.hall 9 6, 3878280⟩, ⟨.hall 8 8, 102521720⟩, ⟨.hall 7 11, 93341325⟩]
  caps := #[0, 19136324407200, 1953646895200, 100036136200, 69994324400, 31016485500, 9962752800, 8488279800, 3715812100, 3601215800, 0, 784083300, 2581178600, 13468712400, 0, 0, 0, 0, 0, 0] }

theorem case_45_26_12_checked :
    (Witness.linear .positive case_45_26_12).check 45 26 12 = true := by
  change case_45_26_12.check 45 26 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_26_13 : Certificate := {
  objectiveScale := 1840410000
  eta := 519513378864480
  rows := #[⟨.count 2, 127897629219360⟩, ⟨.count 3, 30959082554400⟩, ⟨.count 4, 8139242671560⟩, ⟨.count 5, 2147162177160⟩, ⟨.count 6, 570674332800⟩, ⟨.count 7, 153643089600⟩, ⟨.count 8, 43532208720⟩, ⟨.count 9, 14665931280⟩, ⟨.count 10, 4190266080⟩, ⟨.count 11, 2560718160⟩, ⟨.path 13, 334627436⟩, ⟨.hall 13 4, 1662804⟩, ⟨.hall 10 5, 33469260⟩, ⟨.hall 9 7, 6334524⟩, ⟨.hall 12 7, 799425⟩]
  caps := #[0, 2544045039536, 0, 0, 0, 6165373500, 3546347376, 954785832, 972667696, 0, 868787920, 0, 1840410000, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_26_13_checked :
    (Witness.linear .positive case_45_26_13).check 45 26 13 = true := by
  change case_45_26_13.check 45 26 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_26_14 : Certificate := {
  objectiveScale := 350658000000
  eta := 128859691032072000
  rows := #[⟨.count 2, 30197422544889600⟩, ⟨.count 3, 6982771136140800⟩, ⟨.count 4, 1803116888773200⟩, ⟨.count 5, 474705932500800⟩, ⟨.count 6, 127973719130400⟩, ⟨.count 7, 35337910608000⟩, ⟨.count 8, 11190338359200⟩, ⟨.count 9, 3855044793600⟩, ⟨.count 10, 1445641797600⟩, ⟨.count 11, 588965176800⟩, ⟨.path 11, 116906189400⟩, ⟨.privateRow 2 24, 390483912218400⟩, ⟨.privateRow 4 20, 237352966250400⟩, ⟨.privateRow 5 17, 17150665948416⟩, ⟨.privateRow 5 18, 86136157107000⟩, ⟨.privateRow 5 19, 196773265568880⟩, ⟨.privateRow 6 15, 11986142496900⟩, ⟨.privateRow 6 16, 34618531713480⟩, ⟨.privateRow 6 17, 75198232395000⟩, ⟨.privateRow 6 18, 109926143355600⟩, ⟨.privateRow 7 13, 6057927532800⟩, ⟨.privateRow 7 14, 14787232831800⟩, ⟨.privateRow 7 15, 30390603122880⟩, ⟨.privateRow 7 16, 44330146789500⟩, ⟨.privateRow 7 17, 49599281674800⟩, ⟨.privateRow 8 10, 8180071900⟩, ⟨.privateRow 8 11, 2742369104475⟩, ⟨.privateRow 8 12, 6552237591900⟩, ⟨.privateRow 8 13, 13153555615200⟩, ⟨.privateRow 8 14, 8863925910840⟩, ⟨.privateRow 8 15, 42258251435400⟩, ⟨.privateRow 8 16, 368103235500⟩, ⟨.privateRow 9 8, 69604975440⟩, ⟨.privateRow 9 9, 1142235494400⟩, ⟨.privateRow 9 10, 2984982600600⟩, ⟨.privateRow 9 11, 6111469821600⟩, ⟨.privateRow 9 12, 9066494236800⟩, ⟨.privateRow 9 13, 5996736345600⟩, ⟨.privateRow 10 6, 52568792640⟩, ⟨.privateRow 10 7, 525249853128⟩, ⟨.privateRow 10 8, 1370682593280⟩, ⟨.privateRow 10 9, 3047894789940⟩, ⟨.privateRow 10 10, 3235484023200⟩, ⟨.privateRow 11 4, 22309287000⟩, ⟨.privateRow 11 5, 267711444000⟩, ⟨.privateRow 11 6, 696049754400⟩, ⟨.privateRow 11 7, 1409946938400⟩, ⟨.privateRow 12 3, 153376348125⟩, ⟨.privateRow 12 4, 408259952100⟩, ⟨.privateRow 12 5, 51534452970⟩, ⟨.privateRow 13 1, 67957520400⟩, ⟨.privateRow 13 2, 63103411800⟩, ⟨.privateRow 14 0, 21034470600⟩, ⟨.hall 6 19, 79081195667760⟩, ⟨.hall 5 20, 288761212396800⟩, ⟨.hall 4 21, 681780734434800⟩, ⟨.hall 3 22, 1266326344483200⟩, ⟨.hall 2 23, 1540242098194800⟩, ⟨.assumptionRow 14, 414523642104⟩]
  caps := #[0, 0, 66250427487552, 9800380541952, 6035254587648, 3720118225824, 0, 220166955360, 134728915321, 195817166688, 0, 789251463000, 414523642104, 346566121704, 0, 350658000000, 0, 0, 0, 0] }

theorem case_45_26_14_checked :
    (Witness.linear .conditional case_45_26_14).check 45 26 14 = true := by
  change case_45_26_14.check 45 26 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_26_15 : Certificate := {
  objectiveScale := 1632367770572000000
  eta := 596704824119995779988800
  rows := #[⟨.count 2, 128295842415410348078400⟩, ⟨.count 3, 30541805359846995614400⟩, ⟨.count 4, 7217590818869314884000⟩, ⟨.count 5, 1709429404469048262000⟩, ⟨.count 6, 412433761078246564800⟩, ⟨.count 7, 105195655659633739200⟩, ⟨.count 8, 29221015461009372000⟩, ⟨.count 9, 9563241423603067200⟩, ⟨.count 10, 3187747141201022400⟩, ⟨.count 11, 1948067697400624800⟩, ⟨.path 9, 1337883079750176960⟩, ⟨.privateRow 2 24, 8179936261385223535200⟩, ⟨.privateRow 4 19, 258788618176564250775⟩, ⟨.privateRow 4 20, 1389702793633170716700⟩, ⟨.privateRow 5 17, 160559739619759496016⟩, ⟨.privateRow 5 18, 502698869314231229640⟩, ⟨.privateRow 5 19, 1148061229668101548800⟩, ⟨.privateRow 6 15, 71000110185619200300⟩, ⟨.privateRow 6 16, 191202844499871324120⟩, ⟨.privateRow 6 17, 429392386122582361050⟩, ⟨.privateRow 6 18, 676536081768702698400⟩, ⟨.privateRow 7 13, 27133800070937274000⟩, ⟨.privateRow 7 14, 74374441732902425400⟩, ⟨.privateRow 7 15, 168062583208605330960⟩, ⟨.privateRow 7 16, 271024918400861925300⟩, ⟨.privateRow 7 17, 344807982439910589600⟩, ⟨.privateRow 8 11, 9435952909284276375⟩, ⟨.privateRow 8 12, 29151441614673635400⟩, ⟨.privateRow 8 13, 69075233770330487700⟩, ⟨.privateRow 8 14, 115569116148292066260⟩, ⟨.privateRow 8 15, 152375420206055121075⟩, ⟨.privateRow 8 16, 149757704237673031500⟩, ⟨.privateRow 9 9, 2990972626312070400⟩, ⟨.privateRow 9 10, 11378486323453649400⟩, ⟨.privateRow 9 11, 29651108329266652800⟩, ⟨.privateRow 9 12, 43093618760680488000⟩, ⟨.privateRow 9 13, 93507249475229990400⟩, ⟨.privateRow 9 14, 34976670021511218000⟩, ⟨.privateRow 10 7, 796936785300255600⟩, ⟨.privateRow 10 8, 4374297465981402960⟩, ⟨.privateRow 10 9, 13169380377086723790⟩, ⟨.privateRow 10 10, 26116756935411233520⟩, ⟨.privateRow 10 11, 33444780423100726680⟩, ⟨.privateRow 11 5, 112698131254581600⟩, ⟨.privateRow 11 6, 1611583276940516880⟩, ⟨.privateRow 11 7, 5981945252624140800⟩, ⟨.privateRow 11 8, 13702885280579394900⟩, ⟨.privateRow 11 9, 5540608126373205600⟩, ⟨.privateRow 12 4, 420605525575134900⟩, ⟨.privateRow 12 5, 2751645622578382530⟩, ⟨.privateRow 12 6, 5276016680460025500⟩, ⟨.privateRow 13 2, 34786923167868300⟩, ⟨.privateRow 13 3, 1062582380400340800⟩, ⟨.privateRow 13 4, 1210584926241816840⟩, ⟨.privateRow 14 1, 376858334318573250⟩, ⟨.privateRow 14 2, 164447273157195600⟩, ⟨.hall 6 18, 1028228213214465120⟩, ⟨.hall 7 18, 85509918928006372800⟩, ⟨.hall 6 19, 710905561858556578800⟩, ⟨.hall 5 20, 2055536098707225934800⟩, ⟨.hall 4 21, 4430702880674321050800⟩, ⟨.hall 3 22, 8132589746478834436800⟩, ⟨.hall 2 23, 11731750690670912701800⟩, ⟨.assumptionRow 15, 1276752156048230400⟩]
  caps := #[0, 5756470481264173316800, 578760751350145758240, 83910954164014358920, 0, 20479712205992863824, 404229930294876400, 650518120647040360, 922531851339748650, 0, 1198348056425212550, 937271446593666600, 1276752156048230400, 7474296170001140480, 1276752156048230400, 15046925549671769600, 1632367770572000000, 0, 0, 0] }

theorem case_45_26_15_checked :
    (Witness.linear .conditional case_45_26_15).check 45 26 15 = true := by
  change case_45_26_15.check 45 26 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_26_16 : Certificate := {
  objectiveScale := 29798267499000000
  eta := 12757433357937387319200
  rows := #[⟨.count 2, 2703956463353675930400⟩, ⟨.count 3, 628517478006801583200⟩, ⟨.count 4, 143465946066769926600⟩, ⟨.count 5, 32231665538810337600⟩, ⟨.count 6, 7056932982876176400⟩, ⟨.count 7, 1495700198498305800⟩, ⟨.count 8, 296445084387051600⟩, ⟨.count 9, 66148903127689200⟩, ⟨.path 9, 32045161175052480⟩, ⟨.privateRow 2 24, 184631388466880955600⟩, ⟨.privateRow 4 19, 5058094252354067925⟩, ⟨.privateRow 4 20, 29166153870716963100⟩, ⟨.privateRow 5 17, 3062008226186982072⟩, ⟨.privateRow 5 18, 10186257342835984410⟩, ⟨.privateRow 5 19, 24722621719442566920⟩, ⟨.privateRow 6 15, 1303363804461468750⟩, ⟨.privateRow 6 16, 3706141045262275620⟩, ⟨.privateRow 6 17, 8971313738869181700⟩, ⟨.privateRow 6 18, 15335899868815425900⟩, ⟨.privateRow 7 13, 472717161466921800⟩, ⟨.privateRow 7 14, 1366727337109134000⟩, ⟨.privateRow 7 15, 3371389096074559560⟩, ⟨.privateRow 7 16, 6001569232777468350⟩, ⟨.privateRow 7 17, 8512208851685338800⟩, ⟨.privateRow 8 10, 748598697947100⟩, ⟨.privateRow 8 11, 151591236334287750⟩, ⟨.privateRow 8 12, 499529216872986300⟩, ⟨.privateRow 8 13, 1313790714897160500⟩, ⟨.privateRow 8 14, 2467231588694052180⟩, ⟨.privateRow 8 15, 3683667042923192325⟩, ⟨.privateRow 8 16, 4258029393923104800⟩, ⟨.privateRow 9 9, 43010397918415200⟩, ⟨.privateRow 9 10, 176397075007171200⟩, ⟨.privateRow 9 11, 525341288860642800⟩, ⟨.privateRow 9 12, 1073898859418658000⟩, ⟨.privateRow 9 13, 1087291970669202480⟩, ⟨.privateRow 9 14, 3409118470451093400⟩, ⟨.privateRow 9 15, 140464337505710400⟩, ⟨.privateRow 10 7, 8819853750358560⟩, ⟨.privateRow 10 8, 58554029064880440⟩, ⟨.privateRow 10 9, 211400869578906735⟩, ⟨.privateRow 10 10, 492966825689683800⟩, ⟨.privateRow 10 11, 862140704097549240⟩, ⟨.privateRow 10 12, 884190338473445640⟩, ⟨.privateRow 11 6, 15924735938147400⟩, ⟨.privateRow 11 7, 83026401045042000⟩, ⟨.privateRow 11 8, 234277365243899250⟩, ⟨.privateRow 11 9, 467942240644023600⟩, ⟨.privateRow 11 10, 160472339069023800⟩, ⟨.privateRow 12 4, 306244921887450⟩, ⟨.privateRow 12 5, 28633900196476575⟩, ⟨.privateRow 12 6, 111915505343091450⟩, ⟨.privateRow 12 7, 205490342586478950⟩, ⟨.privateRow 13 3, 2099965178656800⟩, ⟨.privateRow 13 4, 49664176475233320⟩, ⟨.privateRow 13 5, 65448914734803600⟩, ⟨.privateRow 14 2, 6824886830634600⟩, ⟨.privateRow 14 3, 27527043550226220⟩, ⟨.privateRow 15 1, 9554841562888440⟩, ⟨.hall 7 18, 5544515956310931600⟩, ⟨.hall 6 19, 21711329985614789520⟩, ⟨.hall 5 20, 52259675103687051000⟩, ⟨.hall 4 21, 104291095658927322600⟩, ⟨.hall 3 22, 182879667513684741600⟩, ⟨.hall 2 23, 258086887104242196000⟩, ⟨.assumptionRow 16, 9507090553114000⟩]
  caps := #[0, 0, 3411875039402318720, 120166213030928400, 597747000352496995, 18037241330334408, 0, 10895816247045800, 8884708868778750, 44250202457399120, 9784954805475570, 16438199216193300, 52886489386005275, 9507090553114000, 142823016938499660, 9507090553114000, 258677316937886000, 29798267499000000, 0, 0] }

theorem case_45_26_16_checked :
    (Witness.linear .conditional case_45_26_16).check 45 26 16 = true := by
  change case_45_26_16.check 45 26 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_27_1_checked :
    (Witness.rising).check 45 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_27_2_checked :
    (Witness.rising).check 45 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_27_3_checked :
    (Witness.rising).check 45 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_27_4_checked :
    (Witness.rising).check 45 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_27_5_checked :
    (Witness.rising).check 45 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_27_6_checked :
    (Witness.rising).check 45 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_27_7_checked :
    (Witness.rising).check 45 27 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_27_8_checked :
    (Witness.rising).check 45 27 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_27_9_checked :
    (Witness.rising).check 45 27 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_27_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_27_10_checked :
    (Witness.linear .positive case_45_27_10).check 45 27 10 = true := by
  change case_45_27_10.check 45 27 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_27_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_27_11_checked :
    (Witness.linear .positive case_45_27_11).check 45 27 11 = true := by
  change case_45_27_11.check 45 27 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_27_12 : Certificate := {
  objectiveScale := 17102800000
  eta := 10699259194784160
  rows := #[⟨.count 2, 2177522051664960⟩, ⟨.count 3, 478917033514920⟩, ⟨.count 4, 101525817176784⟩, ⟨.count 5, 23133710765880⟩, ⟨.count 6, 5300686591200⟩, ⟨.count 7, 1280999259540⟩, ⟨.count 8, 321253732800⟩, ⟨.count 9, 86738507856⟩, ⟨.count 10, 32125373280⟩, ⟨.count 11, 44172388260⟩, ⟨.path 11, 9502404912⟩, ⟨.hall 10 5, 86958630⟩, ⟨.hall 8 10, 2086560⟩, ⟨.hall 7 11, 90995751⟩, ⟨.hall 9 11, 48541086⟩]
  caps := #[0, 32749693364960, 0, 0, 123139951792, 0, 0, 12224380740, 11330439120, 19640457408, 3982236544, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_27_12_checked :
    (Witness.linear .positive case_45_27_12).check 45 27 12 = true := by
  change case_45_27_12.check 45 27 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_27_13 : Certificate := {
  objectiveScale := 4275700000
  eta := 2763758356479120
  rows := #[⟨.count 2, 664588305501120⟩, ⟨.count 3, 156097858046130⟩, ⟨.count 4, 35551901288904⟩, ⟨.count 5, 8932638514800⟩, ⟨.count 6, 2238067671840⟩, ⟨.count 7, 549700831680⟩, ⟨.count 8, 149918408640⟩, ⟨.count 9, 44975522592⟩, ⟨.count 10, 12493200720⟩, ⟨.path 10, 1111414304⟩, ⟨.path 11, 1124427304⟩, ⟨.hall 11 5, 31461815⟩, ⟨.hall 10 9, 5074881⟩]
  caps := #[0, 5898745458320, 0, 0, 75714973048, 32697296632, 3731495768, 4743538800, 4028920896, 0, 1667322800, 5400127304, 4275700000, 0, 0, 0, 0, 0, 0] }

theorem case_45_27_13_checked :
    (Witness.linear .positive case_45_27_13).check 45 27 13 = true := by
  change case_45_27_13.check 45 27 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_27_14 : Certificate := {
  objectiveScale := 390733200000
  eta := 320717453235379200
  rows := #[⟨.count 2, 65172530603980800⟩, ⟨.count 3, 14792449380508800⟩, ⟨.count 4, 3258626530199040⟩, ⟨.count 5, 796280919033600⟩, ⟨.count 6, 194358508344000⟩, ⟨.count 7, 49473074851200⟩, ⟨.count 8, 13492656777600⟩, ⟨.count 9, 4047797033280⟩, ⟨.count 10, 1499184086400⟩, ⟨.path 10, 298807629120⟩, ⟨.privateRow 2 25, 1715066594841600⟩, ⟨.privateRow 3 23, 1487284312714200⟩, ⟨.privateRow 4 20, 198304575028560⟩, ⟨.privateRow 4 21, 587767614273840⟩, ⟨.privateRow 5 17, 3573055405920⟩, ⟨.privateRow 5 18, 128936256505056⟩, ⟨.privateRow 5 19, 233524692601200⟩, ⟨.privateRow 5 20, 431318831143200⟩, ⟨.privateRow 6 15, 12115855065600⟩, ⟨.privateRow 6 16, 52417900735200⟩, ⟨.privateRow 6 17, 99652907914560⟩, ⟨.privateRow 6 18, 169180247035800⟩, ⟨.privateRow 6 19, 207904707410400⟩, ⟨.privateRow 6 20, 27975845898000⟩, ⟨.privateRow 7 13, 8871287975550⟩, ⟨.privateRow 7 14, 22506883542000⟩, ⟨.privateRow 7 15, 40982160219000⟩, ⟨.privateRow 7 16, 71794855051920⟩, ⟨.privateRow 7 17, 86136157107000⟩, ⟨.privateRow 7 18, 78037885926000⟩, ⟨.privateRow 8 10, 149918408640⟩, ⟨.privateRow 8 11, 4643306267600⟩, ⟨.privateRow 8 12, 10681686615600⟩, ⟨.privateRow 8 13, 18070522470000⟩, ⟨.privateRow 8 14, 31514098816200⟩, ⟨.privateRow 8 15, 40028215106880⟩, ⟨.privateRow 8 16, 5106595794300⟩, ⟨.privateRow 9 8, 231692086080⟩, ⟨.privateRow 9 9, 2173816925280⟩, ⟨.privateRow 9 10, 5363747509120⟩, ⟨.privateRow 9 11, 9032584120560⟩, ⟨.privateRow 9 12, 15313094596800⟩, ⟨.privateRow 9 13, 4822375477920⟩, ⟨.privateRow 10 6, 174904810080⟩, ⟨.privateRow 10 7, 1090315699200⟩, ⟨.privateRow 10 8, 2788482400704⟩, ⟨.privateRow 10 9, 5047253090880⟩, ⟨.privateRow 10 10, 2286255731760⟩, ⟨.privateRow 11 4, 86491389600⟩, ⟨.privateRow 11 5, 624660036000⟩, ⟨.privateRow 11 6, 1601401183200⟩, ⟨.privateRow 11 7, 824551247520⟩, ⟨.privateRow 12 0, 18405161775⟩, ⟨.privateRow 12 3, 385092615600⟩, ⟨.privateRow 12 4, 343563019800⟩, ⟨.privateRow 13 1, 126206823600⟩, ⟨.hall 6 20, 6394479062400⟩, ⟨.hall 5 21, 298257319760400⟩, ⟨.hall 4 22, 1070052418955520⟩, ⟨.hall 3 23, 2435260575097350⟩, ⟨.hall 2 24, 2006627915964672⟩, ⟨.assumptionRow 14, 476318242400⟩]
  caps := #[0, 0, 197237893652800, 0, 6043437119720, 0, 3889049135400, 0, 1382960553260, 1745836776320, 0, 785369849600, 0, 2439159236800, 4212480157600, 390733200000, 0, 0, 0] }

theorem case_45_27_14_checked :
    (Witness.linear .conditional case_45_27_14).check 45 27 14 = true := by
  change case_45_27_14.check 45 27 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_27_15 : Certificate := {
  objectiveScale := 48571498067400000
  eta := 36058664164070227680000
  rows := #[⟨.count 2, 7508686537694623881600⟩, ⟨.count 3, 1654456355763222211200⟩, ⟨.count 4, 356344445856694014720⟩, ⟨.count 5, 84086380718735194800⟩, ⟨.count 6, 19928996677621231200⟩, ⟨.count 7, 4894841289240302400⟩, ⟨.count 8, 1186628191330982400⟩, ⟨.count 9, 400487014574206560⟩, ⟨.count 10, 148328523916372800⟩, ⟨.path 9, 57360473134997760⟩, ⟨.privateRow 2 25, 509063494080991449600⟩, ⟨.privateRow 3 22, 29165096015056801800⟩, ⟨.privateRow 3 23, 220063906295428595400⟩, ⟨.privateRow 4 20, 31021056670560416460⟩, ⟨.privateRow 4 21, 85550948310833285280⟩, ⟨.privateRow 5 18, 16302152369974607136⟩, ⟨.privateRow 5 19, 32725510333778021760⟩, ⟨.privateRow 5 20, 65451020667556043520⟩, ⟨.privateRow 6 15, 790833201492906000⟩, ⟨.privateRow 6 16, 6137975584920379200⟩, ⟨.privateRow 6 17, 13262689017036819360⟩, ⟨.privateRow 6 18, 25391989187934068700⟩, ⟨.privateRow 6 19, 35351631533402184000⟩, ⟨.privateRow 7 13, 553583241045034200⟩, ⟨.privateRow 7 14, 2380824164494432800⟩, ⟨.privateRow 7 15, 5234760823215323400⟩, ⟨.privateRow 7 16, 10523908771866650160⟩, ⟨.privateRow 7 17, 14779215737899663050⟩, ⟨.privateRow 7 18, 16287001670746006200⟩, ⟨.privateRow 7 19, 3700266926985228600⟩, ⟨.privateRow 8 11, 259574916853652400⟩, ⟨.privateRow 8 12, 994264636876936425⟩, ⟨.privateRow 8 13, 2171953385918316000⟩, ⟨.privateRow 8 14, 4511659269123006000⟩, ⟨.privateRow 8 15, 6760072477488690360⟩, ⟨.privateRow 8 16, 7759435907375252100⟩, ⟨.privateRow 8 17, 599494450828673400⟩, ⟨.privateRow 9 9, 100863396263133504⟩, ⟨.privateRow 9 10, 433448908777844960⟩, ⟨.privateRow 9 11, 978968257848060480⟩, ⟨.privateRow 9 12, 1370979356769902880⟩, ⟨.privateRow 9 13, 4751457049454475360⟩, ⟨.privateRow 9 14, 1008633962631335040⟩, ⟨.privateRow 10 7, 32362587036299520⟩, ⟨.privateRow 10 8, 191343795852120912⟩, ⟨.privateRow 10 9, 479595560662938720⟩, ⟨.privateRow 10 10, 1069819478746838820⟩, ⟨.privateRow 10 11, 1265030411115350880⟩, ⟨.privateRow 11 5, 6180355163182200⟩, ⟨.privateRow 11 6, 82592018998889400⟩, ⟨.privateRow 11 7, 248450277559924440⟩, ⟨.privateRow 11 8, 613915279542765200⟩, ⟨.privateRow 11 9, 39399764165286525⟩, ⟨.privateRow 12 4, 29135960055001800⟩, ⟨.privateRow 12 5, 132436182068190000⟩, ⟨.privateRow 12 6, 136939012258508460⟩, ⟨.privateRow 13 2, 4482455393077200⟩, ⟨.privateRow 13 3, 63127913452503900⟩, ⟨.privateRow 13 4, 10594894565455200⟩, ⟨.privateRow 14 1, 11654384022000720⟩, ⟨.hall 6 20, 10155963219172056000⟩, ⟨.hall 5 21, 71242719781762128600⟩, ⟨.hall 4 22, 185826619669057567200⟩, ⟨.hall 3 23, 385443257562625687425⟩, ⟨.hall 2 24, 322406879584627918080⟩, ⟨.assumptionRow 15, 42582830606702100⟩]
  caps := #[0, 25241882898446557200, 1159268784805620720, 14901989840753843520, 0, 556000580963691864, 16891904913953940, 0, 74143077613447240, 196076763467249392, 65416376883125268, 66816283426341900, 63963805804959060, 38100375213624900, 676562507382453120, 491703648134697900, 48571498067400000, 0, 0] }

theorem case_45_27_15_checked :
    (Witness.linear .conditional case_45_27_15).check 45 27 15 = true := by
  change case_45_27_15.check 45 27 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_27_16 : Certificate := {
  objectiveScale := 631346531508000000
  eta := 484636894354383401030400
  rows := #[⟨.count 2, 99171629820953299209600⟩, ⟨.count 3, 19163325257833292335800⟩, ⟨.count 4, 3927439162634083256160⟩, ⟨.count 5, 769024215518532573600⟩, ⟨.count 6, 142473608725535287200⟩, ⟨.count 7, 26245138449440710800⟩, ⟨.count 8, 5302048171604184000⟩, ⟨.count 9, 954368670888753120⟩, ⟨.path 8, 1885540316490230400⟩, ⟨.privateRow 2 25, 11524531905798854342400⟩, ⟨.privateRow 3 22, 1137289332809097468000⟩, ⟨.privateRow 3 23, 3591938809455399503100⟩, ⟨.privateRow 4 20, 673843929689390249790⟩, ⟨.privateRow 4 21, 1367274508999381622640⟩, ⟨.privateRow 5 17, 37368078078013202520⟩, ⟨.privateRow 5 18, 245437869347182367856⟩, ⟨.privateRow 5 19, 510697067066180434440⟩, ⟨.privateRow 5 20, 1027170841854565808400⟩, ⟨.privateRow 6 15, 24281216524652630400⟩, ⟨.privateRow 6 16, 86997773749071985800⟩, ⟨.privateRow 6 17, 188298453637257163200⟩, ⟨.privateRow 6 18, 390760950247228360800⟩, ⟨.privateRow 6 19, 581697804046069510800⟩, ⟨.privateRow 7 13, 10414737479936790000⟩, ⟨.privateRow 7 14, 32642762901401881800⟩, ⟨.privateRow 7 15, 70889646446769750600⟩, ⟨.privateRow 7 16, 153554889404188031760⟩, ⟨.privateRow 7 17, 240736656848738900850⟩, ⟨.privateRow 7 18, 298278081425389665600⟩, ⟨.privateRow 7 19, 114770407028903425800⟩, ⟨.privateRow 8 11, 3578882515832824200⟩, ⟨.privateRow 8 12, 12658640009704989300⟩, ⟨.privateRow 8 13, 28309150059100911000⟩, ⟨.privateRow 8 14, 63293200048524946500⟩, ⟨.privateRow 8 15, 106014453191225659080⟩, ⟨.privateRow 8 16, 140139760735713088350⟩, ⟨.privateRow 8 17, 105775861023503470800⟩, ⟨.privateRow 9 9, 996785056261586592⟩, ⟨.privateRow 9 10, 4830755000794923200⟩, ⟨.privateRow 9 11, 12022394229112487220⟩, ⟨.privateRow 9 12, 28146301436687353920⟩, ⟨.privateRow 9 13, 36778540817027689680⟩, ⟨.privateRow 9 14, 98957427074820490176⟩, ⟨.privateRow 10 7, 183161664109962720⟩, ⟨.privateRow 10 8, 1717863607599755616⟩, ⟨.privateRow 10 9, 5266701183793489440⟩, ⟨.privateRow 10 10, 13639518921451763340⟩, ⟨.privateRow 10 11, 26237564094909847680⟩, ⟨.privateRow 10 12, 23735502314881397040⟩, ⟨.privateRow 11 6, 482004379236744000⟩, ⟨.privateRow 11 7, 2240115352502767740⟩, ⟨.privateRow 11 8, 7025213827375543800⟩, ⟨.privateRow 11 9, 15259957393898292075⟩, ⟨.privateRow 11 10, 889986657376416600⟩, ⟨.privateRow 12 4, 34715791599789300⟩, ⟨.privateRow 12 5, 795307225740627600⟩, ⟨.privateRow 12 6, 3665987592937750080⟩, ⟨.privateRow 12 7, 4628772213305240000⟩, ⟨.privateRow 13 3, 69431583199578600⟩, ⟨.privateRow 13 4, 1666357996789886400⟩, ⟨.privateRow 13 5, 1166450597752920480⟩, ⟨.privateRow 14 2, 180522116318904360⟩, ⟨.privateRow 14 3, 590799653407323360⟩, ⟨.privateRow 15 1, 315913703558082630⟩, ⟨.hall 6 20, 261380154353613609600⟩, ⟨.hall 5 21, 1347269376290950312200⟩, ⟨.hall 4 22, 3166609081438895732640⟩, ⟨.hall 3 23, 6321433208197233426300⟩, ⟨.hall 2 24, 5483250969916928592384⟩, ⟨.assumptionRow 16, 297237947033966400⟩]
  caps := #[0, 1376703109255240166400, 220562088864846220800, 2908853278899554448, 0, 1247042053879221600, 3115060175369056200, 0, 0, 3133532616653543104, 496645190512136064, 461814716591414550, 262522155434177100, 297237947033966400, 15879790607381380680, 297237947033966400, 6016227368046033600, 631346531508000000, 0] }

theorem case_45_27_16_checked :
    (Witness.linear .conditional case_45_27_16).check 45 27 16 = true := by
  change case_45_27_16.check 45 27 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_27_17 : Certificate := {
  objectiveScale := 513084000000
  eta := 663302005554988800
  rows := #[⟨.count 2, 102903995690496000⟩, ⟨.count 3, 16963080539605200⟩, ⟨.count 4, 3258626530199040⟩, ⟨.count 5, 765654729840000⟩, ⟨.count 6, 190824717283200⟩, ⟨.count 7, 47411696732400⟩, ⟨.count 8, 10494288604800⟩, ⟨.count 9, 2698531355520⟩, ⟨.path 4, 221729326378560⟩, ⟨.path 10, 315797401920⟩, ⟨.privateRow 6 15, 2776550119200⟩, ⟨.privateRow 6 16, 53399509363200⟩, ⟨.privateRow 7 13, 1840516177500⟩, ⟨.privateRow 7 14, 14008957419600⟩, ⟨.privateRow 8 11, 812058046800⟩, ⟨.privateRow 8 12, 6746328388800⟩, ⟨.privateRow 8 13, 18846885657600⟩, ⟨.privateRow 8 15, 36017897675760⟩, ⟨.privateRow 8 17, 313829202086400⟩, ⟨.privateRow 9 9, 284844976416⟩, ⟨.privateRow 9 12, 44675685774720⟩, ⟨.privateRow 9 13, 2473653742560⟩, ⟨.privateRow 9 16, 286693970122560⟩, ⟨.privateRow 10 7, 81773677440⟩, ⟨.privateRow 10 8, 539706271104⟩, ⟨.privateRow 10 9, 1132716865280⟩, ⟨.privateRow 10 10, 2736010957680⟩, ⟨.privateRow 10 11, 17454786148800⟩, ⟨.privateRow 10 14, 113825551759920⟩, ⟨.privateRow 11 5, 15616500900⟩, ⟨.privateRow 11 6, 204434193600⟩, ⟨.privateRow 11 7, 862030849680⟩, ⟨.privateRow 11 11, 49035812826000⟩, ⟨.privateRow 12 10, 12368268712800⟩, ⟨.privateRow 14 4, 918785675808⟩, ⟨.privateRow 14 11, 4593928379040⟩, ⟨.hall 14 3, 18739801080⟩, ⟨.hall 12 4, 34086629280⟩, ⟨.hall 11 5, 18809670825⟩, ⟨.hall 12 5, 7256647200⟩, ⟨.hall 6 15, 143941769400⟩, ⟨.hall 7 15, 131043232320⟩, ⟨.hall 5 17, 501074413840⟩, ⟨.hall 4 19, 178551893520⟩]
  caps := #[0, 0, 77352710909760, 19839080804400, 0, 4527349706880, 3946388160000, 0, 755025036480, 0, 499588181040, 0, 4824241722300, 231625062240, 0, 17173592436000, 22575696000000, 4617756000000, 513084000000] }

theorem case_45_27_17_checked :
    (Witness.linear .negative case_45_27_17).check 45 27 17 = true := by
  change case_45_27_17.check 45 27 17 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_28_1_checked :
    (Witness.rising).check 45 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_28_2_checked :
    (Witness.rising).check 45 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_28_3_checked :
    (Witness.rising).check 45 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_28_4_checked :
    (Witness.rising).check 45 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_28_5_checked :
    (Witness.rising).check 45 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_28_6_checked :
    (Witness.rising).check 45 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_28_7_checked :
    (Witness.rising).check 45 28 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_28_8_checked :
    (Witness.rising).check 45 28 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_28_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_28_9_checked :
    (Witness.linear .positive case_45_28_9).check 45 28 9 = true := by
  change case_45_28_9.check 45 28 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_28_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_28_10_checked :
    (Witness.linear .positive case_45_28_10).check 45 28 10 = true := by
  change case_45_28_10.check 45 28 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_28_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_28_11_checked :
    (Witness.linear .positive case_45_28_11).check 45 28 11 = true := by
  change case_45_28_11.check 45 28 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_28_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_45_28_12_checked :
    (Witness.linear .positive case_45_28_12).check 45 28 12 = true := by
  change case_45_28_12.check 45 28 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_28_13 : Certificate := {
  objectiveScale := 10000000
  eta := 19275223968000
  rows := #[⟨.count 2, 3982207729500⟩, ⟨.count 3, 789748759800⟩, ⟨.count 4, 163176499200⟩, ⟨.count 5, 33831666000⟩, ⟨.count 6, 7109553000⟩, ⟨.count 7, 1560090000⟩, ⟨.count 8, 312018000⟩, ⟨.count 9, 62403600⟩, ⟨.path 9, 24727911⟩]
  caps := #[0, 41173189525, 0, 745070560, 72242248, 0, 0, 0, 25805288, 12324311, 20000000, 10000000, 10000000, 0, 0, 0, 0, 0] }

theorem case_45_28_13_checked :
    (Witness.linear .positive case_45_28_13).check 45 28 13 = true := by
  change case_45_28_13.check 45 28 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_28_14 : Certificate := {
  objectiveScale := 248648400000
  eta := 376242734243376000
  rows := #[⟨.count 2, 72756340703046000⟩, ⟨.count 3, 14470874393976000⟩, ⟨.count 4, 2894174878795200⟩, ⟨.count 5, 644916868596000⟩, ⟨.count 6, 136934403606000⟩, ⟨.count 7, 30920671782000⟩, ⟨.count 8, 6746328388800⟩, ⟨.count 9, 2248776129600⟩, ⟨.path 9, 507965005548⟩, ⟨.privateRow 2 26, 5225593531158000⟩, ⟨.privateRow 3 23, 902196489994800⟩, ⟨.privateRow 3 24, 2050040539146600⟩, ⟨.privateRow 4 20, 109105799002200⟩, ⟨.privateRow 4 21, 525430558352700⟩, ⟨.privateRow 4 22, 817336424104200⟩, ⟨.privateRow 4 23, 1260459098999100⟩, ⟨.privateRow 5 18, 106897179589200⟩, ⟨.privateRow 5 19, 209907189011520⟩, ⟨.privateRow 5 20, 325550501476200⟩, ⟨.privateRow 5 21, 502387295810400⟩, ⟨.privateRow 5 22, 478828688738400⟩, ⟨.privateRow 6 15, 10398916402875⟩, ⟨.privateRow 6 16, 50482729440000⟩, ⟨.privateRow 6 17, 89694488383500⟩, ⟨.privateRow 6 18, 129719580190200⟩, ⟨.privateRow 6 19, 199143850405500⟩, ⟨.privateRow 6 20, 200248160112000⟩, ⟨.privateRow 6 21, 116320622418000⟩, ⟨.privateRow 7 13, 8923714800000⟩, ⟨.privateRow 7 14, 22638348983250⟩, ⟨.privateRow 7 15, 39927249648000⟩, ⟨.privateRow 7 16, 56353258962000⟩, ⟨.privateRow 7 17, 83766910827600⟩, ⟨.privateRow 7 18, 67362892096500⟩, ⟨.privateRow 8 10, 408868387200⟩, ⟨.privateRow 8 11, 4975417186740⟩, ⟨.privateRow 8 12, 11275113649800⟩, ⟨.privateRow 8 13, 18974048593500⟩, ⟨.privateRow 8 14, 27065626988400⟩, ⟨.privateRow 8 15, 31529715317100⟩, ⟨.privateRow 9 8, 416440024000⟩, ⟨.privateRow 9 9, 2680359427200⟩, ⟨.privateRow 9 10, 6171641155680⟩, ⟨.privateRow 9 11, 10327712595200⟩, ⟨.privateRow 9 12, 10244424590400⟩, ⟨.privateRow 10 6, 302719863600⟩, ⟨.privateRow 10 7, 1569458340450⟩, ⟨.privateRow 10 8, 3756478307400⟩, ⟨.privateRow 10 9, 3148286581440⟩, ⟨.privateRow 11 4, 172100214000⟩, ⟨.privateRow 11 5, 1050252588000⟩, ⟨.privateRow 11 6, 1104309706500⟩, ⟨.privateRow 12 2, 98160862800⟩, ⟨.privateRow 12 3, 420689412000⟩, ⟨.privateRow 13 1, 117793035360⟩, ⟨.hall 5 22, 1920538620000⟩, ⟨.hall 4 23, 309133097172900⟩, ⟨.hall 3 24, 993666708386352⟩, ⟨.hall 2 25, 2257209040086000⟩, ⟨.assumptionRow 14, 311648337000⟩]
  caps := #[0, 1602393540848100, 52985181285036, 16537428267360, 8723645114184, 2591446777920, 908498600295, 1337473797660, 3592329571740, 792479839788, 686296611000, 311648337000, 3190923106800, 0, 2920780863000, 248648400000, 0, 0] }

theorem case_45_28_14_checked :
    (Witness.linear .conditional case_45_28_14).check 45 28 14 = true := by
  change case_45_28_14.check 45 28 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_28_15 : Certificate := {
  objectiveScale := 4531365158553090000000
  eta := 7679439735635884339835712000
  rows := #[⟨.count 2, 1396821169863257808607938000⟩, ⟨.count 3, 258442683410823030667548000⟩, ⟨.count 4, 46414196204392707548457600⟩, ⟨.count 5, 9061046461813261671756000⟩, ⟨.count 6, 1758113492590632861684000⟩, ⟨.count 7, 344245998549214826064000⟩, ⟨.count 8, 103273799564764447819200⟩, ⟨.count 9, 34424599854921482606400⟩, ⟨.path 7, 22753474979400957792000⟩, ⟨.path 8, 12188716059754778544000⟩, ⟨.privateRow 2 26, 138451437541512337857615000⟩, ⟨.privateRow 3 23, 22015487846107147056865200⟩, ⟨.privateRow 3 24, 45535139458097391117615600⟩, ⟨.privateRow 4 20, 2426196619775073349123920⟩, ⟨.privateRow 4 21, 10812397979432392099356600⟩, ⟨.privateRow 4 22, 17932757624424455189176800⟩, ⟨.privateRow 4 23, 29272589651634037147038600⟩, ⟨.privateRow 5 18, 1911384925278021367574400⟩, ⟨.privateRow 5 19, 4127509522605085764507360⟩, ⟨.privateRow 5 20, 6958072245676004671818600⟩, ⟨.privateRow 5 21, 11801900316928914953560800⟩, ⟨.privateRow 5 22, 12631369246766546867791200⟩, ⟨.privateRow 6 15, 114108327644103575157375⟩, ⟨.privateRow 6 16, 840416889315302521794000⟩, ⟨.privateRow 6 17, 1690493742875608520850000⟩, ⟨.privateRow 6 18, 2734091880144150847721400⟩, ⟨.privateRow 6 19, 4691120136479813645358750⟩, ⟨.privateRow 6 20, 5511009601774483777971000⟩, ⟨.privateRow 6 21, 4243139294617777387333500⟩, ⟨.privateRow 7 13, 84695444087505234984000⟩, ⟨.privateRow 7 14, 349624842276546307721250⟩, ⟨.privateRow 7 15, 724497318375260794650000⟩, ⟨.privateRow 7 16, 1165928411752995452562000⟩, ⟨.privateRow 7 17, 1587219943310844073030800⟩, ⟨.privateRow 7 18, 3219622173931272591982500⟩, ⟨.privateRow 7 19, 1004050829101876576020000⟩, ⟨.privateRow 8 11, 43030749818651853258000⟩, ⟨.privateRow 8 12, 154910699347146671728800⟩, ⟨.privateRow 8 13, 328109467367220381092250⟩, ⟨.privateRow 8 14, 544646347704650599808400⟩, ⟨.privateRow 8 15, 930898554410168425481400⟩, ⟨.privateRow 8 16, 996592165799976921455280⟩, ⟨.privateRow 9 9, 18777054466320808694400⟩, ⟨.privateRow 9 10, 74586633018996545647200⟩, ⟨.privateRow 9 11, 163623098075861367944000⟩, ⟨.privateRow 9 12, 252447065602757539113600⟩, ⟨.privateRow 9 13, 554618553218179441992000⟩, ⟨.privateRow 10 7, 7530381218264074320150⟩, ⟨.privateRow 10 8, 38336486202071651084400⟩, ⟨.privateRow 10 9, 91655497113728447439540⟩, ⟨.privateRow 10 10, 165429327080594902525200⟩, ⟨.privateRow 10 11, 56477859136980557401125⟩, ⟨.privateRow 11 5, 2837192295735287028000⟩, ⟨.privateRow 11 6, 20490833246977072980000⟩, ⟨.privateRow 11 7, 57560613393781050462000⟩, ⟨.privateRow 11 8, 31350974867874921659400⟩, ⟨.privateRow 12 3, 804997020416956438500⟩, ⟨.privateRow 12 4, 11269958285837390139000⟩, ⟨.privateRow 12 5, 19722427000215432743250⟩, ⟨.privateRow 13 2, 5795978547002086357200⟩, ⟨.privateRow 13 3, 2080607683539210487200⟩, ⟨.hall 5 22, 1552314254327515302624000⟩, ⟨.hall 4 23, 9361954348045119988467300⟩, ⟨.hall 3 24, 25253542207571850425228976⟩, ⟨.hall 2 25, 53960560272589423985532000⟩, ⟨.assumptionRow 15, 4250547396947237906520⟩]
  caps := #[0, 0, 3301941601442294234853000, 688753140541619558461056, 161732375834512975988496, 0, 79408089767791492690125, 17280393362476210120440, 0, 0, 31449875002027496407575, 4538682267584501266560, 1835556335696368591020, 0, 293658001048273837215240, 50125834505689842093480, 4531365158553090000000, 0] }

theorem case_45_28_15_checked :
    (Witness.linear .conditional case_45_28_15).check 45 28 15 = true := by
  change case_45_28_15.check 45 28 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_28_16 : Certificate := {
  objectiveScale := 2439965854605510000000
  eta := 4709400008819441892164208000
  rows := #[⟨.count 2, 822504095616984407124498000⟩, ⟨.count 3, 141528136153545945365562000⟩, ⟨.count 4, 23089890536023644916783200⟩, ⟨.count 5, 3831785817184712647260000⟩, ⟨.count 6, 586037830863544287228000⟩, ⟨.count 7, 86061499637303706516000⟩, ⟨.count 8, 22949733236614321737600⟩, ⟨.count 9, 11474866618307160868800⟩, ⟨.path 7, 31320413745393028256000⟩, ⟨.path 8, 925879480800962688000⟩, ⟨.privateRow 2 26, 85121994932929807719867000⟩, ⟨.privateRow 3 23, 12580278769204084032494400⟩, ⟨.privateRow 3 24, 27348432106965400070640000⟩, ⟨.privateRow 4 20, 1242400201430713888923360⟩, ⟨.privateRow 4 21, 5984911347693946033315950⟩, ⟨.privateRow 4 22, 10587750144268033455919200⟩, ⟨.privateRow 4 23, 18372285997572113404597800⟩, ⟨.privateRow 5 18, 928644562753000947453600⟩, ⟨.privateRow 5 19, 2201699050721192537555040⟩, ⟨.privateRow 5 20, 4014359141415278367511800⟩, ⟨.privateRow 5 21, 7399103279928441205924800⟩, ⟨.privateRow 5 22, 8736471663181144835752800⟩, ⟨.privateRow 6 15, 45079833143349560556000⟩, ⟨.privateRow 6 16, 385861905119861119521000⟩, ⟨.privateRow 6 17, 860273482485587447277000⟩, ⟨.privateRow 6 18, 1534968318531052536931800⟩, ⟨.privateRow 6 19, 2907649237746046655862000⟩, ⟨.privateRow 6 20, 3866847909629540083248000⟩, ⟨.privateRow 6 21, 3546280207276832097072000⟩, ⟨.privateRow 7 13, 28459490620801490250000⟩, ⟨.privateRow 7 14, 148814676456170992517250⟩, ⟨.privateRow 7 15, 349222343766337829502000⟩, ⟨.privateRow 7 16, 629751608457095376252000⟩, ⟨.privateRow 7 17, 1202402094932614642466400⟩, ⟨.privateRow 7 18, 1235084973961543073869500⟩, ⟨.privateRow 7 19, 2728012932947547649404000⟩, ⟨.privateRow 8 11, 11474866618307160868800⟩, ⟨.privateRow 8 12, 59446184008730152834200⟩, ⟨.privateRow 8 13, 147918202501615745574375⟩, ⟨.privateRow 8 14, 279290057156297504717400⟩, ⟨.privateRow 8 15, 544578044927160676231800⟩, ⟨.privateRow 8 16, 807830609928824125163520⟩, ⟨.privateRow 8 17, 649047143097998786641500⟩, ⟨.privateRow 9 9, 3477232308577927536000⟩, ⟨.privateRow 9 10, 24607213970369800529760⟩, ⟨.privateRow 9 11, 67149219470093756195200⟩, ⟨.privateRow 9 12, 134351563322679675172200⟩, ⟨.privateRow 9 13, 245525717483778616684800⟩, ⟨.privateRow 9 14, 489169313987834894814400⟩, ⟨.privateRow 10 7, 597649303036831295250⟩, ⟨.privateRow 10 8, 10040508291018765760200⟩, ⟨.privateRow 10 9, 32846805694904247986940⟩, ⟨.privateRow 10 10, 71558543216943267084600⟩, ⟨.privateRow 10 11, 154731404556235622340225⟩, ⟨.privateRow 10 12, 95077466265973618627200⟩, ⟨.privateRow 11 6, 3585895818220987771500⟩, ⟨.privateRow 11 7, 16765227202072150620000⟩, ⟨.privateRow 11 8, 42416024821242541068600⟩, ⟨.privateRow 11 9, 66253694165225869302000⟩, ⟨.privateRow 12 4, 866919868141337703000⟩, ⟨.privateRow 12 5, 8139414317549226211500⟩, ⟨.privateRow 12 6, 27321110995969430640000⟩, ⟨.privateRow 12 7, 6010644419113274740800⟩, ⟨.privateRow 13 3, 3467679472565350812000⟩, ⟨.privateRow 13 4, 9767297181059071453800⟩, ⟨.privateRow 14 2, 2253991657167478027800⟩, ⟨.hall 5 22, 1926672868691852957676000⟩, ⟨.hall 4 23, 7178963428078417518543000⟩, ⟨.hall 3 24, 17098239753274768124164128⟩, ⟨.hall 2 25, 34159243564373129511309000⟩, ⟨.assumptionRow 16, 1443843985020299577000⟩]
  caps := #[0, 8270222573469222589652000, 241848650545744722337000, 0, 92981622690654056146018, 56911226481952243561160, 7178377348239002691500, 16519797470657988692900, 1952941840890515897565, 0, 5138076436679501049735, 1443843985020299577000, 39966415679364995736300, 0, 174010101399437375872800, 141271652729114555076000, 25395780415640310423000, 2439965854605510000000] }

theorem case_45_28_16_checked :
    (Witness.linear .conditional case_45_28_16).check 45 28 16 = true := by
  change case_45_28_16.check 45 28 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_28_17 : Certificate := {
  objectiveScale := 196462210230000000
  eta := 417998880721092054384000
  rows := #[⟨.count 2, 82930382918864348868000⟩, ⟨.count 3, 15805117820859797430000⟩, ⟨.count 4, 3134460340943623692000⟩, ⟨.count 5, 576217611568514916000⟩, ⟨.count 6, 108296217777061314000⟩, ⟨.count 7, 18204166967670684000⟩, ⟨.count 8, 2080476224876649600⟩, ⟨.path 8, 785227648933728000⟩, ⟨.path 9, 211875827963563764⟩, ⟨.privateRow 3 23, 1094995090856953286000⟩, ⟨.privateRow 3 24, 3340768041350365025400⟩, ⟨.privateRow 4 20, 37188512519670111600⟩, ⟨.privateRow 4 21, 608297811928889682600⟩, ⟨.privateRow 4 22, 1051018199067819582600⟩, ⟨.privateRow 5 18, 57621761156851491600⟩, ⟨.privateRow 5 19, 227544656823651847680⟩, ⟨.privateRow 5 21, 1731649711172331350400⟩, ⟨.privateRow 5 22, 290560795620719223600⟩, ⟨.privateRow 6 17, 152170943323009110500⟩, ⟨.privateRow 6 18, 33169973621024440200⟩, ⟨.privateRow 6 19, 396319885025330516250⟩, ⟨.privateRow 6 20, 600396955789179549000⟩, ⟨.privateRow 6 21, 389934494826211335000⟩, ⟨.privateRow 7 13, 1279657995459844000⟩, ⟨.privateRow 7 14, 7337393828806041000⟩, ⟨.privateRow 7 15, 31366363492400508000⟩, ⟨.privateRow 7 16, 90742199629664583000⟩, ⟨.privateRow 7 17, 75974533569156222000⟩, ⟨.privateRow 7 18, 230524195988564478000⟩, ⟨.privateRow 7 19, 286189318791067692000⟩, ⟨.privateRow 7 20, 189379063505512881000⟩, ⟨.privateRow 8 11, 936214301194492320⟩, ⟨.privateRow 8 12, 3987579431013578400⟩, ⟨.privateRow 8 13, 11458872957328421625⟩, ⟨.privateRow 8 16, 294933510829076038920⟩, ⟨.privateRow 8 18, 65968433630463764400⟩, ⟨.privateRow 9 9, 462328049972588800⟩, ⟨.privateRow 9 10, 1895545004887614080⟩, ⟨.privateRow 9 12, 21498254323725379200⟩, ⟨.privateRow 9 13, 1353960717776867200⟩, ⟨.privateRow 9 14, 9362143011944923200⟩, ⟨.privateRow 9 16, 171639288552323592000⟩, ⟨.privateRow 10 7, 10835813671232550⟩, ⟨.privateRow 10 8, 1276655865265216800⟩, ⟨.privateRow 10 9, 13002976405479060⟩, ⟨.privateRow 10 11, 2210505988931440200⟩, ⟨.privateRow 10 13, 69327535868545854900⟩, ⟨.privateRow 11 7, 2229081669510696000⟩, ⟨.privateRow 11 9, 784306513346356000⟩, ⟨.privateRow 11 10, 3691916515127090250⟩, ⟨.privateRow 11 11, 1486054446340464000⟩, ⟨.privateRow 11 12, 20309410766653008000⟩, ⟨.privateRow 12 5, 425692679941278750⟩, ⟨.privateRow 12 11, 13905960878081772500⟩, ⟨.hall 13 3, 29190355195973400⟩, ⟨.hall 12 4, 20657789830996560⟩, ⟨.hall 10 12, 1120704710664000⟩, ⟨.hall 3 21, 2180599143198838362⟩, ⟨.hall 4 21, 5296895699089094100⟩, ⟨.hall 5 21, 17792271441782838000⟩]
  caps := #[0, 0, 131248136877687285456, 35311281253354334800, 12859590527503166304, 2351588283994666860, 777981972398706504, 131948695433925942, 1873730802231165735, 211875827963563764, 0, 2267603046993212500, 0, 8359066262377630800, 0, 40864139727840000000, 10608959352420000000, 1964622102300000000] }

theorem case_45_28_17_checked :
    (Witness.linear .negative case_45_28_17).check 45 28 17 = true := by
  change case_45_28_17.check 45 28 17 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_28_18 : Certificate := {
  objectiveScale := 91940742347454000000
  eta := 225351080561394896582073600
  rows := #[⟨.count 2, 41296132481517754106666400⟩, ⟨.count 3, 7001198619383142418083840⟩, ⟨.count 4, 1195517174961630345945120⟩, ⟨.count 5, 180319332573398242224000⟩, ⟨.count 6, 25545238781231417648400⟩, ⟨.count 7, 2868716654576790217200⟩, ⟨.path 7, 1226093988527305497600⟩, ⟨.path 8, 131166259780136380800⟩, ⟨.privateRow 6 16, 6690419680798704622200⟩, ⟨.privateRow 7 14, 3449290263241140618300⟩, ⟨.privateRow 8 11, 76499110788714405792⟩, ⟨.privateRow 8 12, 1094362279338553305080⟩, ⟨.privateRow 9 9, 38635914539754750400⟩, ⟨.privateRow 9 10, 356995850347333893696⟩, ⟨.privateRow 10 8, 17386161542889637680⟩, ⟨.privateRow 13 7, 66784937990147497120⟩, ⟨.hall 12 4, 1981531127180200464⟩, ⟨.hall 13 4, 4293317442223767672⟩, ⟨.hall 14 5, 4553518499328238440⟩, ⟨.hall 10 7, 3185059131317451850⟩, ⟨.hall 9 9, 3282419519677485180⟩, ⟨.hall 10 9, 1295252176999373460⟩, ⟨.hall 11 9, 3986904206425403340⟩, ⟨.hall 12 9, 3677841864842038740⟩, ⟨.hall 13 9, 2732111099596943064⟩, ⟨.hall 8 12, 5280302995220066352⟩, ⟨.hall 6 14, 5329472825645653685⟩, ⟨.hall 7 14, 12048732128253460640⟩]
  caps := #[0, 0, 0, 0, 29248776181489344480, 0, 1415236063763937472200, 0, 338344752197398290344, 0, 0, 809022346648382867000, 255135049232282919700, 3385695648579173697768, 0, 0, 14158874321507916000000, 4045392663287976000000] }

theorem case_45_28_18_checked :
    (Witness.linear .negative case_45_28_18).check 45 28 18 = true := by
  change case_45_28_18.check 45 28 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_29_1_checked :
    (Witness.rising).check 45 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_29_2_checked :
    (Witness.rising).check 45 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_29_3_checked :
    (Witness.rising).check 45 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_29_4_checked :
    (Witness.rising).check 45 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_29_5_checked :
    (Witness.rising).check 45 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_29_6_checked :
    (Witness.rising).check 45 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_29_7_checked :
    (Witness.rising).check 45 29 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_29_8_checked :
    (Witness.rising).check 45 29 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_29_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_29_9_checked :
    (Witness.linear .positive case_45_29_9).check 45 29 9 = true := by
  change case_45_29_9.check 45 29 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_29_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_29_10_checked :
    (Witness.linear .positive case_45_29_10).check 45 29 10 = true := by
  change case_45_29_10.check 45 29 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_29_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_45_29_11_checked :
    (Witness.linear .positive case_45_29_11).check 45 29 11 = true := by
  change case_45_29_11.check 45 29 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_29_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_45_29_12_checked :
    (Witness.linear .positive case_45_29_12).check 45 29 12 = true := by
  change case_45_29_12.check 45 29 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_29_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_45_29_13_checked :
    (Witness.linear .positive case_45_29_13).check 45 29 13 = true := by
  change case_45_29_13.check 45 29 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_29_14 : Certificate := {
  objectiveScale := 7276650000
  eta := 66136042161459270
  rows := #[⟨.count 2, 8954501928390018⟩, ⟨.count 3, 1191552649644357⟩, ⟨.count 4, 155843398318608⟩, ⟨.count 5, 20396171254305⟩, ⟨.count 6, 3632713247520⟩, ⟨.count 7, 953587227474⟩, ⟨.count 8, 282544363696⟩, ⟨.count 9, 158931204579⟩, ⟨.path 5, 2753309235600⟩, ⟨.path 6, 461657308539⟩]
  caps := #[0, 0, 10136005199796, 646510188513, 0, 149264417919, 0, 6930572526, 23074936304, 0, 36383250000, 14553300000, 7276650000, 7276650000, 0, 0, 0] }

theorem case_45_29_14_checked :
    (Witness.linear .positive case_45_29_14).check 45 29 14 = true := by
  change case_45_29_14.check 45 29 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_29_15 : Certificate := {
  objectiveScale := 202481370000000
  eta := 841406579825335524000
  rows := #[⟨.count 2, 132946656444843040800⟩, ⟨.count 3, 21011502893276095200⟩, ⟨.count 4, 3407270739450177600⟩, ⟨.count 5, 533902822420968000⟩, ⟨.count 6, 86042190390156000⟩, ⟨.count 7, 13899123063025200⟩, ⟨.count 8, 4118258685340800⟩, ⟨.path 6, 2032864937789400⟩, ⟨.path 7, 4122756237600000⟩, ⟨.privateRow 2 27, 11704605966074221200⟩, ⟨.privateRow 3 23, 141969614143757400⟩, ⟨.privateRow 3 24, 2460806645158461600⟩, ⟨.privateRow 3 25, 3864728385024507000⟩, ⟨.privateRow 4 21, 483424737392076480⟩, ⟨.privateRow 4 22, 1039290380462634300⟩, ⟨.privateRow 4 23, 1531330367943776400⟩, ⟨.privateRow 4 24, 2275154072816625000⟩, ⟨.privateRow 5 18, 63444296430543600⟩, ⟨.privateRow 5 19, 238638382748766000⟩, ⟨.privateRow 5 20, 404795412635533920⟩, ⟨.privateRow 5 21, 594573597696078000⟩, ⟨.privateRow 5 22, 916533178489328400⟩, ⟨.privateRow 5 23, 834829867785513600⟩, ⟨.privateRow 6 15, 4657554465564000⟩, ⟨.privateRow 6 16, 43158983320703250⟩, ⟨.privateRow 6 17, 101485660460184000⟩, ⟨.privateRow 6 18, 169694319936141000⟩, ⟨.privateRow 6 19, 241138754093437200⟩, ⟨.privateRow 6 20, 287910406305522000⟩, ⟨.privateRow 6 21, 541992259124316000⟩, ⟨.privateRow 7 13, 4302109519507800⟩, ⟨.privateRow 7 14, 22135640433706800⟩, ⟨.privateRow 7 15, 46330410210084000⟩, ⟨.privateRow 7 16, 76492452775424400⟩, ⟨.privateRow 7 17, 108766153493197200⟩, ⟨.privateRow 7 18, 165995241152700960⟩, ⟨.privateRow 7 19, 90675231411164400⟩, ⟨.privateRow 8 11, 2620710072489600⟩, ⟨.privateRow 8 12, 11273733151120440⟩, ⟨.privateRow 8 13, 23622789403413200⟩, ⟨.privateRow 8 14, 38801718550945350⟩, ⟨.privateRow 8 15, 55449411584767200⟩, ⟨.privateRow 8 16, 51564030622704600⟩, ⟨.privateRow 9 9, 1458549951058200⟩, ⟨.privateRow 9 10, 6270984816314400⟩, ⟨.privateRow 9 11, 13693210128758160⟩, ⟨.privateRow 9 12, 22993610993152800⟩, ⟨.privateRow 9 13, 17759990580532200⟩, ⟨.privateRow 10 7, 814600619078400⟩, ⟨.privateRow 10 8, 3916022767757100⟩, ⟨.privateRow 10 9, 9205912678107600⟩, ⟨.privateRow 10 10, 6022953327310920⟩, ⟨.privateRow 11 5, 551552502501000⟩, ⟨.privateRow 11 6, 2800189628082000⟩, ⟨.privateRow 11 7, 2665837095421500⟩, ⟨.privateRow 12 3, 323577468133920⟩, ⟨.privateRow 12 4, 1213415505502200⟩, ⟨.privateRow 13 1, 455030814563325⟩, ⟨.hall 4 24, 358782696666890496⟩, ⟨.hall 3 25, 1445177867053120200⟩, ⟨.hall 2 26, 3713410977356880800⟩, ⟨.assumptionRow 15, 203407722267750⟩]
  caps := #[0, 1633636780582716000, 0, 114142972293643800, 12633319037022840, 5649980239784400, 747792300362250, 1512956648753550, 5666645243170730, 1632819891748500, 8008834127544180, 203407722267750, 17495673739918920, 0, 15375615188251500, 2428850087732250, 202481370000000] }

theorem case_45_29_15_checked :
    (Witness.linear .conditional case_45_29_15).check 45 29 15 = true := by
  change case_45_29_15.check 45 29 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_29_16 : Certificate := {
  objectiveScale := 6675135831000000
  eta := 32690633200812297711000
  rows := #[⟨.count 2, 4776583442268289251600⟩, ⟨.count 3, 681690763913608449000⟩, ⟨.count 4, 95796727328387685600⟩, ⟨.count 5, 12261563683099731000⟩, ⟨.count 6, 1423005456452580000⟩, ⟨.count 7, 199220763903361200⟩, ⟨.count 8, 88542561734827200⟩, ⟨.path 6, 501101207165087100⟩, ⟨.path 7, 29931210284976000⟩, ⟨.privateRow 2 27, 441572823191800099800⟩, ⟨.privateRow 3 23, 4917669689924041050⟩, ⟨.privateRow 3 24, 86370106737976261200⟩, ⟨.privateRow 3 25, 143121145458478987800⟩, ⟨.privateRow 4 21, 15120855980265115080⟩, ⟨.privateRow 4 22, 35532446247620922600⟩, ⟨.privateRow 4 23, 56351016075522168000⟩, ⟨.privateRow 4 24, 89692033920206117400⟩, ⟨.privateRow 5 18, 1647298221255343800⟩, ⟨.privateRow 5 19, 7200407609650054800⟩, ⟨.privateRow 5 20, 13472066991388725720⟩, ⟨.privateRow 5 21, 21640355479002610350⟩, ⟨.privateRow 5 22, 36645552738001607400⟩, ⟨.privateRow 5 23, 37958670550872571500⟩, ⟨.privateRow 6 15, 65879882243175000⟩, ⟨.privateRow 6 16, 1061324902937549250⟩, ⟨.privateRow 6 17, 2937489835105683000⟩, ⟨.privateRow 6 18, 5482523800277023500⟩, ⟨.privateRow 6 19, 8666103229796212200⟩, ⟨.privateRow 6 20, 14923769724546432750⟩, ⟨.privateRow 6 21, 17439722427413286000⟩, ⟨.privateRow 6 22, 12558023153194018500⟩, ⟨.privateRow 7 13, 45536174606482560⟩, ⟨.privateRow 7 14, 507538612801420200⟩, ⟨.privateRow 7 15, 1270032369883927650⟩, ⟨.privateRow 7 16, 2384550572026966200⟩, ⟨.privateRow 7 17, 3808911271771405800⟩, ⟨.privateRow 7 18, 4596307624341833400⟩, ⟨.privateRow 7 19, 12205829302722004950⟩, ⟨.privateRow 8 11, 17104813062409800⟩, ⟨.privateRow 8 12, 234637788597292080⟩, ⟨.privateRow 8 13, 603811080719446600⟩, ⟨.privateRow 8 14, 1146902869971433575⟩, ⟨.privateRow 8 15, 1862556030779043600⟩, ⟨.privateRow 8 16, 3272385510782988600⟩, ⟨.privateRow 8 17, 2525676573485945880⟩, ⟨.privateRow 9 9, 3689273405617800⟩, ⟨.privateRow 9 10, 109672036694274600⟩, ⟨.privateRow 9 11, 318753222245377920⟩, ⟨.privateRow 9 12, 630865752360643800⟩, ⟨.privateRow 9 13, 1047292488019752975⟩, ⟨.privateRow 9 14, 1490993494927536600⟩, ⟨.privateRow 10 8, 50991028856217450⟩, ⟨.privateRow 10 9, 187577991986931000⟩, ⟨.privateRow 10 10, 404133549632532720⟩, ⟨.privateRow 10 11, 641933572577497200⟩, ⟨.privateRow 11 6, 23716757607543000⟩, ⟨.privateRow 11 7, 120560184505010250⟩, ⟨.privateRow 11 8, 291069297910755000⟩, ⟨.privateRow 12 4, 14907676210455600⟩, ⟨.privateRow 12 5, 84285707805268200⟩, ⟨.privateRow 12 6, 43480722280495500⟩, ⟨.privateRow 13 2, 10435373347318920⟩, ⟨.privateRow 13 3, 33542271473525100⟩, ⟨.hall 5 23, 54350902850619375⟩, ⟨.hall 4 24, 20060961722885891808⟩, ⟨.hall 3 25, 62612240083913520000⟩, ⟨.hall 2 26, 146311664235594457600⟩, ⟨.assumptionRow 16, 4622386451319000⟩]
  caps := #[0, 0, 1007247562873016400, 0, 0, 0, 63922225217615700, 59135418710058015, 27065313108342145, 133139231933667960, 16837972089038100, 224141532206728500, 1640851209227880, 0, 1920282760231290000, 453894435119853000, 75479243520681000] }

theorem case_45_29_16_checked :
    (Witness.linear .conditional case_45_29_16).check 45 29 16 = true := by
  change case_45_29_16.check 45 29 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_29_17 : Certificate := {
  objectiveScale := 16856169089760000
  eta := 111247862875095444498000
  rows := #[⟨.count 2, 16371431122207814452800⟩, ⟨.count 3, 2344202268741722188800⟩, ⟨.count 4, 323079158832993763200⟩, ⟨.count 5, 39654418719811896000⟩, ⟨.count 6, 3984415278067224000⟩, ⟨.count 7, 199220763903361200⟩, ⟨.path 6, 1415551618347352200⟩, ⟨.path 7, 206962363127520000⟩, ⟨.privateRow 2 27, 1566871308099935838000⟩, ⟨.privateRow 3 23, 11870237182575271500⟩, ⟨.privateRow 3 24, 296190680174735346000⟩, ⟨.privateRow 3 25, 503298056541191511600⟩, ⟨.privateRow 4 21, 49588894146459507840⟩, ⟨.privateRow 4 22, 120606827461638417900⟩, ⟨.privateRow 4 23, 196393726396542074400⟩, ⟨.privateRow 4 24, 322453036432154628000⟩, ⟨.privateRow 5 18, 5888532103129962000⟩, ⟨.privateRow 5 19, 23410020875818777200⟩, ⟨.privateRow 5 20, 44830363900082080320⟩, ⟨.privateRow 5 21, 74325946666279007700⟩, ⟨.privateRow 5 22, 131172642975798824400⟩, ⟨.privateRow 5 23, 143955975326264501400⟩, ⟨.privateRow 6 15, 527039057945400000⟩, ⟨.privateRow 6 16, 3539726072925792750⟩, ⟨.privateRow 6 17, 9398612229046326000⟩, ⟨.privateRow 6 18, 17795473791526431000⟩, ⟨.privateRow 6 19, 29143151748148838400⟩, ⟨.privateRow 6 20, 52746068919175632000⟩, ⟨.privateRow 6 21, 66169753725044970000⟩, ⟨.privateRow 6 22, 53765889496299981000⟩, ⟨.privateRow 7 12, 23285543832860400⟩, ⟨.privateRow 7 13, 387057484155101760⟩, ⟨.privateRow 7 14, 1663335266875682400⟩, ⟨.privateRow 7 15, 3970185223502698200⟩, ⟨.privateRow 7 16, 7533797459447516400⟩, ⟨.privateRow 7 17, 12465527798524600800⟩, ⟨.privateRow 7 18, 22768087303241280000⟩, ⟨.privateRow 7 19, 30786723050351568300⟩, ⟨.privateRow 7 20, 19039813007335520400⟩, ⟨.privateRow 8 10, 18446367028089000⟩, ⟨.privateRow 8 11, 215319411491511600⟩, ⟨.privateRow 8 12, 790242363483332760⟩, ⟨.privateRow 8 13, 1849555734016390400⟩, ⟨.privateRow 8 14, 3525100739067807900⟩, ⟨.privateRow 8 15, 5916540464495060400⟩, ⟨.privateRow 8 16, 10990345475335426200⟩, ⟨.privateRow 8 17, 15813701525840137920⟩, ⟨.privateRow 8 18, 160483393144374300⟩, ⟨.privateRow 9 8, 10216449430941600⟩, ⟨.privateRow 9 9, 118056748979769600⟩, ⟨.privateRow 9 10, 414540175394872800⟩, ⟨.privateRow 9 11, 980608871213211240⟩, ⟨.privateRow 9 12, 1893827014883804000⟩, ⟨.privateRow 9 13, 1162121122769607000⟩, ⟨.privateRow 9 14, 10195043536895817600⟩, ⟨.privateRow 9 15, 852222156697711800⟩, ⟨.privateRow 10 6, 6098594813368200⟩, ⟨.privateRow 10 7, 72244892404515600⟩, ⟨.privateRow 10 8, 253769306400710100⟩, ⟨.privateRow 10 9, 613185987598657200⟩, ⟨.privateRow 10 10, 1209554637984693000⟩, ⟨.privateRow 10 11, 2093399138159128800⟩, ⟨.privateRow 10 12, 1647128815843861350⟩, ⟨.privateRow 11 4, 6324468695344800⟩, ⟨.privateRow 11 5, 54209731674384000⟩, ⟨.privateRow 11 6, 189734060860344000⟩, ⟨.privateRow 11 7, 466429566281679000⟩, ⟨.privateRow 11 8, 948670304301720000⟩, ⟨.privateRow 11 9, 445875043021808400⟩, ⟨.privateRow 12 2, 6522108342074325⟩, ⟨.privateRow 12 3, 48698408954154960⟩, ⟨.privateRow 12 4, 178892114525467200⟩, ⟨.privateRow 12 5, 449523774961430400⟩, ⟨.privateRow 12 6, 34784577824396400⟩, ⟨.privateRow 13 1, 58698975078668925⟩, ⟨.privateRow 13 2, 166965973557102720⟩, ⟨.privateRow 14 0, 84787408446966225⟩, ⟨.hall 5 23, 7500424593385473750⟩, ⟨.hall 4 24, 82297528366295930688⟩, ⟨.hall 3 25, 234795900314675700000⟩, ⟨.hall 2 26, 527566097003345400000⟩, ⟨.assumptionRow 17, 3062552319262800⟩]
  caps := #[0, 42810135491673108000, 0, 1857724247214037800, 151020723160312200, 397030462408153860, 324804647643767850, 71936131195253520, 3062552319262800, 298865576723264320, 113653295750400300, 86807275181593200, 0, 1100726247522823740, 0, 4365917632921244400, 1058900363003246400] }

theorem case_45_29_17_checked :
    (Witness.linear .conditional case_45_29_17).check 45 29 17 = true := by
  change case_45_29_17.check 45 29 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_29_18 : Certificate := {
  objectiveScale := 667693276250000
  eta := 5976720948279750669000
  rows := #[⟨.count 2, 807296075885095196400⟩, ⟨.count 3, 103628067711958389600⟩, ⟨.count 4, 11999941670532816000⟩, ⟨.count 5, 1142851587669792000⟩, ⟨.count 6, 77921699159304000⟩, ⟨.path 5, 169197915991104000⟩, ⟨.path 6, 68274250691961600⟩, ⟨.privateRow 7 13, 4870106197456500⟩, ⟨.privateRow 7 14, 13203399024215400⟩, ⟨.privateRow 8 11, 275480754603600⟩, ⟨.privateRow 8 12, 8181778411726920⟩, ⟨.privateRow 9 10, 3030288300639600⟩, ⟨.privateRow 9 11, 4393918035927420⟩, ⟨.privateRow 10 8, 1298694985988400⟩, ⟨.privateRow 11 6, 499498071534000⟩, ⟨.privateRow 11 8, 1770947708166000⟩, ⟨.privateRow 12 5, 1648343636062200⟩, ⟨.hall 11 6, 40015811893200⟩, ⟨.hall 12 6, 27703254387600⟩, ⟨.hall 10 7, 32797280496750⟩, ⟨.hall 13 7, 16233687324855⟩, ⟨.hall 9 8, 28005913546380⟩, ⟨.hall 8 9, 23397541245540⟩, ⟨.hall 7 11, 19497951037950⟩, ⟨.hall 6 15, 70561383984000⟩, ⟨.hall 5 17, 230435690914000⟩, ⟨.hall 4 19, 949660625468412⟩, ⟨.hall 3 22, 24805780044870825⟩]
  caps := #[0, 993504157859499000, 664966040049511200, 164614957619655400, 0, 0, 0, 1897851368413000, 187180329964320, 14284390068108160, 0, 45505916103627000, 0, 103524079772313200, 18305777988257760, 425320616971250000, 138880201460000000] }

theorem case_45_29_18_checked :
    (Witness.linear .negative case_45_29_18).check 45 29 18 = true := by
  change case_45_29_18.check 45 29 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_30_1_checked :
    (Witness.rising).check 45 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_30_2_checked :
    (Witness.rising).check 45 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_30_3_checked :
    (Witness.rising).check 45 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_30_4_checked :
    (Witness.rising).check 45 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_30_5_checked :
    (Witness.rising).check 45 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_30_6_checked :
    (Witness.rising).check 45 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_30_7_checked :
    (Witness.rising).check 45 30 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_30_8_checked :
    (Witness.rising).check 45 30 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_30_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_30_9_checked :
    (Witness.linear .positive case_45_30_9).check 45 30 9 = true := by
  change case_45_30_9.check 45 30 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_30_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_45_30_10_checked :
    (Witness.linear .positive case_45_30_10).check 45 30 10 = true := by
  change case_45_30_10.check 45 30 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_45_30_11_checked :
    (Witness.linear .positive case_45_30_11).check 45 30 11 = true := by
  change case_45_30_11.check 45 30 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_30_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_45_30_12_checked :
    (Witness.linear .positive case_45_30_12).check 45 30 12 = true := by
  change case_45_30_12.check 45 30 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_30_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_45_30_13_checked :
    (Witness.linear .positive case_45_30_13).check 45 30 13 = true := by
  change case_45_30_13.check 45 30 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_30_14 : Certificate := {
  objectiveScale := 143
  eta := 38749664
  rows := #[⟨.assumptionRow 14, 411⟩]
  caps := #[0, 0, 11228126, 3300414, 986986, 301444, 94523, 30657, 10398, 3752, 1483, 87723, 39324, 10441, 1734, 143] }

theorem case_45_30_14_checked :
    (Witness.linear .conditional case_45_30_14).check 45 30 14 = true := by
  change case_45_30_14.check 45 30 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_30_15 : Certificate := {
  objectiveScale := 6424317900000
  eta := 66960015885789586560
  rows := #[⟨.count 2, 9063407238291806400⟩, ⟨.count 3, 1209574274619110400⟩, ⟨.count 4, 156236677138301760⟩, ⟨.count 5, 19090503071640000⟩, ⟨.count 6, 2290860368596800⟩, ⟨.count 7, 356356057337280⟩, ⟨.path 6, 1042468362936000⟩, ⟨.privateRow 2 28, 677025600932640960⟩, ⟨.privateRow 3 24, 49978937041553520⟩, ⟨.privateRow 3 25, 156236677138301760⟩, ⟨.privateRow 3 26, 220915301545018080⟩, ⟨.privateRow 4 21, 13229718628646520⟩, ⟨.privateRow 4 22, 39983149633242816⟩, ⟨.privateRow 4 23, 64678624406716320⟩, ⟨.privateRow 4 24, 85958171830571040⟩, ⟨.privateRow 4 25, 116967512319938280⟩, ⟨.privateRow 5 18, 2233588859381880⟩, ⟨.privateRow 5 19, 9381618652348800⟩, ⟨.privateRow 5 20, 17614170834099840⟩, ⟨.privateRow 5 21, 25718725738113408⟩, ⟨.privateRow 5 22, 33561104399943120⟩, ⟨.privateRow 5 23, 46682643511183680⟩, ⟨.privateRow 5 24, 33446561381513280⟩, ⟨.privateRow 6 15, 206177433173712⟩, ⟨.privateRow 6 16, 1815718958813760⟩, ⟨.privateRow 6 17, 4705809007159260⟩, ⟨.privateRow 6 18, 7788925253229120⟩, ⟨.privateRow 6 19, 11136126791790000⟩, ⟨.privateRow 6 20, 14157517077928224⟩, ⟨.privateRow 6 21, 19586856151502640⟩, ⟨.privateRow 6 22, 3385382544704160⟩, ⟨.privateRow 7 13, 194376031274880⟩, ⟨.privateRow 7 14, 1114885379383776⟩, ⟨.privateRow 7 15, 2403989275688000⟩, ⟨.privateRow 7 16, 3862645121495160⟩, ⟨.privateRow 7 17, 5418066586046400⟩, ⟨.privateRow 7 18, 6855611769726720⟩, ⟨.privateRow 7 19, 2575945214466624⟩, ⟨.privateRow 8 11, 141057606029340⟩, ⟨.privateRow 8 12, 688415110765200⟩, ⟨.privateRow 8 13, 1398697525048824⟩, ⟨.privateRow 8 14, 2232174748043240⟩, ⟨.privateRow 8 15, 3123683565097095⟩, ⟨.privateRow 8 16, 12727002047760⟩, ⟨.privateRow 9 9, 105732017012160⟩, ⟨.privateRow 9 10, 470899075767120⟩, ⟨.privateRow 9 11, 971880156374400⟩, ⟨.privateRow 9 12, 967252155629760⟩, ⟨.privateRow 10 7, 87270871184640⟩, ⟨.privateRow 10 8, 381810061432800⟩, ⟨.privateRow 10 9, 318175051194000⟩, ⟨.privateRow 11 5, 81452813105664⟩, ⟨.privateRow 11 6, 141815165675040⟩, ⟨.privateRow 12 3, 52498883447010⟩, ⟨.hall 4 25, 1098438176737440⟩, ⟨.hall 3 26, 49465614625627200⟩, ⟨.hall 2 27, 170816367055585680⟩, ⟨.assumptionRow 15, 6839523512640⟩]
  caps := #[0, 20426795939571840, 917966478789360, 600998354227440, 797880503023968, 228859888352832, 0, 410514685098960, 172994703295680, 98132189702400, 20933776150560, 232176161580480, 379267374810870, 2680925639595840, 565536208910400, 83100927087360] }

theorem case_45_30_15_checked :
    (Witness.linear .conditional case_45_30_15).check 45 30 15 = true := by
  change case_45_30_15.check 45 30 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_30_16 : Certificate := {
  objectiveScale := 3823419600000
  eta := 52679899773824843520
  rows := #[⟨.count 2, 6160935724844060160⟩, ⟨.count 3, 668134582623668160⟩, ⟨.count 4, 63738989363649600⟩, ⟨.count 5, 5794453578513600⟩, ⟨.count 6, 204510126300480⟩, ⟨.count 8, 159063431567040⟩, ⟨.path 5, 3496284687495600⟩, ⟨.privateRow 2 28, 477667484995821120⟩, ⟨.privateRow 3 24, 35618846997333600⟩, ⟨.privateRow 3 25, 102232339802873280⟩, ⟨.privateRow 3 26, 152973574472759040⟩, ⟨.privateRow 4 21, 8154841286231640⟩, ⟨.privateRow 4 22, 24370790050807200⟩, ⟨.privateRow 4 23, 41477209990316100⟩, ⟨.privateRow 4 24, 59677191021848400⟩, ⟨.privateRow 4 25, 87734844182905920⟩, ⟨.privateRow 5 18, 1073678163077520⟩, ⟨.privateRow 5 19, 5064060270297600⟩, ⟨.privateRow 5 20, 10270953009757440⟩, ⟨.privateRow 5 21, 16360810104038400⟩, ⟨.privateRow 5 22, 23399366950879920⟩, ⟨.privateRow 5 23, 36084675618351360⟩, ⟨.privateRow 5 24, 31255964302923360⟩, ⟨.privateRow 6 12, 31463096353920⟩, ⟨.privateRow 6 16, 768806585907360⟩, ⟨.privateRow 6 17, 2407254611661900⟩, ⟨.privateRow 6 18, 4421314159067520⟩, ⟨.privateRow 6 19, 6993110152108080⟩, ⟨.privateRow 6 20, 9891473108733216⟩, ⟨.privateRow 6 21, 15397908259373640⟩, ⟨.privateRow 6 22, 12690989504313120⟩, ⟨.privateRow 7 11, 12235648582080⟩, ⟨.privateRow 7 14, 443105273651040⟩, ⟨.privateRow 7 15, 1171514797573120⟩, ⟨.privateRow 7 16, 2124632978788320⟩, ⟨.privateRow 7 17, 3327347292984000⟩, ⟨.privateRow 7 18, 3628161129552960⟩, ⟨.privateRow 7 19, 9530171885602368⟩, ⟨.privateRow 8 12, 251247920316120⟩, ⟨.privateRow 8 13, 642218604951924⟩, ⟨.privateRow 8 14, 1175302022134240⟩, ⟨.privateRow 8 15, 1841656293612135⟩, ⟨.privateRow 8 16, 2610344528751960⟩, ⟨.privateRow 8 17, 1047167591149680⟩, ⟨.privateRow 9 10, 145808145603120⟩, ⟨.privateRow 9 11, 415217529155520⟩, ⟨.privateRow 9 12, 645343065214848⟩, ⟨.privateRow 9 13, 1489641660707200⟩, ⟨.privateRow 10 8, 97011213757920⟩, ⟨.privateRow 10 9, 315286444713240⟩, ⟨.privateRow 10 10, 523669868860320⟩, ⟨.privateRow 11 6, 77908619543040⟩, ⟨.privateRow 11 7, 230729373262080⟩, ⟨.privateRow 12 4, 74987046310176⟩, ⟨.privateRow 12 5, 13390543983960⟩, ⟨.privateRow 13 2, 46866903943860⟩, ⟨.hall 4 25, 6345057764707200⟩, ⟨.hall 3 26, 42492659575766400⟩, ⟨.hall 2 27, 126031799977031520⟩, ⟨.assumptionRow 16, 2967355951560⟩]
  caps := #[0, 590576799692880, 3875744242450080, 2860346095841520, 818147736873720, 321258734002800, 0, 7679779430400, 63009418474093, 219004368599744, 20100708405360, 2967355951560, 1875133558903176, 0, 1373699605037760, 302564780678160] }

theorem case_45_30_16_checked :
    (Witness.linear .conditional case_45_30_16).check 45 30 16 = true := by
  change case_45_30_16.check 45 30 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_30_17 : Certificate := {
  objectiveScale := 9088268389200000
  eta := 148252838459607293892480
  rows := #[⟨.count 2, 17656871351394304149120⟩, ⟨.count 3, 1946426763145828803840⟩, ⟨.count 4, 186265198487856327840⟩, ⟨.count 5, 13368315680946626400⟩, ⟨.count 6, 486120570216240960⟩, ⟨.path 5, 8515127990074305600⟩, ⟨.path 6, 324693910523062080⟩, ⟨.privateRow 2 28, 1454027135564294731440⟩, ⟨.privateRow 3 24, 88899299278295065560⟩, ⟨.privateRow 3 25, 298261976526009175680⟩, ⟨.privateRow 3 26, 464771775174244377840⟩, ⟨.privateRow 4 21, 20423815623668457000⟩, ⟨.privateRow 4 22, 65727552097987579800⟩, ⟨.privateRow 4 23, 120259139813182359990⟩, ⟨.privateRow 4 24, 181066409056377084240⟩, ⟨.privateRow 4 25, 279174992470435381320⟩, ⟨.privateRow 5 18, 2947105956935960820⟩, ⟨.privateRow 5 19, 12882195110730385440⟩, ⟨.privateRow 5 20, 27668362454807714640⟩, ⟨.privateRow 5 21, 46489330531679843808⟩, ⟨.privateRow 5 22, 70406462586318899040⟩, ⟨.privateRow 5 23, 115696695711465348480⟩, ⟨.privateRow 5 24, 110754469914266898720⟩, ⟨.privateRow 6 14, 3682731592547280⟩, ⟨.privateRow 6 15, 247111289859922488⟩, ⟨.privateRow 6 16, 2002996793946548400⟩, ⟨.privateRow 6 17, 6030933324245239410⟩, ⟨.privateRow 6 18, 11632170787317194400⟩, ⟨.privateRow 6 19, 19411064435717955000⟩, ⟨.privateRow 6 20, 29215846269996081696⟩, ⟨.privateRow 6 21, 40398644887345524780⟩, ⟨.privateRow 6 22, 71473227170960094480⟩, ⟨.privateRow 7 13, 191502042812458560⟩, ⟨.privateRow 7 14, 1112675971828284864⟩, ⟨.privateRow 7 15, 2874713001649128640⟩, ⟨.privateRow 7 16, 5418218855535185700⟩, ⟨.privateRow 7 17, 8970081950418732000⟩, ⟨.privateRow 7 18, 11995475181724834800⟩, ⟨.privateRow 7 19, 26023654525576099392⟩, ⟨.privateRow 7 20, 16467334316075162520⟩, ⟨.privateRow 8 11, 124062020523936495⟩, ⟨.privateRow 8 12, 635884988313163680⟩, ⟨.privateRow 8 13, 1545458312812466052⟩, ⟨.privateRow 8 14, 2903970258189920920⟩, ⟨.privateRow 8 15, 4791157078329166545⟩, ⟨.privateRow 8 16, 7231043481966584280⟩, ⟨.privateRow 8 17, 11212843569258641310⟩, ⟨.privateRow 9 9, 85174971704555040⟩, ⟨.privateRow 9 10, 411852149766537480⟩, ⟨.privateRow 9 11, 989427221197702560⟩, ⟨.privateRow 9 12, 1863462185828923680⟩, ⟨.privateRow 9 13, 3081764355630120160⟩, ⟨.privateRow 9 14, 4331199247134980220⟩, ⟨.privateRow 10 7, 69445795745177280⟩, ⟨.privateRow 10 8, 317848065141388320⟩, ⟨.privateRow 10 9, 783194252015054880⟩, ⟨.privateRow 10 10, 1495189026574195680⟩, ⟨.privateRow 10 11, 1296321520576642560⟩, ⟨.privateRow 11 5, 70217415697901472⟩, ⟨.privateRow 11 6, 306718931207866320⟩, ⟨.privateRow 11 7, 791504005352084640⟩, ⟨.privateRow 11 8, 229556935935447120⟩, ⟨.privateRow 12 3, 83551973005916415⟩, ⟨.privateRow 12 4, 386195786338458096⟩, ⟨.privateRow 13 1, 157274302128783840⟩, ⟨.hall 4 25, 31261292053905957120⟩, ⟨.hall 3 26, 145863177763217634720⟩, ⟨.hall 2 27, 398057514061710737520⟩, ⟨.assumptionRow 17, 3324942990188820⟩]
  caps := #[0, 29808023911007362020, 6461511527439848880, 152395811157549960, 0, 623226625486296, 109290647394686550, 68719228424045472, 17511275532310560, 4986248490410220, 7183042753809780, 0, 163539231780865941, 0, 9988243254708919200, 2881649067103006200] }

theorem case_45_30_17_checked :
    (Witness.linear .conditional case_45_30_17).check 45 30 17 = true := by
  change case_45_30_17.check 45 30 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_30_18 : Certificate := {
  objectiveScale := 10871922600000
  eta := 189376072325392352400
  rows := #[⟨.count 2, 26070945519785166000⟩, ⟨.count 3, 3420827245407171600⟩, ⟨.count 4, 411591246224558400⟩, ⟨.count 5, 41999106757608000⟩, ⟨.count 6, 2863575460746000⟩, ⟨.path 6, 2850885938300400⟩, ⟨.privateRow 4 21, 6299866013641200⟩, ⟨.privateRow 4 22, 73183443525131940⟩, ⟨.privateRow 4 23, 146865626443010475⟩, ⟨.privateRow 5 19, 12845181352489200⟩, ⟨.privateRow 5 20, 34840168105743000⟩, ⟨.privateRow 5 21, 64831348431289440⟩, ⟨.privateRow 5 22, 101656928856483000⟩, ⟨.privateRow 6 15, 95452515358200⟩, ⟨.privateRow 6 17, 8566863253398450⟩, ⟨.privateRow 6 18, 13826978653316400⟩, ⟨.privateRow 6 21, 223836148514979000⟩, ⟨.privateRow 6 23, 12647458284961500⟩, ⟨.privateRow 7 12, 10605835039800⟩, ⟨.privateRow 7 13, 92560014892800⟩, ⟨.privateRow 8 11, 9280105659825⟩, ⟨.privateRow 8 12, 146794398619050⟩, ⟨.privateRow 8 14, 556806339589500⟩, ⟨.privateRow 8 19, 54567021279771000⟩, ⟨.privateRow 8 21, 9131623969267800⟩, ⟨.privateRow 9 9, 4895000787600⟩, ⟨.privateRow 9 11, 248755040024400⟩, ⟨.privateRow 9 12, 133633521501480⟩, ⟨.privateRow 9 17, 1603602258017760⟩, ⟨.privateRow 10 9, 23863128839550⟩, ⟨.hall 10 6, 1221476976720⟩, ⟨.hall 12 6, 452479064400⟩, ⟨.hall 9 7, 59103724680⟩, ⟨.hall 11 7, 448013810475⟩, ⟨.hall 9 8, 511763203380⟩, ⟨.hall 7 9, 63503409060⟩, ⟨.hall 8 9, 458501621760⟩, ⟨.hall 7 10, 110819483775⟩, ⟨.hall 6 12, 355855440600⟩, ⟨.hall 5 16, 268030329840⟩, ⟨.hall 4 19, 3905663361336⟩, ⟨.hall 3 22, 92660236648056⟩, ⟨.hall 2 26, 85942616605846000⟩]
  caps := #[0, 16811023588959600, 0, 4118633481362400, 381089820566268, 0, 0, 173550027924000, 3120839542275, 534708216468720, 100146091423950, 0, 0, 0, 27701658784800000, 9893449566000000] }

theorem case_45_30_18_checked :
    (Witness.linear .negative case_45_30_18).check 45 30 18 = true := by
  change case_45_30_18.check 45 30 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_30_19 : Certificate := {
  objectiveScale := 284008387162500
  eta := 5129645532040569660120
  rows := #[⟨.count 2, 642050494787686584600⟩, ⟨.count 3, 73971346767904666080⟩, ⟨.count 4, 7352573624520644520⟩, ⟨.count 5, 573892339838617800⟩, ⟨.count 6, 20255023759010040⟩, ⟨.path 5, 227511070356269700⟩, ⟨.path 6, 22777315316715960⟩, ⟨.hall 12 6, 8001338122140⟩, ⟨.hall 13 9, 19857866430402⟩, ⟨.hall 10 10, 7966534563540⟩, ⟨.hall 11 10, 9044574791175⟩, ⟨.hall 8 11, 4811011917140⟩, ⟨.hall 9 11, 7216517875710⟩, ⟨.hall 7 12, 1366153164915⟩, ⟨.hall 12 12, 16002676244280⟩]
  caps := #[0, 1742406467492871180, 393618216861029160, 20310904942047720, 39445249925521440, 0, 2522291557705920, 0, 0, 0, 8666745845815200, 17025962000327280, 24004014366420, 399358204269624600, 0, 465205738172175000] }

theorem case_45_30_19_checked :
    (Witness.linear .negative case_45_30_19).check 45 30 19 = true := by
  change case_45_30_19.check 45 30 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_31_1_checked :
    (Witness.rising).check 45 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_31_2_checked :
    (Witness.rising).check 45 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_31_3_checked :
    (Witness.rising).check 45 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_31_4_checked :
    (Witness.rising).check 45 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_31_5_checked :
    (Witness.rising).check 45 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_31_6_checked :
    (Witness.rising).check 45 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_31_7_checked :
    (Witness.rising).check 45 31 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_31_8_checked :
    (Witness.rising).check 45 31 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_31_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_45_31_9_checked :
    (Witness.linear .positive case_45_31_9).check 45 31 9 = true := by
  change case_45_31_9.check 45 31 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_31_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_45_31_10_checked :
    (Witness.linear .positive case_45_31_10).check 45 31 10 = true := by
  change case_45_31_10.check 45 31 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_45_31_11_checked :
    (Witness.linear .positive case_45_31_11).check 45 31 11 = true := by
  change case_45_31_11.check 45 31 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_45_31_12_checked :
    (Witness.linear .positive case_45_31_12).check 45 31 12 = true := by
  change case_45_31_12.check 45 31 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_31_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_45_31_13_checked :
    (Witness.linear .positive case_45_31_13).check 45 31 13 = true := by
  change case_45_31_13.check 45 31 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_31_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_45_31_14_checked :
    (Witness.linear .positive case_45_31_14).check 45 31 14 = true := by
  change case_45_31_14.check 45 31 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_31_15 : Certificate := {
  objectiveScale := 583
  eta := 238262888
  rows := #[⟨.assumptionRow 15, 1158⟩]
  caps := #[0, 0, 69233758, 20378070, 6088992, 1852136, 575575, 183601, 60495, 20764, 3138933, 1923807, 770697, 230199, 50849] }

theorem case_45_31_15_checked :
    (Witness.linear .conditional case_45_31_15).check 45 31 15 = true := by
  change case_45_31_15.check 45 31 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_31_16 : Certificate := {
  objectiveScale := 41925420860400000
  eta := 911364078920217087765600
  rows := #[⟨.count 2, 101549706770506058064000⟩, ⟨.count 3, 10956678888396706264800⟩, ⟨.count 4, 1036552030831321804800⟩, ⟨.count 5, 80980627408697016000⟩, ⟨.path 5, 54191495155520923200⟩, ⟨.privateRow 2 28, 2360585288963518016400⟩, ⟨.privateRow 2 29, 9175105085405371912800⟩, ⟨.privateRow 3 25, 1239678437914803486600⟩, ⟨.privateRow 3 26, 2306148311649893911200⟩, ⟨.privateRow 3 27, 2909903878219179441600⟩, ⟨.privateRow 4 21, 49166809498137474000⟩, ⟨.privateRow 4 22, 219322532565221085000⟩, ⟨.privateRow 4 23, 636507731432358545760⟩, ⟨.privateRow 4 24, 883701096597406187100⟩, ⟨.privateRow 4 25, 1158022971944367328800⟩, ⟨.privateRow 4 26, 1532558373709591027800⟩, ⟨.privateRow 5 18, 12237072586203104640⟩, ⟨.privateRow 5 19, 42514829389565933400⟩, ⟨.privateRow 5 20, 136047454046610986880⟩, ⟨.privateRow 5 21, 258058266009047824320⟩, ⟨.privateRow 5 22, 363117133300597419744⟩, ⟨.privateRow 5 23, 366032435887310512320⟩, ⟨.privateRow 5 24, 849216846092536041120⟩, ⟨.privateRow 5 25, 183826024217742226320⟩, ⟨.privateRow 6 13, 553713691683398400⟩, ⟨.privateRow 6 15, 490791681264830400⟩, ⟨.privateRow 6 16, 7738148841275492640⟩, ⟨.privateRow 6 17, 29193016300419171200⟩, ⟨.privateRow 6 18, 68046221642030131500⟩, ⟨.privateRow 6 19, 114529744478014351200⟩, ⟨.privateRow 6 20, 164660609064350599200⟩, ⟨.privateRow 6 21, 210369674312815137120⟩, ⟨.privateRow 6 22, 249465321656236085400⟩, ⟨.privateRow 7 7, 37491031207730100⟩, ⟨.privateRow 7 13, 281182734057975750⟩, ⟨.privateRow 7 14, 5889500175177964800⟩, ⟨.privateRow 7 15, 17883221886087257700⟩, ⟨.privateRow 7 16, 36666228521160037800⟩, ⟨.privateRow 7 17, 59554503073479263850⟩, ⟨.privateRow 7 18, 85318875305591499000⟩, ⟨.privateRow 7 19, 107299331316523546200⟩, ⟨.privateRow 8 11, 103821317190637200⟩, ⟨.privateRow 8 12, 4498923744927612000⟩, ⟨.privateRow 8 13, 12147094111304552400⟩, ⟨.privateRow 8 14, 23416898092348220460⟩, ⟨.privateRow 8 15, 37491031207730100000⟩, ⟨.privateRow 8 16, 35682088951957122675⟩, ⟨.privateRow 9 10, 3875995841783788800⟩, ⟨.privateRow 9 11, 9972614301256206600⟩, ⟨.privateRow 9 12, 18731882501607693600⟩, ⟨.privateRow 9 13, 6928342567188522480⟩, ⟨.privateRow 10 8, 3817658149267145040⟩, ⟨.privateRow 10 9, 9343918547157348000⟩, ⟨.privateRow 11 6, 4318966795130507520⟩, ⟨.privateRow 12 4, 927903022391319975⟩, ⟨.hall 3 27, 437439996270193702500⟩, ⟨.hall 2 28, 1910584319759672356800⟩, ⟨.assumptionRow 16, 35901576391177728⟩]
  caps := #[0, 0, 0, 31198559986591572960, 7719346186123071060, 14816914539914462976, 1180973515645721952, 5640050359302867576, 1099571097328714332, 424553581800754560, 10855582719569097840, 35901576391177728, 52689532887838229229, 70277899263386766336, 18535141357507450368] }

theorem case_45_31_16_checked :
    (Witness.linear .conditional case_45_31_16).check 45 31 16 = true := by
  change case_45_31_16.check 45 31 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_31_17 : Certificate := {
  objectiveScale := 72670729491360000
  eta := 1662920987712111484156800
  rows := #[⟨.count 2, 185639990271697039478400⟩, ⟨.count 3, 19775469213203811307200⟩, ⟨.count 4, 1781573802991334352000⟩, ⟨.count 5, 105274815631306120800⟩, ⟨.path 5, 100269653400819302400⟩, ⟨.privateRow 2 28, 6369126345694020308400⟩, ⟨.privateRow 2 29, 19686390523054244589600⟩, ⟨.privateRow 3 25, 2393989797769605535500⟩, ⟨.privateRow 3 26, 4820146900315443496800⟩, ⟨.privateRow 3 27, 6220661862111409112400⟩, ⟨.privateRow 4 21, 79823761302858487200⟩, ⟨.privateRow 4 22, 390056688685223960400⟩, ⟨.privateRow 4 23, 1213899604856368269840⟩, ⟨.privateRow 4 24, 1802831217686117318700⟩, ⟨.privateRow 4 25, 2505000741175694361600⟩, ⟨.privateRow 4 26, 3520632776593102770600⟩, ⟨.privateRow 5 18, 21414877025855433120⟩, ⟨.privateRow 5 19, 68023727023305493440⟩, ⟨.privateRow 5 20, 237851671360401521280⟩, ⟨.privateRow 5 21, 485613829027486439280⟩, ⟨.privateRow 5 22, 728825646678273144000⟩, ⟨.privateRow 5 23, 1005779392416016938720⟩, ⟨.privateRow 5 24, 1522975666132895214240⟩, ⟨.privateRow 5 25, 1091618857469235775680⟩, ⟨.privateRow 6 15, 2944750087588982400⟩, ⟨.privateRow 6 16, 12147094111304552400⟩, ⟨.privateRow 6 17, 45489117865379188000⟩, ⟨.privateRow 6 18, 116297178806378770200⟩, ⟨.privateRow 6 19, 210678171941038744800⟩, ⟨.privateRow 6 20, 324522366134111745600⟩, ⟨.privateRow 6 21, 234483905585627137440⟩, ⟨.privateRow 6 22, 1115958034929294156600⟩, ⟨.privateRow 6 23, 26393685970241990400⟩, ⟨.privateRow 7 12, 155731975785955800⟩, ⟨.privateRow 7 13, 1630859857536259350⟩, ⟨.privateRow 7 14, 8834250262766947200⟩, ⟨.privateRow 7 15, 27195994038087414540⟩, ⟨.privateRow 7 16, 60885434681353682400⟩, ⟨.privateRow 7 17, 106287073473914833500⟩, ⟨.privateRow 7 18, 163696553976151825200⟩, ⟨.privateRow 7 19, 228995218616815450800⟩, ⟨.privateRow 7 20, 224451305634438562680⟩, ⟨.privateRow 8 10, 48202754409938700⟩, ⟨.privateRow 8 11, 1349677123478283600⟩, ⟨.privateRow 8 12, 6579675976956632550⟩, ⟨.privateRow 8 13, 18097943246640621000⟩, ⟨.privateRow 8 14, 37521024032696284080⟩, ⟨.privateRow 8 15, 64559555739711232200⟩, ⟨.privateRow 8 16, 98948204115001666425⟩, ⟨.privateRow 8 17, 84644036743852357200⟩, ⟨.privateRow 9 9, 1285406784265032000⟩, ⟨.privateRow 9 10, 5744779551215258400⟩, ⟨.privateRow 9 11, 14621502171014739000⟩, ⟨.privateRow 9 12, 28956709194624993600⟩, ⟨.privateRow 9 13, 49308204244406627520⟩, ⟨.privateRow 9 14, 14796460316650812800⟩, ⟨.privateRow 10 7, 1511638378295677632⟩, ⟨.privateRow 10 8, 6247076971528055520⟩, ⟨.privateRow 10 9, 15199440836709286080⟩, ⟨.privateRow 10 10, 18085673454609000240⟩, ⟨.privateRow 11 5, 2277580145869603575⟩, ⟨.privateRow 11 6, 8907869014956671760⟩, ⟨.privateRow 11 7, 2892165264596322000⟩, ⟨.privateRow 12 3, 4366602458312094000⟩, ⟨.hall 3 27, 1170748499108591145600⟩, ⟨.hall 2 28, 4300350558944600160000⟩, ⟨.assumptionRow 17, 37087227293109840⟩]
  caps := #[0, 1107932052449980573200, 0, 9065746260166622400, 0, 3309459284267136000, 11359720033312836800, 152426156351113260, 37087227293109840, 864765545340284320, 1661166869166267408, 1643842895959270710, 0, 317046639992672399040, 103364788487860247040] }

theorem case_45_31_17_checked :
    (Witness.linear .conditional case_45_31_17).check 45 31 17 = true := by
  change case_45_31_17.check 45 31 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_31_18 : Certificate := {
  objectiveScale := 125114772607624800000
  eta := 3765756374098337006647459200
  rows := #[⟨.count 2, 435430533726745448036745600⟩, ⟨.count 3, 48217582348439267703139200⟩, ⟨.count 4, 4584183748602484160534400⟩, ⟨.count 5, 317881354830099266606400⟩, ⟨.count 6, 11153731748424535670400⟩, ⟨.path 5, 188660933932691546726400⟩, ⟨.path 6, 9631295953141031769600⟩, ⟨.privateRow 2 28, 23372644878823614497323200⟩, ⟨.privateRow 3 26, 26010502437326017183372800⟩, ⟨.privateRow 4 21, 161330762789712033804000⟩, ⟨.privateRow 4 23, 3896556186312111536454240⟩, ⟨.privateRow 4 24, 5079827703173099464387800⟩, ⟨.privateRow 4 25, 8175685371595184646403200⟩, ⟨.privateRow 5 18, 48704628634787139094080⟩, ⟨.privateRow 5 19, 156431087771654112777360⟩, ⟨.privateRow 5 20, 290156364484015420797120⟩, ⟨.privateRow 5 21, 1384735796566906103480160⟩, ⟨.privateRow 5 23, 6936505774345218733421760⟩, ⟨.privateRow 5 24, 2997007720801672734636480⟩, ⟨.privateRow 5 25, 2429282774806863869013120⟩, ⟨.privateRow 6 15, 9294776457020446392000⟩, ⟨.privateRow 6 16, 28999702545903792743040⟩, ⟨.privateRow 6 17, 104927698670364150380800⟩, ⟨.privateRow 6 18, 182642357380451771602800⟩, ⟨.privateRow 6 19, 524225392175953176508800⟩, ⟨.privateRow 6 21, 1899480516756698424669120⟩, ⟨.privateRow 6 23, 6313012169608287189446400⟩, ⟨.privateRow 7 12, 428989682631712910400⟩, ⟨.privateRow 7 13, 1161847057127555799000⟩, ⟨.privateRow 7 14, 4055902453972558425600⟩, ⟨.privateRow 7 15, 111676739131100663399880⟩, ⟨.privateRow 7 17, 378181217095019412574500⟩, ⟨.privateRow 7 21, 2805860642963047254585000⟩, ⟨.privateRow 8 10, 99586890610933354200⟩, ⟨.privateRow 8 11, 536237103289641138000⟩, ⟨.privateRow 8 12, 1858955291404089278400⟩, ⟨.privateRow 8 14, 2370167996540213829960⟩, ⟨.privateRow 9 8, 123930352760272618560⟩, ⟨.privateRow 9 9, 398347562443733416800⟩, ⟨.privateRow 9 10, 714982804386188184000⟩, ⟨.privateRow 9 11, 1084390586652385412400⟩, ⟨.privateRow 9 12, 1013975613493139606400⟩, ⟨.privateRow 9 13, 4647388228510223196000⟩, ⟨.privateRow 9 14, 9914428220821809484800⟩, ⟨.hall 9 6, 28746500143702011840⟩, ⟨.hall 11 7, 5539456557202588020⟩, ⟨.hall 12 7, 3652388938814893200⟩, ⟨.hall 8 8, 9717247339192192800⟩, ⟨.hall 10 8, 5261969865097820160⟩, ⟨.hall 7 9, 3965640676088834925⟩, ⟨.hall 7 10, 3204644289290753400⟩, ⟨.hall 6 12, 977503844844428616⟩, ⟨.hall 4 24, 6242276537494346971776⟩, ⟨.hall 3 25, 35906606670275414931000⟩, ⟨.hall 2 27, 799153890876343670896800⟩]
  caps := #[0, 0, 54245375871356811398400, 22782676979193167836800, 10776175346831085595008, 10169382147163450273920, 0, 27759484732621844475, 15000339236022228100320, 143732500718510059200, 0, 58712966812358968824000, 0, 0, 476437054089835238400000] }

theorem case_45_31_18_checked :
    (Witness.linear .negative case_45_31_18).check 45 31 18 = true := by
  change case_45_31_18.check 45 31 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_31_19 : Certificate := {
  objectiveScale := 147497521494400000
  eta := 3244966715912338187971200
  rows := #[⟨.count 2, 382175567150040699235200⟩, ⟨.count 3, 41249576897190739677600⟩, ⟨.count 4, 3717910582808178556800⟩, ⟨.count 5, 224356673100493533600⟩, ⟨.path 5, 193997185275615321600⟩, ⟨.path 6, 1923677739210427200⟩, ⟨.hall 12 6, 12994268255225400⟩, ⟨.hall 11 7, 3789994907774075⟩, ⟨.hall 10 8, 551271986585320⟩, ⟨.hall 9 11, 4952360978390100⟩, ⟨.hall 6 13, 2633778957027504⟩, ⟨.hall 7 13, 4376363402822125⟩, ⟨.hall 8 13, 5836448192250000⟩, ⟨.hall 10 13, 10237908322298800⟩, ⟨.hall 11 13, 5305992870883705⟩]
  caps := #[0, 0, 0, 0, 0, 0, 1923677739210427200, 0, 8903042583352918000, 10064309007268516000, 2205087946341280, 11369984723322225, 401983985302623403680, 0, 912714663007347200000] }

theorem case_45_31_19_checked :
    (Witness.linear .negative case_45_31_19).check 45 31 19 = true := by
  change case_45_31_19.check 45 31 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_31_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16796, 16796, 11934, 7072] }

theorem case_45_31_20_checked :
    (Witness.linear .negative case_45_31_20).check 45 31 20 = true := by
  change case_45_31_20.check 45 31 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_32_1_checked :
    (Witness.rising).check 45 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_32_2_checked :
    (Witness.rising).check 45 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_32_3_checked :
    (Witness.rising).check 45 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_32_4_checked :
    (Witness.rising).check 45 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_32_5_checked :
    (Witness.rising).check 45 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_32_6_checked :
    (Witness.rising).check 45 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_32_7_checked :
    (Witness.rising).check 45 32 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_32_8_checked :
    (Witness.rising).check 45 32 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_32_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_45_32_9_checked :
    (Witness.linear .positive case_45_32_9).check 45 32 9 = true := by
  change case_45_32_9.check 45 32 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_32_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_45_32_10_checked :
    (Witness.linear .positive case_45_32_10).check 45 32 10 = true := by
  change case_45_32_10.check 45 32 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_45_32_11_checked :
    (Witness.linear .positive case_45_32_11).check 45 32 11 = true := by
  change case_45_32_11.check 45 32 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_45_32_12_checked :
    (Witness.linear .positive case_45_32_12).check 45 32 12 = true := by
  change case_45_32_12.check 45 32 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_32_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_45_32_13_checked :
    (Witness.linear .positive case_45_32_13).check 45 32 13 = true := by
  change case_45_32_13.check 45 32 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_32_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_45_32_14_checked :
    (Witness.linear .positive case_45_32_14).check 45 32 14 = true := by
  change case_45_32_14.check 45 32 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_32_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_45_32_15_checked :
    (Witness.linear .positive case_45_32_15).check 45 32 15 = true := by
  change case_45_32_15.check 45 32 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_32_16 : Certificate := {
  objectiveScale := 5
  eta := 3380195
  rows := #[⟨.assumptionRow 16, 8⟩]
  caps := #[0, 0, 1010344, 305558, 93670, 29172, 9256, 3003, 1001, 72105, 93423, 54663, 23655, 8151] }

theorem case_45_32_16_checked :
    (Witness.linear .conditional case_45_32_16).check 45 32 16 = true := by
  change case_45_32_16.check 45 32 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_32_17 : Certificate := {
  objectiveScale := 1234986552800000
  eta := 51762017751999329174400
  rows := #[⟨.count 2, 4654112777448665731200⟩, ⟨.count 3, 358199226963528350400⟩, ⟨.count 4, 18430167694389010560⟩, ⟨.count 5, 330289743627043200⟩, ⟨.path 4, 17535998535612036480⟩, ⟨.privateRow 2 29, 404646222161081300400⟩, ⟨.privateRow 2 30, 574951871218775450400⟩, ⟨.privateRow 3 25, 42012855389359895040⟩, ⟨.privateRow 3 26, 81870570201553333200⟩, ⟨.privateRow 3 27, 170099217967927248000⟩, ⟨.privateRow 3 28, 184053959636169823200⟩, ⟨.privateRow 3 29, 237808615411471104000⟩, ⟨.privateRow 4 21, 2117982981008414520⟩, ⟨.privateRow 4 22, 10892483902328988960⟩, ⟨.privateRow 4 23, 18132906925124671680⟩, ⟨.privateRow 4 24, 42062398850903951520⟩, ⟨.privateRow 4 25, 58597529141232801720⟩, ⟨.privateRow 4 26, 73720670777556042240⟩, ⟨.privateRow 4 27, 91630632125732459760⟩, ⟨.privateRow 5 18, 713425846234413312⟩, ⟨.privateRow 5 19, 2253310028744494720⟩, ⟨.privateRow 5 20, 4450654295374407120⟩, ⟨.privateRow 5 21, 10380534799707072000⟩, ⟨.privateRow 5 22, 17406269489145176640⟩, ⟨.privateRow 5 23, 24243267182224970880⟩, ⟨.privateRow 5 24, 30667402695770961120⟩, ⟨.privateRow 5 25, 38996209064232900480⟩, ⟨.privateRow 6 15, 161704353650739900⟩, ⟨.privateRow 6 16, 521707663229079600⟩, ⟨.privateRow 6 17, 1077570288583228440⟩, ⟨.privateRow 6 18, 2853336396333623200⟩, ⟨.privateRow 6 19, 5274314343544346100⟩, ⟨.privateRow 6 20, 8245447528403685600⟩, ⟨.privateRow 6 21, 11580784135923202200⟩, ⟨.privateRow 6 22, 14697893591403422400⟩, ⟨.privateRow 6 23, 6512900882145758100⟩, ⟨.privateRow 7 12, 40443642076780800⟩, ⟨.privateRow 7 13, 141552747268732800⟩, ⟨.privateRow 7 14, 312595650218451600⟩, ⟨.privateRow 7 15, 836448052042512000⟩, ⟨.privateRow 7 16, 1826030439766653120⟩, ⟨.privateRow 7 17, 3118092460669586400⟩, ⟨.privateRow 7 18, 4719899416741809300⟩, ⟨.privateRow 7 19, 6577147292736477600⟩, ⟨.privateRow 7 20, 1521692033138877600⟩, ⟨.privateRow 8 9, 12901943110431375⟩, ⟨.privateRow 8 10, 46791047013831120⟩, ⟨.privateRow 8 11, 115011607155845400⟩, ⟨.privateRow 8 12, 314410429029589200⟩, ⟨.privateRow 8 13, 715627777858593600⟩, ⟨.privateRow 8 14, 1422497873121015600⟩, ⟨.privateRow 8 15, 2320285448979978480⟩, ⟨.privateRow 8 16, 2064310897669020000⟩, ⟨.privateRow 9 6, 3669886040300480⟩, ⟨.privateRow 9 7, 23314570138379520⟩, ⟨.privateRow 9 8, 57800705134732560⟩, ⟨.privateRow 9 9, 158539076940980736⟩, ⟨.privateRow 9 10, 377473992716620800⟩, ⟨.privateRow 9 11, 782532623362533120⟩, ⟨.privateRow 9 12, 1084451324908791840⟩, ⟨.privateRow 10 4, 15645303645491520⟩, ⟨.privateRow 10 5, 41286217953380400⟩, ⟨.privateRow 10 6, 43714819009461600⟩, ⟨.privateRow 10 7, 418022956777976550⟩, ⟨.privateRow 10 8, 326986846190772768⟩, ⟨.privateRow 11 3, 182528542530734400⟩, ⟨.privateRow 11 4, 82572435906760800⟩, ⟨.privateRow 12 0, 129756684996338400⟩, ⟨.hall 3 28, 9379089788857588800⟩, ⟨.assumptionRow 17, 763639685079040⟩]
  caps := #[0, 6980463728055417600, 981984757499166960, 866640330034617600, 0, 8054684945594560, 140048451448642100, 2162145121938010, 19246644284829885, 29455144626490968, 0, 4293068994748195200, 0, 7353715192780830720] }

theorem case_45_32_17_checked :
    (Witness.linear .conditional case_45_32_17).check 45 32 17 = true := by
  change case_45_32_17.check 45 32 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_32_18 : Certificate := {
  objectiveScale := 6154948800000
  eta := 349196298952973472000
  rows := #[⟨.count 2, 23498547937060996800⟩, ⟨.count 3, 1062148687861060800⟩, ⟨.path 3, 1059889894455974400⟩, ⟨.privateRow 2 28, 2115015177451176000⟩, ⟨.privateRow 2 29, 3511654510147383600⟩, ⟨.privateRow 2 30, 4879121219706333600⟩, ⟨.privateRow 3 23, 40917445439270400⟩, ⟨.privateRow 3 24, 182991908770070400⟩, ⟨.privateRow 3 25, 558125321748714720⟩, ⟨.privateRow 3 26, 665334711778136400⟩, ⟨.privateRow 3 27, 1400285910588364800⟩, ⟨.privateRow 3 28, 1496754471189978000⟩, ⟨.privateRow 3 29, 1941305466952051200⟩, ⟨.privateRow 4 16, 91801960921440⟩, ⟨.privateRow 4 17, 248630310828900⟩, ⟨.privateRow 4 18, 1030685652163440⟩, ⟨.privateRow 4 19, 7458909324867000⟩, ⟨.privateRow 4 20, 13658091741534240⟩, ⟨.privateRow 4 21, 60417165531422700⟩, ⟨.privateRow 4 22, 109539411228046800⟩, ⟨.privateRow 4 23, 165189978514721160⟩, ⟨.privateRow 4 24, 334159137754041600⟩, ⟨.privateRow 4 25, 469165396534134300⟩, ⟨.privateRow 4 26, 597309458735349360⟩, ⟨.privateRow 4 27, 749471208962636160⟩, ⟨.privateRow 5 11, 15600333228480⟩, ⟨.privateRow 5 12, 16575354055260⟩, ⟨.privateRow 5 13, 88401888294720⟩, ⟨.privateRow 5 14, 246262403106720⟩, ⟨.privateRow 5 15, 999621352255680⟩, ⟨.privateRow 5 16, 1900640598336480⟩, ⟨.privateRow 5 17, 5400551721277440⟩, ⟨.privateRow 5 18, 16044942725491680⟩, ⟨.privateRow 5 19, 25724949493763520⟩, ⟨.privateRow 5 20, 40244959646171280⟩, ⟨.privateRow 5 21, 88199826835760640⟩, ⟨.privateRow 5 22, 136138907973868800⟩, ⟨.privateRow 5 23, 191319366647433024⟩, ⟨.privateRow 5 24, 246508665509826720⟩, ⟨.privateRow 5 25, 321429265839601920⟩, ⟨.privateRow 6 9, 46042650153500⟩, ⟨.privateRow 6 10, 58501249606800⟩, ⟨.privateRow 6 11, 186472733121675⟩, ⟨.privateRow 6 12, 375708025252560⟩, ⟨.privateRow 6 13, 959002627482900⟩, ⟨.privateRow 6 14, 2078294393082600⟩, ⟨.privateRow 6 15, 4889729446301700⟩, ⟨.privateRow 6 16, 7926032939151600⟩, ⟨.privateRow 6 17, 11602747838682000⟩, ⟨.privateRow 6 18, 24881448142951400⟩, ⟨.privateRow 6 19, 43282393276797675⟩, ⟨.privateRow 6 20, 64430769120517800⟩, ⟨.privateRow 6 21, 90252802830890700⟩, ⟨.privateRow 6 22, 116988848922025080⟩, ⟨.privateRow 6 23, 56066135091916950⟩, ⟨.privateRow 7 4, 6457930151400⟩, ⟨.privateRow 7 6, 71037231665400⟩, ⟨.privateRow 7 7, 37388016666000⟩, ⟨.privateRow 7 8, 102609334627800⟩, ⟨.privateRow 7 9, 267434283916800⟩, ⟨.privateRow 7 10, 550538545406850⟩, ⟨.privateRow 7 11, 1022936135981760⟩, ⟨.privateRow 7 12, 1999190662583400⟩, ⟨.privateRow 7 13, 3278641461480000⟩, ⟨.privateRow 7 14, 4712136367138200⟩, ⟨.privateRow 7 15, 8847364307418000⟩, ⟨.privateRow 7 16, 15656605859054160⟩, ⟨.privateRow 7 17, 25305040524363600⟩, ⟨.privateRow 7 18, 36992638389757050⟩, ⟨.privateRow 7 19, 51004732335757200⟩, ⟨.privateRow 7 20, 8429751490960800⟩, ⟨.privateRow 8 4, 221004720736800⟩, ⟨.privateRow 8 6, 218096763885000⟩, ⟨.privateRow 8 7, 414383851381500⟩, ⟨.privateRow 8 8, 692264787013800⟩, ⟨.privateRow 8 9, 1180993976437275⟩, ⟨.privateRow 8 10, 1878540126262800⟩, ⟨.privateRow 8 11, 2734933419117900⟩, ⟨.privateRow 8 12, 4755851586624600⟩, ⟨.privateRow 8 13, 7527973300097250⟩, ⟨.privateRow 8 14, 12356173023012000⟩, ⟨.privateRow 8 15, 18895903622996400⟩, ⟨.privateRow 8 16, 6501222201674200⟩, ⟨.privateRow 9 1, 311328389211840⟩, ⟨.privateRow 9 3, 214690300144320⟩, ⟨.privateRow 9 4, 411068780570448⟩, ⟨.privateRow 9 5, 669993258654720⟩, ⟨.privateRow 9 6, 1031355363438400⟩, ⟨.privateRow 9 7, 1560033322848000⟩, ⟨.privateRow 9 8, 2254248151515360⟩, ⟨.privateRow 9 9, 123762643612608⟩, ⟨.privateRow 9 10, 13146623673543360⟩, ⟨.privateRow 10 0, 778320973029600⟩, ⟨.privateRow 10 3, 5668771086898920⟩, ⟨.privateRow 11 0, 2531508619348800⟩, ⟨.privateRow 12 0, 1041879397759200⟩, ⟨.hall 3 28, 71811292534581600⟩]
  caps := #[0, 41672876168851200, 47737164987766800, 0, 4885944905095380, 0, 910957994845010, 0, 860759877148675, 0, 5762010559785480, 0, 0, 95426326195200000] }

theorem case_45_32_18_checked :
    (Witness.linear .negative case_45_32_18).check 45 32 18 = true := by
  change case_45_32_18.check 45 32 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_32_19 : Certificate := {
  objectiveScale := 448
  eta := 40043575
  rows := #[⟨.assumptionRow 19, 285⟩]
  caps := #[0, 0, 16214011, 5711343, 2480640, 945744, 381276, 161700, 59241, 29716, 16222998, 15662270, 10659000, 6000048] }

theorem case_45_32_19_checked :
    (Witness.linear .conditional case_45_32_19).check 45 32 19 = true := by
  change case_45_32_19.check 45 32 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_32_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58786, 58786, 41990, 25194] }

theorem case_45_32_20_checked :
    (Witness.linear .negative case_45_32_20).check 45 32 20 = true := by
  change case_45_32_20.check 45 32 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_33_1_checked :
    (Witness.rising).check 45 33 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_33_2_checked :
    (Witness.rising).check 45 33 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_33_3_checked :
    (Witness.rising).check 45 33 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_33_4_checked :
    (Witness.rising).check 45 33 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_33_5_checked :
    (Witness.rising).check 45 33 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_33_6_checked :
    (Witness.rising).check 45 33 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_33_7_checked :
    (Witness.rising).check 45 33 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_33_8_checked :
    (Witness.rising).check 45 33 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_33_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_45_33_9_checked :
    (Witness.linear .positive case_45_33_9).check 45 33 9 = true := by
  change case_45_33_9.check 45 33 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_33_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_45_33_10_checked :
    (Witness.linear .positive case_45_33_10).check 45 33 10 = true := by
  change case_45_33_10.check 45 33 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_33_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_45_33_11_checked :
    (Witness.linear .positive case_45_33_11).check 45 33 11 = true := by
  change case_45_33_11.check 45 33 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_33_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_45_33_12_checked :
    (Witness.linear .positive case_45_33_12).check 45 33 12 = true := by
  change case_45_33_12.check 45 33 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_33_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_45_33_13_checked :
    (Witness.linear .positive case_45_33_13).check 45 33 13 = true := by
  change case_45_33_13.check 45 33 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_33_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_45_33_14_checked :
    (Witness.linear .positive case_45_33_14).check 45 33 14 = true := by
  change case_45_33_14.check 45 33 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_33_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_45_33_15_checked :
    (Witness.linear .positive case_45_33_15).check 45 33 15 = true := by
  change case_45_33_15.check 45 33 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_33_16 : Certificate := {
  objectiveScale := 11
  eta := 25592905
  rows := #[⟨.assumptionRow 16, 27⟩]
  caps := #[0, 0, 7250704, 2074952, 600780, 176358, 53482, 16588, 5291, 1749, 606, 17556, 32319] }

theorem case_45_33_16_checked :
    (Witness.linear .conditional case_45_33_16).check 45 33 16 = true := by
  change case_45_33_16.check 45 33 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_33_17 : Certificate := {
  objectiveScale := 881
  eta := 826500285
  rows := #[⟨.assumptionRow 17, 1123⟩]
  caps := #[0, 0, 254926135, 79103992, 24732110, 7804326, 2490228, 805168, 264407, 66701932, 54035487, 30297894, 13748343] }

theorem case_45_33_17_checked :
    (Witness.linear .conditional case_45_33_17).check 45 33 17 = true := by
  change case_45_33_17.check 45 33 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_33_18 : Certificate := {
  objectiveScale := 883
  eta := 628204980
  rows := #[⟨.assumptionRow 18, 856⟩]
  caps := #[0, 0, 200355760, 63332225, 20301842, 7248120, 2524092, 865956, 297160, 87602768, 78777116, 49649622, 25728888] }

theorem case_45_33_18_checked :
    (Witness.linear .conditional case_45_33_18).check 45 33 18 = true := by
  change case_45_33_18.check 45 33 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_33_19 : Certificate := {
  objectiveScale := 997
  eta := 71655925
  rows := #[⟨.assumptionRow 19, 623⟩]
  caps := #[0, 0, 31702165, 11630850, 4822713, 1930248, 736032, 331184, 148580, 125995840, 122251624, 84149252, 48312402] }

theorem case_45_33_19_checked :
    (Witness.linear .conditional case_45_33_19).check 45 33 19 = true := by
  change case_45_33_19.check 45 33 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_33_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 208012, 208012, 149226, 90440] }

theorem case_45_33_20_checked :
    (Witness.linear .negative case_45_33_20).check 45 33 20 = true := by
  change case_45_33_20.check 45 33 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_33_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58786, 58786] }

theorem case_45_33_21_checked :
    (Witness.linear .negative case_45_33_21).check 45 33 21 = true := by
  change case_45_33_21.check 45 33 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_34_1_checked :
    (Witness.rising).check 45 34 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_34_2_checked :
    (Witness.rising).check 45 34 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_34_3_checked :
    (Witness.rising).check 45 34 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_34_4_checked :
    (Witness.rising).check 45 34 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_34_5_checked :
    (Witness.rising).check 45 34 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_34_6_checked :
    (Witness.rising).check 45 34 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_34_7_checked :
    (Witness.rising).check 45 34 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_34_8_checked :
    (Witness.rising).check 45 34 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_34_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_45_34_9_checked :
    (Witness.linear .positive case_45_34_9).check 45 34 9 = true := by
  change case_45_34_9.check 45 34 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_34_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_45_34_10_checked :
    (Witness.linear .positive case_45_34_10).check 45 34 10 = true := by
  change case_45_34_10.check 45 34 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_34_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_45_34_11_checked :
    (Witness.linear .positive case_45_34_11).check 45 34 11 = true := by
  change case_45_34_11.check 45 34 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_34_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_45_34_12_checked :
    (Witness.linear .positive case_45_34_12).check 45 34 12 = true := by
  change case_45_34_12.check 45 34 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_34_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_45_34_13_checked :
    (Witness.linear .positive case_45_34_13).check 45 34 13 = true := by
  change case_45_34_13.check 45 34 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_34_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_45_34_14_checked :
    (Witness.linear .positive case_45_34_14).check 45 34 14 = true := by
  change case_45_34_14.check 45 34 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_34_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_45_34_15_checked :
    (Witness.linear .positive case_45_34_15).check 45 34 15 = true := by
  change case_45_34_15.check 45 34 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_34_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_45_34_16_checked :
    (Witness.linear .positive case_45_34_16).check 45 34 16 = true := by
  change case_45_34_16.check 45 34 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_34_17 : Certificate := {
  objectiveScale := 778
  eta := 1152703305
  rows := #[⟨.assumptionRow 17, 1089⟩]
  caps := #[0, 0, 340768230, 101658436, 30639780, 9343098, 2887144, 905814, 312455, 93616325, 72595314, 38907858] }

theorem case_45_34_17_checked :
    (Witness.linear .conditional case_45_34_17).check 45 34 17 = true := by
  change case_45_34_17.check 45 34 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_34_18 : Certificate := {
  objectiveScale := 1
  eta := 852150
  rows := #[⟨.assumptionRow 18, 1⟩]
  caps := #[0, 0, 264385, 81719, 28424, 9690, 3264, 1092, 227240, 264385, 182666, 100947] }

theorem case_45_34_18_checked :
    (Witness.linear .conditional case_45_34_18).check 45 34 18 = true := by
  change case_45_34_18.check 45 34 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_34_19 : Certificate := {
  objectiveScale := 119
  eta := 18911750
  rows := #[⟨.assumptionRow 19, 81⟩]
  caps := #[0, 0, 6369275, 2696727, 987411, 372096, 154224, 56448, 34284835, 42159575, 31461815, 19040527] }

theorem case_45_34_19_checked :
    (Witness.linear .conditional case_45_34_19).check 45 34 19 = true := by
  change case_45_34_19.check 45 34 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_34_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900, 534888, 326876] }

theorem case_45_34_20_checked :
    (Witness.linear .negative case_45_34_20).check 45 34 20 = true := by
  change case_45_34_20.check 45 34 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_34_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208012, 208012] }

theorem case_45_34_21_checked :
    (Witness.linear .negative case_45_34_21).check 45 34 21 = true := by
  change case_45_34_21.check 45 34 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_34_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_34_22_checked :
    (Witness.linear .negative case_45_34_22).check 45 34 22 = true := by
  change case_45_34_22.check 45 34 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_35_1_checked :
    (Witness.rising).check 45 35 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_35_2_checked :
    (Witness.rising).check 45 35 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_35_3_checked :
    (Witness.rising).check 45 35 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_35_4_checked :
    (Witness.rising).check 45 35 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_35_5_checked :
    (Witness.rising).check 45 35 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_35_6_checked :
    (Witness.rising).check 45 35 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_35_7_checked :
    (Witness.rising).check 45 35 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_35_8_checked :
    (Witness.rising).check 45 35 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_35_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_45_35_9_checked :
    (Witness.linear .positive case_45_35_9).check 45 35 9 = true := by
  change case_45_35_9.check 45 35 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_35_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_45_35_10_checked :
    (Witness.linear .positive case_45_35_10).check 45 35 10 = true := by
  change case_45_35_10.check 45 35 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_35_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_45_35_11_checked :
    (Witness.linear .positive case_45_35_11).check 45 35 11 = true := by
  change case_45_35_11.check 45 35 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_35_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_45_35_12_checked :
    (Witness.linear .positive case_45_35_12).check 45 35 12 = true := by
  change case_45_35_12.check 45 35 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_35_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_45_35_13_checked :
    (Witness.linear .positive case_45_35_13).check 45 35 13 = true := by
  change case_45_35_13.check 45 35 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_35_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_45_35_14_checked :
    (Witness.linear .positive case_45_35_14).check 45 35 14 = true := by
  change case_45_35_14.check 45 35 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_35_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_45_35_15_checked :
    (Witness.linear .positive case_45_35_15).check 45 35 15 = true := by
  change case_45_35_15.check 45 35 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_35_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_45_35_16_checked :
    (Witness.linear .positive case_45_35_16).check 45 35 16 = true := by
  change case_45_35_16.check 45 35 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_35_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_45_35_17_checked :
    (Witness.linear .positive case_45_35_17).check 45 35 17 = true := by
  change case_45_35_17.check 45 35 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_35_18 : Certificate := {
  objectiveScale := 435
  eta := 536854500
  rows := #[⟨.assumptionRow 18, 466⟩]
  caps := #[0, 0, 173696575, 55814077, 17871590, 5717100, 1830900, 603772, 254451990, 223405325, 138201250] }

theorem case_45_35_18_checked :
    (Witness.linear .conditional case_45_35_18).check 45 35 18 = true := by
  change case_45_35_18.check 45 35 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_35_19 : Certificate := {
  objectiveScale := 645
  eta := 306173010
  rows := #[⟨.assumptionRow 19, 506⟩]
  caps := #[0, 0, 99048235, 38306983, 13632861, 4612440, 1767456, 688275, 474732765, 450588515, 304162925] }

theorem case_45_35_19_checked :
    (Witness.linear .conditional case_45_35_19).check 45 35 19 = true := by
  change case_45_35_19.check 45 35 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_35_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 2674440, 2674440, 1931540, 1188640] }

theorem case_45_35_20_checked :
    (Witness.linear .negative case_45_35_20).check 45 35 20 = true := by
  change case_45_35_20.check 45 35 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_35_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900] }

theorem case_45_35_21_checked :
    (Witness.linear .negative case_45_35_21).check 45 35 21 = true := by
  change case_45_35_21.check 45 35 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_35_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_35_22_checked :
    (Witness.linear .negative case_45_35_22).check 45 35 22 = true := by
  change case_45_35_22.check 45 35 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_36_1_checked :
    (Witness.rising).check 45 36 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_36_2_checked :
    (Witness.rising).check 45 36 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_36_3_checked :
    (Witness.rising).check 45 36 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_36_4_checked :
    (Witness.rising).check 45 36 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_36_5_checked :
    (Witness.rising).check 45 36 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_36_6_checked :
    (Witness.rising).check 45 36 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_36_7_checked :
    (Witness.rising).check 45 36 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_36_8_checked :
    (Witness.rising).check 45 36 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_36_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_45_36_9_checked :
    (Witness.linear .positive case_45_36_9).check 45 36 9 = true := by
  change case_45_36_9.check 45 36 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_36_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_45_36_10_checked :
    (Witness.linear .positive case_45_36_10).check 45 36 10 = true := by
  change case_45_36_10.check 45 36 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_36_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_45_36_11_checked :
    (Witness.linear .positive case_45_36_11).check 45 36 11 = true := by
  change case_45_36_11.check 45 36 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_36_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_45_36_12_checked :
    (Witness.linear .positive case_45_36_12).check 45 36 12 = true := by
  change case_45_36_12.check 45 36 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_36_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_45_36_13_checked :
    (Witness.linear .positive case_45_36_13).check 45 36 13 = true := by
  change case_45_36_13.check 45 36 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_36_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_45_36_14_checked :
    (Witness.linear .positive case_45_36_14).check 45 36 14 = true := by
  change case_45_36_14.check 45 36 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_36_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_45_36_15_checked :
    (Witness.linear .positive case_45_36_15).check 45 36 15 = true := by
  change case_45_36_15.check 45 36 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_36_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_45_36_16_checked :
    (Witness.linear .positive case_45_36_16).check 45 36 16 = true := by
  change case_45_36_16.check 45 36 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_36_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_45_36_17_checked :
    (Witness.linear .positive case_45_36_17).check 45 36 17 = true := by
  change case_45_36_17.check 45 36 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_36_18 : Certificate := {
  objectiveScale := 7
  eta := 54557265
  rows := #[⟨.assumptionRow 18, 11⟩]
  caps := #[0, 0, 15594345, 4494545, 1307504, 397936, 122740, 38454, 12272, 4004] }

theorem case_45_36_18_checked :
    (Witness.linear .conditional case_45_36_18).check 45 36 18 = true := by
  change case_45_36_18.check 45 36 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_36_19 : Certificate := {
  objectiveScale := 27
  eta := 15885870
  rows := #[⟨.assumptionRow 19, 22⟩]
  caps := #[0, 0, 5936645, 2071817, 692835, 244188, 93024, 50565270, 57860985, 41755350] }

theorem case_45_36_19_checked :
    (Witness.linear .conditional case_45_36_19).check 45 36 19 = true := by
  change case_45_36_19.check 45 36 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_36_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 9694845, 9694845, 7020405, 4345965] }

theorem case_45_36_20_checked :
    (Witness.linear .negative case_45_36_20).check 45 36 20 = true := by
  change case_45_36_20.check 45 36 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_36_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 2674440, 2674440] }

theorem case_45_36_21_checked :
    (Witness.linear .negative case_45_36_21).check 45 36 21 = true := by
  change case_45_36_21.check 45 36 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_36_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_36_22_checked :
    (Witness.linear .negative case_45_36_22).check 45 36 22 = true := by
  change case_45_36_22.check 45 36 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_36_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_36_23_checked :
    (Witness.linear .negative case_45_36_23).check 45 36 23 = true := by
  change case_45_36_23.check 45 36 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_37_1_checked :
    (Witness.rising).check 45 37 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_37_2_checked :
    (Witness.rising).check 45 37 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_37_3_checked :
    (Witness.rising).check 45 37 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_37_4_checked :
    (Witness.rising).check 45 37 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_37_5_checked :
    (Witness.rising).check 45 37 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_37_6_checked :
    (Witness.rising).check 45 37 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_37_7_checked :
    (Witness.rising).check 45 37 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_37_8_checked :
    (Witness.rising).check 45 37 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_37_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1] }

theorem case_45_37_9_checked :
    (Witness.linear .positive case_45_37_9).check 45 37 9 = true := by
  change case_45_37_9.check 45 37 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_37_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_45_37_10_checked :
    (Witness.linear .positive case_45_37_10).check 45 37 10 = true := by
  change case_45_37_10.check 45 37 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_37_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_45_37_11_checked :
    (Witness.linear .positive case_45_37_11).check 45 37 11 = true := by
  change case_45_37_11.check 45 37 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_37_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_45_37_12_checked :
    (Witness.linear .positive case_45_37_12).check 45 37 12 = true := by
  change case_45_37_12.check 45 37 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_37_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_45_37_13_checked :
    (Witness.linear .positive case_45_37_13).check 45 37 13 = true := by
  change case_45_37_13.check 45 37 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_37_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_45_37_14_checked :
    (Witness.linear .positive case_45_37_14).check 45 37 14 = true := by
  change case_45_37_14.check 45 37 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_37_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_45_37_15_checked :
    (Witness.linear .positive case_45_37_15).check 45 37 15 = true := by
  change case_45_37_15.check 45 37 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_37_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_45_37_16_checked :
    (Witness.linear .positive case_45_37_16).check 45 37 16 = true := by
  change case_45_37_16.check 45 37 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_37_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_45_37_17_checked :
    (Witness.linear .positive case_45_37_17).check 45 37 17 = true := by
  change case_45_37_17.check 45 37 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_37_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_45_37_18_checked :
    (Witness.linear .positive case_45_37_18).check 45 37 18 = true := by
  change case_45_37_18.check 45 37 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_37_19 : Certificate := {
  objectiveScale := 85
  eta := 114654540
  rows := #[⟨.assumptionRow 19, 77⟩]
  caps := #[0, 0, 35619870, 12666445, 4331107, 1443810, 472872, 373986900, 348704265] }

theorem case_45_37_19_checked :
    (Witness.linear .conditional case_45_37_19).check 45 37 19 = true := by
  change case_45_37_19.check 45 37 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_37_20 : Certificate := {
  objectiveScale := 5
  eta := 740025
  rows := #[⟨.assumptionRow 20, 3⟩]
  caps := #[0, 0, 284625, 110561, 46398, 16473, 7752, 28514250, 27943965] }

theorem case_45_37_20_checked :
    (Witness.linear .conditional case_45_37_20).check 45 37 20 = true := by
  change case_45_37_20.check 45 37 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_37_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 9694845, 9694845] }

theorem case_45_37_21_checked :
    (Witness.linear .negative case_45_37_21).check 45 37 21 = true := by
  change case_45_37_21.check 45 37 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_37_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_37_22_checked :
    (Witness.linear .negative case_45_37_22).check 45 37 22 = true := by
  change case_45_37_22.check 45 37 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_37_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_37_23_checked :
    (Witness.linear .negative case_45_37_23).check 45 37 23 = true := by
  change case_45_37_23.check 45 37 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_37_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_37_24_checked :
    (Witness.linear .negative case_45_37_24).check 45 37 24 = true := by
  change case_45_37_24.check 45 37 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_38_1_checked :
    (Witness.rising).check 45 38 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_38_2_checked :
    (Witness.rising).check 45 38 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_38_3_checked :
    (Witness.rising).check 45 38 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_38_4_checked :
    (Witness.rising).check 45 38 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_38_5_checked :
    (Witness.rising).check 45 38 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_38_6_checked :
    (Witness.rising).check 45 38 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_38_7_checked :
    (Witness.rising).check 45 38 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_38_8_checked :
    (Witness.rising).check 45 38 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_38_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_45_38_9_checked :
    (Witness.linear .positive case_45_38_9).check 45 38 9 = true := by
  change case_45_38_9.check 45 38 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_38_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_45_38_10_checked :
    (Witness.linear .positive case_45_38_10).check 45 38 10 = true := by
  change case_45_38_10.check 45 38 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_38_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_45_38_11_checked :
    (Witness.linear .positive case_45_38_11).check 45 38 11 = true := by
  change case_45_38_11.check 45 38 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_38_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_45_38_12_checked :
    (Witness.linear .positive case_45_38_12).check 45 38 12 = true := by
  change case_45_38_12.check 45 38 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_38_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42] }

theorem case_45_38_13_checked :
    (Witness.linear .positive case_45_38_13).check 45 38 13 = true := by
  change case_45_38_13.check 45 38 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_38_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_45_38_14_checked :
    (Witness.linear .positive case_45_38_14).check 45 38 14 = true := by
  change case_45_38_14.check 45 38 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_38_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_45_38_15_checked :
    (Witness.linear .positive case_45_38_15).check 45 38 15 = true := by
  change case_45_38_15.check 45 38 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_38_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_45_38_16_checked :
    (Witness.linear .positive case_45_38_16).check 45 38 16 = true := by
  change case_45_38_16.check 45 38 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_38_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_45_38_17_checked :
    (Witness.linear .positive case_45_38_17).check 45 38 17 = true := by
  change case_45_38_17.check 45 38 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_38_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_45_38_18_checked :
    (Witness.linear .positive case_45_38_18).check 45 38 18 = true := by
  change case_45_38_18.check 45 38 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_38_19 : Certificate := {
  objectiveScale := 17
  eta := 2133866400
  rows := #[⟨.assumptionRow 19, 45⟩]
  caps := #[0, 0, 589294500, 164812365, 46468395, 13223620, 3803648, 1107890] }

theorem case_45_38_19_checked :
    (Witness.linear .conditional case_45_38_19).check 45 38 19 = true := by
  change case_45_38_19.check 45 38 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_38_20 : Certificate := {
  objectiveScale := 32
  eta := 4242810
  rows := #[⟨.assumptionRow 20, 19⟩]
  caps := #[0, 0, 1701425, 629717, 277761, 100776, 660009840, 648223950] }

theorem case_45_38_20_checked :
    (Witness.linear .conditional case_45_38_20).check 45 38 20 = true := by
  change case_45_38_20.check 45 38 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_38_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 35357670, 35357670] }

theorem case_45_38_21_checked :
    (Witness.linear .negative case_45_38_21).check 45 38 21 = true := by
  change case_45_38_21.check 45 38 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_38_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_38_22_checked :
    (Witness.linear .negative case_45_38_22).check 45 38 22 = true := by
  change case_45_38_22.check 45 38 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_38_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_38_23_checked :
    (Witness.linear .negative case_45_38_23).check 45 38 23 = true := by
  change case_45_38_23.check 45 38 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_38_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_45_38_24_checked :
    (Witness.linear .negative case_45_38_24).check 45 38 24 = true := by
  change case_45_38_24.check 45 38 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_39_1_checked :
    (Witness.rising).check 45 39 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_39_2_checked :
    (Witness.rising).check 45 39 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_39_3_checked :
    (Witness.rising).check 45 39 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_39_4_checked :
    (Witness.rising).check 45 39 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_39_5_checked :
    (Witness.rising).check 45 39 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_39_6_checked :
    (Witness.rising).check 45 39 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_39_7_checked :
    (Witness.rising).check 45 39 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_39_8_checked :
    (Witness.rising).check 45 39 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_39_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_45_39_9_checked :
    (Witness.linear .positive case_45_39_9).check 45 39 9 = true := by
  change case_45_39_9.check 45 39 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_39_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_45_39_10_checked :
    (Witness.linear .positive case_45_39_10).check 45 39 10 = true := by
  change case_45_39_10.check 45 39 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_39_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_45_39_11_checked :
    (Witness.linear .positive case_45_39_11).check 45 39 11 = true := by
  change case_45_39_11.check 45 39 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_39_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_45_39_12_checked :
    (Witness.linear .positive case_45_39_12).check 45 39 12 = true := by
  change case_45_39_12.check 45 39 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_39_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_45_39_13_checked :
    (Witness.linear .positive case_45_39_13).check 45 39 13 = true := by
  change case_45_39_13.check 45 39 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_39_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429] }

theorem case_45_39_14_checked :
    (Witness.linear .positive case_45_39_14).check 45 39 14 = true := by
  change case_45_39_14.check 45 39 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_39_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430] }

theorem case_45_39_15_checked :
    (Witness.linear .positive case_45_39_15).check 45 39 15 = true := by
  change case_45_39_15.check 45 39 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_39_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862] }

theorem case_45_39_16_checked :
    (Witness.linear .positive case_45_39_16).check 45 39 16 = true := by
  change case_45_39_16.check 45 39 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_39_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796] }

theorem case_45_39_17_checked :
    (Witness.linear .positive case_45_39_17).check 45 39 17 = true := by
  change case_45_39_17.check 45 39 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_39_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_45_39_18_checked :
    (Witness.linear .positive case_45_39_18).check 45 39 18 = true := by
  change case_45_39_18.check 45 39 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_39_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_45_39_19_checked :
    (Witness.linear .positive case_45_39_19).check 45 39 19 = true := by
  change case_45_39_19.check 45 39 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_39_20 : Certificate := {
  objectiveScale := 27
  eta := 50075025
  rows := #[⟨.assumptionRow 20, 22⟩]
  caps := #[0, 0, 15885870, 5936645, 2071817, 692835, 491285520] }

theorem case_45_39_20_checked :
    (Witness.linear .conditional case_45_39_20).check 45 39 20 = true := by
  change case_45_39_20.check 45 39 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_39_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 129644790, 129644790] }

theorem case_45_39_21_checked :
    (Witness.linear .negative case_45_39_21).check 45 39 21 = true := by
  change case_45_39_21.check 45 39 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_39_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_45_39_22_checked :
    (Witness.linear .negative case_45_39_22).check 45 39 22 = true := by
  change case_45_39_22.check 45 39 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_39_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_45_39_23_checked :
    (Witness.linear .negative case_45_39_23).check 45 39 23 = true := by
  change case_45_39_23.check 45 39 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_39_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_45_39_24_checked :
    (Witness.linear .negative case_45_39_24).check 45 39 24 = true := by
  change case_45_39_24.check 45 39 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_39_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_45_39_25_checked :
    (Witness.linear .negative case_45_39_25).check 45 39 25 = true := by
  change case_45_39_25.check 45 39 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_40_1_checked :
    (Witness.rising).check 45 40 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_40_2_checked :
    (Witness.rising).check 45 40 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_40_3_checked :
    (Witness.rising).check 45 40 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_40_4_checked :
    (Witness.rising).check 45 40 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_40_5_checked :
    (Witness.rising).check 45 40 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_40_6_checked :
    (Witness.rising).check 45 40 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_40_7_checked :
    (Witness.rising).check 45 40 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_40_8_checked :
    (Witness.rising).check 45 40 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_40_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_45_40_9_checked :
    (Witness.linear .positive case_45_40_9).check 45 40 9 = true := by
  change case_45_40_9.check 45 40 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_40_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_45_40_10_checked :
    (Witness.linear .positive case_45_40_10).check 45 40 10 = true := by
  change case_45_40_10.check 45 40 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_40_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_45_40_11_checked :
    (Witness.linear .positive case_45_40_11).check 45 40 11 = true := by
  change case_45_40_11.check 45 40 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_40_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_45_40_12_checked :
    (Witness.linear .positive case_45_40_12).check 45 40 12 = true := by
  change case_45_40_12.check 45 40 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_40_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_45_40_13_checked :
    (Witness.linear .positive case_45_40_13).check 45 40 13 = true := by
  change case_45_40_13.check 45 40 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_40_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_45_40_14_checked :
    (Witness.linear .positive case_45_40_14).check 45 40 14 = true := by
  change case_45_40_14.check 45 40 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_40_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862] }

theorem case_45_40_15_checked :
    (Witness.linear .positive case_45_40_15).check 45 40 15 = true := by
  change case_45_40_15.check 45 40 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_40_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796] }

theorem case_45_40_16_checked :
    (Witness.linear .positive case_45_40_16).check 45 40 16 = true := by
  change case_45_40_16.check 45 40 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_40_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786] }

theorem case_45_40_17_checked :
    (Witness.linear .positive case_45_40_17).check 45 40 17 = true := by
  change case_45_40_17.check 45 40 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_40_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012] }

theorem case_45_40_18_checked :
    (Witness.linear .positive case_45_40_18).check 45 40 18 = true := by
  change case_45_40_18.check 45 40 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_40_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900] }

theorem case_45_40_19_checked :
    (Witness.linear .positive case_45_40_19).check 45 40 19 = true := by
  change case_45_40_19.check 45 40 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_40_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440] }

theorem case_45_40_20_checked :
    (Witness.linear .positive case_45_40_20).check 45 40 20 = true := by
  change case_45_40_20.check 45 40 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_40_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 477638700, 477638700] }

theorem case_45_40_21_checked :
    (Witness.linear .negative case_45_40_21).check 45 40 21 = true := by
  change case_45_40_21.check 45 40 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_40_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_45_40_22_checked :
    (Witness.linear .negative case_45_40_22).check 45 40 22 = true := by
  change case_45_40_22.check 45 40 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_40_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_45_40_23_checked :
    (Witness.linear .negative case_45_40_23).check 45 40 23 = true := by
  change case_45_40_23.check 45 40 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_40_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_45_40_24_checked :
    (Witness.linear .negative case_45_40_24).check 45 40 24 = true := by
  change case_45_40_24.check 45 40 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_40_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_45_40_25_checked :
    (Witness.linear .negative case_45_40_25).check 45 40 25 = true := by
  change case_45_40_25.check 45 40 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_40_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_45_40_26_checked :
    (Witness.linear .negative case_45_40_26).check 45 40 26 = true := by
  change case_45_40_26.check 45 40 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_41_1_checked :
    (Witness.rising).check 45 41 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_41_2_checked :
    (Witness.rising).check 45 41 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_41_3_checked :
    (Witness.rising).check 45 41 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_41_4_checked :
    (Witness.rising).check 45 41 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_41_5_checked :
    (Witness.rising).check 45 41 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_41_6_checked :
    (Witness.rising).check 45 41 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_41_7_checked :
    (Witness.rising).check 45 41 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_41_8_checked :
    (Witness.rising).check 45 41 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_41_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_45_41_9_checked :
    (Witness.linear .positive case_45_41_9).check 45 41 9 = true := by
  change case_45_41_9.check 45 41 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_41_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_45_41_10_checked :
    (Witness.linear .positive case_45_41_10).check 45 41 10 = true := by
  change case_45_41_10.check 45 41 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_41_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_45_41_11_checked :
    (Witness.linear .positive case_45_41_11).check 45 41 11 = true := by
  change case_45_41_11.check 45 41 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_41_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_45_41_12_checked :
    (Witness.linear .positive case_45_41_12).check 45 41 12 = true := by
  change case_45_41_12.check 45 41 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_41_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_45_41_13_checked :
    (Witness.linear .positive case_45_41_13).check 45 41 13 = true := by
  change case_45_41_13.check 45 41 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_41_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_45_41_14_checked :
    (Witness.linear .positive case_45_41_14).check 45 41 14 = true := by
  change case_45_41_14.check 45 41 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_41_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796] }

theorem case_45_41_15_checked :
    (Witness.linear .positive case_45_41_15).check 45 41 15 = true := by
  change case_45_41_15.check 45 41 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_41_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786] }

theorem case_45_41_16_checked :
    (Witness.linear .positive case_45_41_16).check 45 41 16 = true := by
  change case_45_41_16.check 45 41 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_41_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012] }

theorem case_45_41_17_checked :
    (Witness.linear .positive case_45_41_17).check 45 41 17 = true := by
  change case_45_41_17.check 45 41 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_41_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900] }

theorem case_45_41_18_checked :
    (Witness.linear .positive case_45_41_18).check 45 41 18 = true := by
  change case_45_41_18.check 45 41 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_41_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440] }

theorem case_45_41_19_checked :
    (Witness.linear .positive case_45_41_19).check 45 41 19 = true := by
  change case_45_41_19.check 45 41 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_41_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845] }

theorem case_45_41_20_checked :
    (Witness.linear .positive case_45_41_20).check 45 41 20 = true := by
  change case_45_41_20.check 45 41 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_41_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 1767263190, 1767263190] }

theorem case_45_41_21_checked :
    (Witness.linear .negative case_45_41_21).check 45 41 21 = true := by
  change case_45_41_21.check 45 41 21 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_41_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_45_41_22_checked :
    (Witness.linear .negative case_45_41_22).check 45 41 22 = true := by
  change case_45_41_22.check 45 41 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_41_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_45_41_23_checked :
    (Witness.linear .negative case_45_41_23).check 45 41 23 = true := by
  change case_45_41_23.check 45 41 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_41_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_45_41_24_checked :
    (Witness.linear .negative case_45_41_24).check 45 41 24 = true := by
  change case_45_41_24.check 45 41 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_41_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_45_41_25_checked :
    (Witness.linear .negative case_45_41_25).check 45 41 25 = true := by
  change case_45_41_25.check 45 41 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_41_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_45_41_26_checked :
    (Witness.linear .negative case_45_41_26).check 45 41 26 = true := by
  change case_45_41_26.check 45 41 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_42_1_checked :
    (Witness.rising).check 45 42 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_42_2_checked :
    (Witness.rising).check 45 42 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_42_3_checked :
    (Witness.rising).check 45 42 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_42_4_checked :
    (Witness.rising).check 45 42 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_42_5_checked :
    (Witness.rising).check 45 42 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_42_6_checked :
    (Witness.rising).check 45 42 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_42_7_checked :
    (Witness.rising).check 45 42 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_42_8_checked :
    (Witness.rising).check 45 42 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_42_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_45_42_9_checked :
    (Witness.linear .positive case_45_42_9).check 45 42 9 = true := by
  change case_45_42_9.check 45 42 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_42_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_45_42_10_checked :
    (Witness.linear .positive case_45_42_10).check 45 42 10 = true := by
  change case_45_42_10.check 45 42 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_42_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_45_42_11_checked :
    (Witness.linear .positive case_45_42_11).check 45 42 11 = true := by
  change case_45_42_11.check 45 42 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_42_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_45_42_12_checked :
    (Witness.linear .positive case_45_42_12).check 45 42 12 = true := by
  change case_45_42_12.check 45 42 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_42_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_45_42_13_checked :
    (Witness.linear .positive case_45_42_13).check 45 42 13 = true := by
  change case_45_42_13.check 45 42 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_42_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_45_42_14_checked :
    (Witness.linear .positive case_45_42_14).check 45 42 14 = true := by
  change case_45_42_14.check 45 42 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_42_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_45_42_15_checked :
    (Witness.linear .positive case_45_42_15).check 45 42 15 = true := by
  change case_45_42_15.check 45 42 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_42_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012] }

theorem case_45_42_16_checked :
    (Witness.linear .positive case_45_42_16).check 45 42 16 = true := by
  change case_45_42_16.check 45 42 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_42_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900] }

theorem case_45_42_17_checked :
    (Witness.linear .positive case_45_42_17).check 45 42 17 = true := by
  change case_45_42_17.check 45 42 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_42_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440] }

theorem case_45_42_18_checked :
    (Witness.linear .positive case_45_42_18).check 45 42 18 = true := by
  change case_45_42_18.check 45 42 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_42_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845] }

theorem case_45_42_19_checked :
    (Witness.linear .positive case_45_42_19).check 45 42 19 = true := by
  change case_45_42_19.check 45 42 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_42_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670] }

theorem case_45_42_20_checked :
    (Witness.linear .positive case_45_42_20).check 45 42 20 = true := by
  change case_45_42_20.check 45 42 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_42_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790] }

theorem case_45_42_21_checked :
    (Witness.linear .positive case_45_42_21).check 45 42 21 = true := by
  change case_45_42_21.check 45 42 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_42_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_45_42_22_checked :
    (Witness.linear .negative case_45_42_22).check 45 42 22 = true := by
  change case_45_42_22.check 45 42 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_42_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_45_42_23_checked :
    (Witness.linear .negative case_45_42_23).check 45 42 23 = true := by
  change case_45_42_23.check 45 42 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_42_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_45_42_24_checked :
    (Witness.linear .negative case_45_42_24).check 45 42 24 = true := by
  change case_45_42_24.check 45 42 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_42_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_45_42_25_checked :
    (Witness.linear .negative case_45_42_25).check 45 42 25 = true := by
  change case_45_42_25.check 45 42 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_42_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_45_42_26_checked :
    (Witness.linear .negative case_45_42_26).check 45 42 26 = true := by
  change case_45_42_26.check 45 42 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_42_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_45_42_27_checked :
    (Witness.linear .negative case_45_42_27).check 45 42 27 = true := by
  change case_45_42_27.check 45 42 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_43_1_checked :
    (Witness.rising).check 45 43 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_43_2_checked :
    (Witness.rising).check 45 43 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_43_3_checked :
    (Witness.rising).check 45 43 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_43_4_checked :
    (Witness.rising).check 45 43 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_43_5_checked :
    (Witness.rising).check 45 43 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_43_6_checked :
    (Witness.rising).check 45 43 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_43_7_checked :
    (Witness.rising).check 45 43 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_43_8_checked :
    (Witness.rising).check 45 43 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_43_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_45_43_9_checked :
    (Witness.linear .positive case_45_43_9).check 45 43 9 = true := by
  change case_45_43_9.check 45 43 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_43_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_45_43_10_checked :
    (Witness.linear .positive case_45_43_10).check 45 43 10 = true := by
  change case_45_43_10.check 45 43 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_43_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_45_43_11_checked :
    (Witness.linear .positive case_45_43_11).check 45 43 11 = true := by
  change case_45_43_11.check 45 43 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_43_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_45_43_12_checked :
    (Witness.linear .positive case_45_43_12).check 45 43 12 = true := by
  change case_45_43_12.check 45 43 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_43_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_45_43_13_checked :
    (Witness.linear .positive case_45_43_13).check 45 43 13 = true := by
  change case_45_43_13.check 45 43 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_43_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_45_43_14_checked :
    (Witness.linear .positive case_45_43_14).check 45 43 14 = true := by
  change case_45_43_14.check 45 43 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_43_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_45_43_15_checked :
    (Witness.linear .positive case_45_43_15).check 45 43 15 = true := by
  change case_45_43_15.check 45 43 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_43_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900] }

theorem case_45_43_16_checked :
    (Witness.linear .positive case_45_43_16).check 45 43 16 = true := by
  change case_45_43_16.check 45 43 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_43_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440] }

theorem case_45_43_17_checked :
    (Witness.linear .positive case_45_43_17).check 45 43 17 = true := by
  change case_45_43_17.check 45 43 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_43_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845] }

theorem case_45_43_18_checked :
    (Witness.linear .positive case_45_43_18).check 45 43 18 = true := by
  change case_45_43_18.check 45 43 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_43_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670] }

theorem case_45_43_19_checked :
    (Witness.linear .positive case_45_43_19).check 45 43 19 = true := by
  change case_45_43_19.check 45 43 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_43_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790] }

theorem case_45_43_20_checked :
    (Witness.linear .positive case_45_43_20).check 45 43 20 = true := by
  change case_45_43_20.check 45 43 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_43_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700] }

theorem case_45_43_21_checked :
    (Witness.linear .positive case_45_43_21).check 45 43 21 = true := by
  change case_45_43_21.check 45 43 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_43_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_45_43_22_checked :
    (Witness.linear .negative case_45_43_22).check 45 43 22 = true := by
  change case_45_43_22.check 45 43 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_43_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_45_43_23_checked :
    (Witness.linear .negative case_45_43_23).check 45 43 23 = true := by
  change case_45_43_23.check 45 43 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_43_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_45_43_24_checked :
    (Witness.linear .negative case_45_43_24).check 45 43 24 = true := by
  change case_45_43_24.check 45 43 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_43_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_45_43_25_checked :
    (Witness.linear .negative case_45_43_25).check 45 43 25 = true := by
  change case_45_43_25.check 45 43 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_43_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_45_43_26_checked :
    (Witness.linear .negative case_45_43_26).check 45 43 26 = true := by
  change case_45_43_26.check 45 43 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_43_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_45_43_27_checked :
    (Witness.linear .negative case_45_43_27).check 45 43 27 = true := by
  change case_45_43_27.check 45 43 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_43_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_45_43_28_checked :
    (Witness.linear .negative case_45_43_28).check 45 43 28 = true := by
  change case_45_43_28.check 45 43 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_44_1_checked :
    (Witness.rising).check 45 44 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_44_2_checked :
    (Witness.rising).check 45 44 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_44_3_checked :
    (Witness.rising).check 45 44 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_44_4_checked :
    (Witness.rising).check 45 44 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_44_5_checked :
    (Witness.rising).check 45 44 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_44_6_checked :
    (Witness.rising).check 45 44 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_44_7_checked :
    (Witness.rising).check 45 44 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_45_44_8_checked :
    (Witness.rising).check 45 44 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_44_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_45_44_9_checked :
    (Witness.linear .positive case_45_44_9).check 45 44 9 = true := by
  change case_45_44_9.check 45 44 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_44_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_45_44_10_checked :
    (Witness.linear .positive case_45_44_10).check 45 44 10 = true := by
  change case_45_44_10.check 45 44 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_44_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_45_44_11_checked :
    (Witness.linear .positive case_45_44_11).check 45 44 11 = true := by
  change case_45_44_11.check 45 44 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_44_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_45_44_12_checked :
    (Witness.linear .positive case_45_44_12).check 45 44 12 = true := by
  change case_45_44_12.check 45 44 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_44_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_45_44_13_checked :
    (Witness.linear .positive case_45_44_13).check 45 44 13 = true := by
  change case_45_44_13.check 45 44 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_44_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_45_44_14_checked :
    (Witness.linear .positive case_45_44_14).check 45 44 14 = true := by
  change case_45_44_14.check 45 44 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_44_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_45_44_15_checked :
    (Witness.linear .positive case_45_44_15).check 45 44 15 = true := by
  change case_45_44_15.check 45 44 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_44_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_45_44_16_checked :
    (Witness.linear .positive case_45_44_16).check 45 44 16 = true := by
  change case_45_44_16.check 45 44 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_44_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0] }

theorem case_45_44_17_checked :
    (Witness.linear .positive case_45_44_17).check 45 44 17 = true := by
  change case_45_44_17.check 45 44 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_44_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0] }

theorem case_45_44_18_checked :
    (Witness.linear .positive case_45_44_18).check 45 44 18 = true := by
  change case_45_44_18.check 45 44 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_44_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0] }

theorem case_45_44_19_checked :
    (Witness.linear .positive case_45_44_19).check 45 44 19 = true := by
  change case_45_44_19.check 45 44 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_44_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0] }

theorem case_45_44_20_checked :
    (Witness.linear .positive case_45_44_20).check 45 44 20 = true := by
  change case_45_44_20.check 45 44 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_44_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0] }

theorem case_45_44_21_checked :
    (Witness.linear .positive case_45_44_21).check 45 44 21 = true := by
  change case_45_44_21.check 45 44 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_44_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0] }

theorem case_45_44_22_checked :
    (Witness.linear .positive case_45_44_22).check 45 44 22 = true := by
  change case_45_44_22.check 45 44 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_44_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_45_44_23_checked :
    (Witness.linear .negative case_45_44_23).check 45 44 23 = true := by
  change case_45_44_23.check 45 44 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_44_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_45_44_24_checked :
    (Witness.linear .negative case_45_44_24).check 45 44 24 = true := by
  change case_45_44_24.check 45 44 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_44_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_45_44_25_checked :
    (Witness.linear .negative case_45_44_25).check 45 44 25 = true := by
  change case_45_44_25.check 45 44 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_44_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_45_44_26_checked :
    (Witness.linear .negative case_45_44_26).check 45 44 26 = true := by
  change case_45_44_26.check 45 44 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_44_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_45_44_27_checked :
    (Witness.linear .negative case_45_44_27).check 45 44 27 = true := by
  change case_45_44_27.check 45 44 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_45_44_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_45_44_28_checked :
    (Witness.linear .negative case_45_44_28).check 45 44 28 = true := by
  change case_45_44_28.check 45 44 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_45 (a k : ℕ) (h : Domain 45 a k) :
    ∃ w : Witness, w.check 45 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 23 ≤ a := by omega
  have haHi : a ≤ 44 := by omega
  interval_cases a

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_45_23_1_checked⟩

    · exact ⟨Witness.rising, case_45_23_2_checked⟩

    · exact ⟨Witness.rising, case_45_23_3_checked⟩

    · exact ⟨Witness.rising, case_45_23_4_checked⟩

    · exact ⟨Witness.rising, case_45_23_5_checked⟩

    · exact ⟨Witness.rising, case_45_23_6_checked⟩

    · exact ⟨Witness.rising, case_45_23_7_checked⟩

    · exact ⟨Witness.rising, case_45_23_8_checked⟩

    · exact ⟨Witness.rising, case_45_23_9_checked⟩

    · exact ⟨Witness.linear .positive case_45_23_10, case_45_23_10_checked⟩

    · exact ⟨Witness.linear .positive case_45_23_11, case_45_23_11_checked⟩

    · exact ⟨Witness.linear .positive case_45_23_12, case_45_23_12_checked⟩

    · exact ⟨Witness.linear .conditional case_45_23_13, case_45_23_13_checked⟩

    · exact ⟨Witness.linear .conditional case_45_23_14, case_45_23_14_checked⟩

  · have hkHi : k ≤ 15 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_45_24_1_checked⟩

    · exact ⟨Witness.rising, case_45_24_2_checked⟩

    · exact ⟨Witness.rising, case_45_24_3_checked⟩

    · exact ⟨Witness.rising, case_45_24_4_checked⟩

    · exact ⟨Witness.rising, case_45_24_5_checked⟩

    · exact ⟨Witness.rising, case_45_24_6_checked⟩

    · exact ⟨Witness.rising, case_45_24_7_checked⟩

    · exact ⟨Witness.rising, case_45_24_8_checked⟩

    · exact ⟨Witness.rising, case_45_24_9_checked⟩

    · exact ⟨Witness.linear .positive case_45_24_10, case_45_24_10_checked⟩

    · exact ⟨Witness.linear .positive case_45_24_11, case_45_24_11_checked⟩

    · exact ⟨Witness.linear .positive case_45_24_12, case_45_24_12_checked⟩

    · exact ⟨Witness.linear .conditional case_45_24_13, case_45_24_13_checked⟩

    · exact ⟨Witness.linear .conditional case_45_24_14, case_45_24_14_checked⟩

    · exact ⟨Witness.linear .conditional case_45_24_15, case_45_24_15_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_45_25_1_checked⟩

    · exact ⟨Witness.rising, case_45_25_2_checked⟩

    · exact ⟨Witness.rising, case_45_25_3_checked⟩

    · exact ⟨Witness.rising, case_45_25_4_checked⟩

    · exact ⟨Witness.rising, case_45_25_5_checked⟩

    · exact ⟨Witness.rising, case_45_25_6_checked⟩

    · exact ⟨Witness.rising, case_45_25_7_checked⟩

    · exact ⟨Witness.rising, case_45_25_8_checked⟩

    · exact ⟨Witness.rising, case_45_25_9_checked⟩

    · exact ⟨Witness.linear .positive case_45_25_10, case_45_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_45_25_11, case_45_25_11_checked⟩

    · exact ⟨Witness.linear .positive case_45_25_12, case_45_25_12_checked⟩

    · exact ⟨Witness.linear .positive case_45_25_13, case_45_25_13_checked⟩

    · exact ⟨Witness.linear .conditional case_45_25_14, case_45_25_14_checked⟩

    · exact ⟨Witness.linear .conditional case_45_25_15, case_45_25_15_checked⟩

    · exact ⟨Witness.linear .negative case_45_25_16, case_45_25_16_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_45_26_1_checked⟩

    · exact ⟨Witness.rising, case_45_26_2_checked⟩

    · exact ⟨Witness.rising, case_45_26_3_checked⟩

    · exact ⟨Witness.rising, case_45_26_4_checked⟩

    · exact ⟨Witness.rising, case_45_26_5_checked⟩

    · exact ⟨Witness.rising, case_45_26_6_checked⟩

    · exact ⟨Witness.rising, case_45_26_7_checked⟩

    · exact ⟨Witness.rising, case_45_26_8_checked⟩

    · exact ⟨Witness.rising, case_45_26_9_checked⟩

    · exact ⟨Witness.linear .positive case_45_26_10, case_45_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_45_26_11, case_45_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_45_26_12, case_45_26_12_checked⟩

    · exact ⟨Witness.linear .positive case_45_26_13, case_45_26_13_checked⟩

    · exact ⟨Witness.linear .conditional case_45_26_14, case_45_26_14_checked⟩

    · exact ⟨Witness.linear .conditional case_45_26_15, case_45_26_15_checked⟩

    · exact ⟨Witness.linear .conditional case_45_26_16, case_45_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_45_27_1_checked⟩

    · exact ⟨Witness.rising, case_45_27_2_checked⟩

    · exact ⟨Witness.rising, case_45_27_3_checked⟩

    · exact ⟨Witness.rising, case_45_27_4_checked⟩

    · exact ⟨Witness.rising, case_45_27_5_checked⟩

    · exact ⟨Witness.rising, case_45_27_6_checked⟩

    · exact ⟨Witness.rising, case_45_27_7_checked⟩

    · exact ⟨Witness.rising, case_45_27_8_checked⟩

    · exact ⟨Witness.rising, case_45_27_9_checked⟩

    · exact ⟨Witness.linear .positive case_45_27_10, case_45_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_45_27_11, case_45_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_45_27_12, case_45_27_12_checked⟩

    · exact ⟨Witness.linear .positive case_45_27_13, case_45_27_13_checked⟩

    · exact ⟨Witness.linear .conditional case_45_27_14, case_45_27_14_checked⟩

    · exact ⟨Witness.linear .conditional case_45_27_15, case_45_27_15_checked⟩

    · exact ⟨Witness.linear .conditional case_45_27_16, case_45_27_16_checked⟩

    · exact ⟨Witness.linear .negative case_45_27_17, case_45_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_45_28_1_checked⟩

    · exact ⟨Witness.rising, case_45_28_2_checked⟩

    · exact ⟨Witness.rising, case_45_28_3_checked⟩

    · exact ⟨Witness.rising, case_45_28_4_checked⟩

    · exact ⟨Witness.rising, case_45_28_5_checked⟩

    · exact ⟨Witness.rising, case_45_28_6_checked⟩

    · exact ⟨Witness.rising, case_45_28_7_checked⟩

    · exact ⟨Witness.rising, case_45_28_8_checked⟩

    · exact ⟨Witness.linear .positive case_45_28_9, case_45_28_9_checked⟩

    · exact ⟨Witness.linear .positive case_45_28_10, case_45_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_45_28_11, case_45_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_45_28_12, case_45_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_45_28_13, case_45_28_13_checked⟩

    · exact ⟨Witness.linear .conditional case_45_28_14, case_45_28_14_checked⟩

    · exact ⟨Witness.linear .conditional case_45_28_15, case_45_28_15_checked⟩

    · exact ⟨Witness.linear .conditional case_45_28_16, case_45_28_16_checked⟩

    · exact ⟨Witness.linear .negative case_45_28_17, case_45_28_17_checked⟩

    · exact ⟨Witness.linear .negative case_45_28_18, case_45_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_45_29_1_checked⟩

    · exact ⟨Witness.rising, case_45_29_2_checked⟩

    · exact ⟨Witness.rising, case_45_29_3_checked⟩

    · exact ⟨Witness.rising, case_45_29_4_checked⟩

    · exact ⟨Witness.rising, case_45_29_5_checked⟩

    · exact ⟨Witness.rising, case_45_29_6_checked⟩

    · exact ⟨Witness.rising, case_45_29_7_checked⟩

    · exact ⟨Witness.rising, case_45_29_8_checked⟩

    · exact ⟨Witness.linear .positive case_45_29_9, case_45_29_9_checked⟩

    · exact ⟨Witness.linear .positive case_45_29_10, case_45_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_45_29_11, case_45_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_45_29_12, case_45_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_45_29_13, case_45_29_13_checked⟩

    · exact ⟨Witness.linear .positive case_45_29_14, case_45_29_14_checked⟩

    · exact ⟨Witness.linear .conditional case_45_29_15, case_45_29_15_checked⟩

    · exact ⟨Witness.linear .conditional case_45_29_16, case_45_29_16_checked⟩

    · exact ⟨Witness.linear .conditional case_45_29_17, case_45_29_17_checked⟩

    · exact ⟨Witness.linear .negative case_45_29_18, case_45_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_45_30_1_checked⟩

    · exact ⟨Witness.rising, case_45_30_2_checked⟩

    · exact ⟨Witness.rising, case_45_30_3_checked⟩

    · exact ⟨Witness.rising, case_45_30_4_checked⟩

    · exact ⟨Witness.rising, case_45_30_5_checked⟩

    · exact ⟨Witness.rising, case_45_30_6_checked⟩

    · exact ⟨Witness.rising, case_45_30_7_checked⟩

    · exact ⟨Witness.rising, case_45_30_8_checked⟩

    · exact ⟨Witness.linear .positive case_45_30_9, case_45_30_9_checked⟩

    · exact ⟨Witness.linear .positive case_45_30_10, case_45_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_45_30_11, case_45_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_45_30_12, case_45_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_45_30_13, case_45_30_13_checked⟩

    · exact ⟨Witness.linear .conditional case_45_30_14, case_45_30_14_checked⟩

    · exact ⟨Witness.linear .conditional case_45_30_15, case_45_30_15_checked⟩

    · exact ⟨Witness.linear .conditional case_45_30_16, case_45_30_16_checked⟩

    · exact ⟨Witness.linear .conditional case_45_30_17, case_45_30_17_checked⟩

    · exact ⟨Witness.linear .negative case_45_30_18, case_45_30_18_checked⟩

    · exact ⟨Witness.linear .negative case_45_30_19, case_45_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_45_31_1_checked⟩

    · exact ⟨Witness.rising, case_45_31_2_checked⟩

    · exact ⟨Witness.rising, case_45_31_3_checked⟩

    · exact ⟨Witness.rising, case_45_31_4_checked⟩

    · exact ⟨Witness.rising, case_45_31_5_checked⟩

    · exact ⟨Witness.rising, case_45_31_6_checked⟩

    · exact ⟨Witness.rising, case_45_31_7_checked⟩

    · exact ⟨Witness.rising, case_45_31_8_checked⟩

    · exact ⟨Witness.linear .positive case_45_31_9, case_45_31_9_checked⟩

    · exact ⟨Witness.linear .positive case_45_31_10, case_45_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_45_31_11, case_45_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_45_31_12, case_45_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_45_31_13, case_45_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_45_31_14, case_45_31_14_checked⟩

    · exact ⟨Witness.linear .conditional case_45_31_15, case_45_31_15_checked⟩

    · exact ⟨Witness.linear .conditional case_45_31_16, case_45_31_16_checked⟩

    · exact ⟨Witness.linear .conditional case_45_31_17, case_45_31_17_checked⟩

    · exact ⟨Witness.linear .negative case_45_31_18, case_45_31_18_checked⟩

    · exact ⟨Witness.linear .negative case_45_31_19, case_45_31_19_checked⟩

    · exact ⟨Witness.linear .negative case_45_31_20, case_45_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_45_32_1_checked⟩

    · exact ⟨Witness.rising, case_45_32_2_checked⟩

    · exact ⟨Witness.rising, case_45_32_3_checked⟩

    · exact ⟨Witness.rising, case_45_32_4_checked⟩

    · exact ⟨Witness.rising, case_45_32_5_checked⟩

    · exact ⟨Witness.rising, case_45_32_6_checked⟩

    · exact ⟨Witness.rising, case_45_32_7_checked⟩

    · exact ⟨Witness.rising, case_45_32_8_checked⟩

    · exact ⟨Witness.linear .positive case_45_32_9, case_45_32_9_checked⟩

    · exact ⟨Witness.linear .positive case_45_32_10, case_45_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_45_32_11, case_45_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_45_32_12, case_45_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_45_32_13, case_45_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_45_32_14, case_45_32_14_checked⟩

    · exact ⟨Witness.linear .positive case_45_32_15, case_45_32_15_checked⟩

    · exact ⟨Witness.linear .conditional case_45_32_16, case_45_32_16_checked⟩

    · exact ⟨Witness.linear .conditional case_45_32_17, case_45_32_17_checked⟩

    · exact ⟨Witness.linear .negative case_45_32_18, case_45_32_18_checked⟩

    · exact ⟨Witness.linear .conditional case_45_32_19, case_45_32_19_checked⟩

    · exact ⟨Witness.linear .negative case_45_32_20, case_45_32_20_checked⟩

  · have hkHi : k ≤ 21 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_45_33_1_checked⟩

    · exact ⟨Witness.rising, case_45_33_2_checked⟩

    · exact ⟨Witness.rising, case_45_33_3_checked⟩

    · exact ⟨Witness.rising, case_45_33_4_checked⟩

    · exact ⟨Witness.rising, case_45_33_5_checked⟩

    · exact ⟨Witness.rising, case_45_33_6_checked⟩

    · exact ⟨Witness.rising, case_45_33_7_checked⟩

    · exact ⟨Witness.rising, case_45_33_8_checked⟩

    · exact ⟨Witness.linear .positive case_45_33_9, case_45_33_9_checked⟩

    · exact ⟨Witness.linear .positive case_45_33_10, case_45_33_10_checked⟩

    · exact ⟨Witness.linear .positive case_45_33_11, case_45_33_11_checked⟩

    · exact ⟨Witness.linear .positive case_45_33_12, case_45_33_12_checked⟩

    · exact ⟨Witness.linear .positive case_45_33_13, case_45_33_13_checked⟩

    · exact ⟨Witness.linear .positive case_45_33_14, case_45_33_14_checked⟩

    · exact ⟨Witness.linear .positive case_45_33_15, case_45_33_15_checked⟩

    · exact ⟨Witness.linear .conditional case_45_33_16, case_45_33_16_checked⟩

    · exact ⟨Witness.linear .conditional case_45_33_17, case_45_33_17_checked⟩

    · exact ⟨Witness.linear .conditional case_45_33_18, case_45_33_18_checked⟩

    · exact ⟨Witness.linear .conditional case_45_33_19, case_45_33_19_checked⟩

    · exact ⟨Witness.linear .negative case_45_33_20, case_45_33_20_checked⟩

    · exact ⟨Witness.linear .negative case_45_33_21, case_45_33_21_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_45_34_1_checked⟩

    · exact ⟨Witness.rising, case_45_34_2_checked⟩

    · exact ⟨Witness.rising, case_45_34_3_checked⟩

    · exact ⟨Witness.rising, case_45_34_4_checked⟩

    · exact ⟨Witness.rising, case_45_34_5_checked⟩

    · exact ⟨Witness.rising, case_45_34_6_checked⟩

    · exact ⟨Witness.rising, case_45_34_7_checked⟩

    · exact ⟨Witness.rising, case_45_34_8_checked⟩

    · exact ⟨Witness.linear .positive case_45_34_9, case_45_34_9_checked⟩

    · exact ⟨Witness.linear .positive case_45_34_10, case_45_34_10_checked⟩

    · exact ⟨Witness.linear .positive case_45_34_11, case_45_34_11_checked⟩

    · exact ⟨Witness.linear .positive case_45_34_12, case_45_34_12_checked⟩

    · exact ⟨Witness.linear .positive case_45_34_13, case_45_34_13_checked⟩

    · exact ⟨Witness.linear .positive case_45_34_14, case_45_34_14_checked⟩

    · exact ⟨Witness.linear .positive case_45_34_15, case_45_34_15_checked⟩

    · exact ⟨Witness.linear .positive case_45_34_16, case_45_34_16_checked⟩

    · exact ⟨Witness.linear .conditional case_45_34_17, case_45_34_17_checked⟩

    · exact ⟨Witness.linear .conditional case_45_34_18, case_45_34_18_checked⟩

    · exact ⟨Witness.linear .conditional case_45_34_19, case_45_34_19_checked⟩

    · exact ⟨Witness.linear .negative case_45_34_20, case_45_34_20_checked⟩

    · exact ⟨Witness.linear .negative case_45_34_21, case_45_34_21_checked⟩

    · exact ⟨Witness.linear .negative case_45_34_22, case_45_34_22_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_45_35_1_checked⟩

    · exact ⟨Witness.rising, case_45_35_2_checked⟩

    · exact ⟨Witness.rising, case_45_35_3_checked⟩

    · exact ⟨Witness.rising, case_45_35_4_checked⟩

    · exact ⟨Witness.rising, case_45_35_5_checked⟩

    · exact ⟨Witness.rising, case_45_35_6_checked⟩

    · exact ⟨Witness.rising, case_45_35_7_checked⟩

    · exact ⟨Witness.rising, case_45_35_8_checked⟩

    · exact ⟨Witness.linear .positive case_45_35_9, case_45_35_9_checked⟩

    · exact ⟨Witness.linear .positive case_45_35_10, case_45_35_10_checked⟩

    · exact ⟨Witness.linear .positive case_45_35_11, case_45_35_11_checked⟩

    · exact ⟨Witness.linear .positive case_45_35_12, case_45_35_12_checked⟩

    · exact ⟨Witness.linear .positive case_45_35_13, case_45_35_13_checked⟩

    · exact ⟨Witness.linear .positive case_45_35_14, case_45_35_14_checked⟩

    · exact ⟨Witness.linear .positive case_45_35_15, case_45_35_15_checked⟩

    · exact ⟨Witness.linear .positive case_45_35_16, case_45_35_16_checked⟩

    · exact ⟨Witness.linear .positive case_45_35_17, case_45_35_17_checked⟩

    · exact ⟨Witness.linear .conditional case_45_35_18, case_45_35_18_checked⟩

    · exact ⟨Witness.linear .conditional case_45_35_19, case_45_35_19_checked⟩

    · exact ⟨Witness.linear .negative case_45_35_20, case_45_35_20_checked⟩

    · exact ⟨Witness.linear .negative case_45_35_21, case_45_35_21_checked⟩

    · exact ⟨Witness.linear .negative case_45_35_22, case_45_35_22_checked⟩

  · have hkHi : k ≤ 23 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_45_36_1_checked⟩

    · exact ⟨Witness.rising, case_45_36_2_checked⟩

    · exact ⟨Witness.rising, case_45_36_3_checked⟩

    · exact ⟨Witness.rising, case_45_36_4_checked⟩

    · exact ⟨Witness.rising, case_45_36_5_checked⟩

    · exact ⟨Witness.rising, case_45_36_6_checked⟩

    · exact ⟨Witness.rising, case_45_36_7_checked⟩

    · exact ⟨Witness.rising, case_45_36_8_checked⟩

    · exact ⟨Witness.linear .positive case_45_36_9, case_45_36_9_checked⟩

    · exact ⟨Witness.linear .positive case_45_36_10, case_45_36_10_checked⟩

    · exact ⟨Witness.linear .positive case_45_36_11, case_45_36_11_checked⟩

    · exact ⟨Witness.linear .positive case_45_36_12, case_45_36_12_checked⟩

    · exact ⟨Witness.linear .positive case_45_36_13, case_45_36_13_checked⟩

    · exact ⟨Witness.linear .positive case_45_36_14, case_45_36_14_checked⟩

    · exact ⟨Witness.linear .positive case_45_36_15, case_45_36_15_checked⟩

    · exact ⟨Witness.linear .positive case_45_36_16, case_45_36_16_checked⟩

    · exact ⟨Witness.linear .positive case_45_36_17, case_45_36_17_checked⟩

    · exact ⟨Witness.linear .conditional case_45_36_18, case_45_36_18_checked⟩

    · exact ⟨Witness.linear .conditional case_45_36_19, case_45_36_19_checked⟩

    · exact ⟨Witness.linear .negative case_45_36_20, case_45_36_20_checked⟩

    · exact ⟨Witness.linear .negative case_45_36_21, case_45_36_21_checked⟩

    · exact ⟨Witness.linear .negative case_45_36_22, case_45_36_22_checked⟩

    · exact ⟨Witness.linear .negative case_45_36_23, case_45_36_23_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_45_37_1_checked⟩

    · exact ⟨Witness.rising, case_45_37_2_checked⟩

    · exact ⟨Witness.rising, case_45_37_3_checked⟩

    · exact ⟨Witness.rising, case_45_37_4_checked⟩

    · exact ⟨Witness.rising, case_45_37_5_checked⟩

    · exact ⟨Witness.rising, case_45_37_6_checked⟩

    · exact ⟨Witness.rising, case_45_37_7_checked⟩

    · exact ⟨Witness.rising, case_45_37_8_checked⟩

    · exact ⟨Witness.linear .positive case_45_37_9, case_45_37_9_checked⟩

    · exact ⟨Witness.linear .positive case_45_37_10, case_45_37_10_checked⟩

    · exact ⟨Witness.linear .positive case_45_37_11, case_45_37_11_checked⟩

    · exact ⟨Witness.linear .positive case_45_37_12, case_45_37_12_checked⟩

    · exact ⟨Witness.linear .positive case_45_37_13, case_45_37_13_checked⟩

    · exact ⟨Witness.linear .positive case_45_37_14, case_45_37_14_checked⟩

    · exact ⟨Witness.linear .positive case_45_37_15, case_45_37_15_checked⟩

    · exact ⟨Witness.linear .positive case_45_37_16, case_45_37_16_checked⟩

    · exact ⟨Witness.linear .positive case_45_37_17, case_45_37_17_checked⟩

    · exact ⟨Witness.linear .positive case_45_37_18, case_45_37_18_checked⟩

    · exact ⟨Witness.linear .conditional case_45_37_19, case_45_37_19_checked⟩

    · exact ⟨Witness.linear .conditional case_45_37_20, case_45_37_20_checked⟩

    · exact ⟨Witness.linear .negative case_45_37_21, case_45_37_21_checked⟩

    · exact ⟨Witness.linear .negative case_45_37_22, case_45_37_22_checked⟩

    · exact ⟨Witness.linear .negative case_45_37_23, case_45_37_23_checked⟩

    · exact ⟨Witness.linear .negative case_45_37_24, case_45_37_24_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_45_38_1_checked⟩

    · exact ⟨Witness.rising, case_45_38_2_checked⟩

    · exact ⟨Witness.rising, case_45_38_3_checked⟩

    · exact ⟨Witness.rising, case_45_38_4_checked⟩

    · exact ⟨Witness.rising, case_45_38_5_checked⟩

    · exact ⟨Witness.rising, case_45_38_6_checked⟩

    · exact ⟨Witness.rising, case_45_38_7_checked⟩

    · exact ⟨Witness.rising, case_45_38_8_checked⟩

    · exact ⟨Witness.linear .positive case_45_38_9, case_45_38_9_checked⟩

    · exact ⟨Witness.linear .positive case_45_38_10, case_45_38_10_checked⟩

    · exact ⟨Witness.linear .positive case_45_38_11, case_45_38_11_checked⟩

    · exact ⟨Witness.linear .positive case_45_38_12, case_45_38_12_checked⟩

    · exact ⟨Witness.linear .positive case_45_38_13, case_45_38_13_checked⟩

    · exact ⟨Witness.linear .positive case_45_38_14, case_45_38_14_checked⟩

    · exact ⟨Witness.linear .positive case_45_38_15, case_45_38_15_checked⟩

    · exact ⟨Witness.linear .positive case_45_38_16, case_45_38_16_checked⟩

    · exact ⟨Witness.linear .positive case_45_38_17, case_45_38_17_checked⟩

    · exact ⟨Witness.linear .positive case_45_38_18, case_45_38_18_checked⟩

    · exact ⟨Witness.linear .conditional case_45_38_19, case_45_38_19_checked⟩

    · exact ⟨Witness.linear .conditional case_45_38_20, case_45_38_20_checked⟩

    · exact ⟨Witness.linear .negative case_45_38_21, case_45_38_21_checked⟩

    · exact ⟨Witness.linear .negative case_45_38_22, case_45_38_22_checked⟩

    · exact ⟨Witness.linear .negative case_45_38_23, case_45_38_23_checked⟩

    · exact ⟨Witness.linear .negative case_45_38_24, case_45_38_24_checked⟩

  · have hkHi : k ≤ 25 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_45_39_1_checked⟩

    · exact ⟨Witness.rising, case_45_39_2_checked⟩

    · exact ⟨Witness.rising, case_45_39_3_checked⟩

    · exact ⟨Witness.rising, case_45_39_4_checked⟩

    · exact ⟨Witness.rising, case_45_39_5_checked⟩

    · exact ⟨Witness.rising, case_45_39_6_checked⟩

    · exact ⟨Witness.rising, case_45_39_7_checked⟩

    · exact ⟨Witness.rising, case_45_39_8_checked⟩

    · exact ⟨Witness.linear .positive case_45_39_9, case_45_39_9_checked⟩

    · exact ⟨Witness.linear .positive case_45_39_10, case_45_39_10_checked⟩

    · exact ⟨Witness.linear .positive case_45_39_11, case_45_39_11_checked⟩

    · exact ⟨Witness.linear .positive case_45_39_12, case_45_39_12_checked⟩

    · exact ⟨Witness.linear .positive case_45_39_13, case_45_39_13_checked⟩

    · exact ⟨Witness.linear .positive case_45_39_14, case_45_39_14_checked⟩

    · exact ⟨Witness.linear .positive case_45_39_15, case_45_39_15_checked⟩

    · exact ⟨Witness.linear .positive case_45_39_16, case_45_39_16_checked⟩

    · exact ⟨Witness.linear .positive case_45_39_17, case_45_39_17_checked⟩

    · exact ⟨Witness.linear .positive case_45_39_18, case_45_39_18_checked⟩

    · exact ⟨Witness.linear .positive case_45_39_19, case_45_39_19_checked⟩

    · exact ⟨Witness.linear .conditional case_45_39_20, case_45_39_20_checked⟩

    · exact ⟨Witness.linear .negative case_45_39_21, case_45_39_21_checked⟩

    · exact ⟨Witness.linear .negative case_45_39_22, case_45_39_22_checked⟩

    · exact ⟨Witness.linear .negative case_45_39_23, case_45_39_23_checked⟩

    · exact ⟨Witness.linear .negative case_45_39_24, case_45_39_24_checked⟩

    · exact ⟨Witness.linear .negative case_45_39_25, case_45_39_25_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_45_40_1_checked⟩

    · exact ⟨Witness.rising, case_45_40_2_checked⟩

    · exact ⟨Witness.rising, case_45_40_3_checked⟩

    · exact ⟨Witness.rising, case_45_40_4_checked⟩

    · exact ⟨Witness.rising, case_45_40_5_checked⟩

    · exact ⟨Witness.rising, case_45_40_6_checked⟩

    · exact ⟨Witness.rising, case_45_40_7_checked⟩

    · exact ⟨Witness.rising, case_45_40_8_checked⟩

    · exact ⟨Witness.linear .positive case_45_40_9, case_45_40_9_checked⟩

    · exact ⟨Witness.linear .positive case_45_40_10, case_45_40_10_checked⟩

    · exact ⟨Witness.linear .positive case_45_40_11, case_45_40_11_checked⟩

    · exact ⟨Witness.linear .positive case_45_40_12, case_45_40_12_checked⟩

    · exact ⟨Witness.linear .positive case_45_40_13, case_45_40_13_checked⟩

    · exact ⟨Witness.linear .positive case_45_40_14, case_45_40_14_checked⟩

    · exact ⟨Witness.linear .positive case_45_40_15, case_45_40_15_checked⟩

    · exact ⟨Witness.linear .positive case_45_40_16, case_45_40_16_checked⟩

    · exact ⟨Witness.linear .positive case_45_40_17, case_45_40_17_checked⟩

    · exact ⟨Witness.linear .positive case_45_40_18, case_45_40_18_checked⟩

    · exact ⟨Witness.linear .positive case_45_40_19, case_45_40_19_checked⟩

    · exact ⟨Witness.linear .positive case_45_40_20, case_45_40_20_checked⟩

    · exact ⟨Witness.linear .negative case_45_40_21, case_45_40_21_checked⟩

    · exact ⟨Witness.linear .negative case_45_40_22, case_45_40_22_checked⟩

    · exact ⟨Witness.linear .negative case_45_40_23, case_45_40_23_checked⟩

    · exact ⟨Witness.linear .negative case_45_40_24, case_45_40_24_checked⟩

    · exact ⟨Witness.linear .negative case_45_40_25, case_45_40_25_checked⟩

    · exact ⟨Witness.linear .negative case_45_40_26, case_45_40_26_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_45_41_1_checked⟩

    · exact ⟨Witness.rising, case_45_41_2_checked⟩

    · exact ⟨Witness.rising, case_45_41_3_checked⟩

    · exact ⟨Witness.rising, case_45_41_4_checked⟩

    · exact ⟨Witness.rising, case_45_41_5_checked⟩

    · exact ⟨Witness.rising, case_45_41_6_checked⟩

    · exact ⟨Witness.rising, case_45_41_7_checked⟩

    · exact ⟨Witness.rising, case_45_41_8_checked⟩

    · exact ⟨Witness.linear .positive case_45_41_9, case_45_41_9_checked⟩

    · exact ⟨Witness.linear .positive case_45_41_10, case_45_41_10_checked⟩

    · exact ⟨Witness.linear .positive case_45_41_11, case_45_41_11_checked⟩

    · exact ⟨Witness.linear .positive case_45_41_12, case_45_41_12_checked⟩

    · exact ⟨Witness.linear .positive case_45_41_13, case_45_41_13_checked⟩

    · exact ⟨Witness.linear .positive case_45_41_14, case_45_41_14_checked⟩

    · exact ⟨Witness.linear .positive case_45_41_15, case_45_41_15_checked⟩

    · exact ⟨Witness.linear .positive case_45_41_16, case_45_41_16_checked⟩

    · exact ⟨Witness.linear .positive case_45_41_17, case_45_41_17_checked⟩

    · exact ⟨Witness.linear .positive case_45_41_18, case_45_41_18_checked⟩

    · exact ⟨Witness.linear .positive case_45_41_19, case_45_41_19_checked⟩

    · exact ⟨Witness.linear .positive case_45_41_20, case_45_41_20_checked⟩

    · exact ⟨Witness.linear .negative case_45_41_21, case_45_41_21_checked⟩

    · exact ⟨Witness.linear .negative case_45_41_22, case_45_41_22_checked⟩

    · exact ⟨Witness.linear .negative case_45_41_23, case_45_41_23_checked⟩

    · exact ⟨Witness.linear .negative case_45_41_24, case_45_41_24_checked⟩

    · exact ⟨Witness.linear .negative case_45_41_25, case_45_41_25_checked⟩

    · exact ⟨Witness.linear .negative case_45_41_26, case_45_41_26_checked⟩

  · have hkHi : k ≤ 27 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_45_42_1_checked⟩

    · exact ⟨Witness.rising, case_45_42_2_checked⟩

    · exact ⟨Witness.rising, case_45_42_3_checked⟩

    · exact ⟨Witness.rising, case_45_42_4_checked⟩

    · exact ⟨Witness.rising, case_45_42_5_checked⟩

    · exact ⟨Witness.rising, case_45_42_6_checked⟩

    · exact ⟨Witness.rising, case_45_42_7_checked⟩

    · exact ⟨Witness.rising, case_45_42_8_checked⟩

    · exact ⟨Witness.linear .positive case_45_42_9, case_45_42_9_checked⟩

    · exact ⟨Witness.linear .positive case_45_42_10, case_45_42_10_checked⟩

    · exact ⟨Witness.linear .positive case_45_42_11, case_45_42_11_checked⟩

    · exact ⟨Witness.linear .positive case_45_42_12, case_45_42_12_checked⟩

    · exact ⟨Witness.linear .positive case_45_42_13, case_45_42_13_checked⟩

    · exact ⟨Witness.linear .positive case_45_42_14, case_45_42_14_checked⟩

    · exact ⟨Witness.linear .positive case_45_42_15, case_45_42_15_checked⟩

    · exact ⟨Witness.linear .positive case_45_42_16, case_45_42_16_checked⟩

    · exact ⟨Witness.linear .positive case_45_42_17, case_45_42_17_checked⟩

    · exact ⟨Witness.linear .positive case_45_42_18, case_45_42_18_checked⟩

    · exact ⟨Witness.linear .positive case_45_42_19, case_45_42_19_checked⟩

    · exact ⟨Witness.linear .positive case_45_42_20, case_45_42_20_checked⟩

    · exact ⟨Witness.linear .positive case_45_42_21, case_45_42_21_checked⟩

    · exact ⟨Witness.linear .negative case_45_42_22, case_45_42_22_checked⟩

    · exact ⟨Witness.linear .negative case_45_42_23, case_45_42_23_checked⟩

    · exact ⟨Witness.linear .negative case_45_42_24, case_45_42_24_checked⟩

    · exact ⟨Witness.linear .negative case_45_42_25, case_45_42_25_checked⟩

    · exact ⟨Witness.linear .negative case_45_42_26, case_45_42_26_checked⟩

    · exact ⟨Witness.linear .negative case_45_42_27, case_45_42_27_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_45_43_1_checked⟩

    · exact ⟨Witness.rising, case_45_43_2_checked⟩

    · exact ⟨Witness.rising, case_45_43_3_checked⟩

    · exact ⟨Witness.rising, case_45_43_4_checked⟩

    · exact ⟨Witness.rising, case_45_43_5_checked⟩

    · exact ⟨Witness.rising, case_45_43_6_checked⟩

    · exact ⟨Witness.rising, case_45_43_7_checked⟩

    · exact ⟨Witness.rising, case_45_43_8_checked⟩

    · exact ⟨Witness.linear .positive case_45_43_9, case_45_43_9_checked⟩

    · exact ⟨Witness.linear .positive case_45_43_10, case_45_43_10_checked⟩

    · exact ⟨Witness.linear .positive case_45_43_11, case_45_43_11_checked⟩

    · exact ⟨Witness.linear .positive case_45_43_12, case_45_43_12_checked⟩

    · exact ⟨Witness.linear .positive case_45_43_13, case_45_43_13_checked⟩

    · exact ⟨Witness.linear .positive case_45_43_14, case_45_43_14_checked⟩

    · exact ⟨Witness.linear .positive case_45_43_15, case_45_43_15_checked⟩

    · exact ⟨Witness.linear .positive case_45_43_16, case_45_43_16_checked⟩

    · exact ⟨Witness.linear .positive case_45_43_17, case_45_43_17_checked⟩

    · exact ⟨Witness.linear .positive case_45_43_18, case_45_43_18_checked⟩

    · exact ⟨Witness.linear .positive case_45_43_19, case_45_43_19_checked⟩

    · exact ⟨Witness.linear .positive case_45_43_20, case_45_43_20_checked⟩

    · exact ⟨Witness.linear .positive case_45_43_21, case_45_43_21_checked⟩

    · exact ⟨Witness.linear .negative case_45_43_22, case_45_43_22_checked⟩

    · exact ⟨Witness.linear .negative case_45_43_23, case_45_43_23_checked⟩

    · exact ⟨Witness.linear .negative case_45_43_24, case_45_43_24_checked⟩

    · exact ⟨Witness.linear .negative case_45_43_25, case_45_43_25_checked⟩

    · exact ⟨Witness.linear .negative case_45_43_26, case_45_43_26_checked⟩

    · exact ⟨Witness.linear .negative case_45_43_27, case_45_43_27_checked⟩

    · exact ⟨Witness.linear .negative case_45_43_28, case_45_43_28_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_45_44_1_checked⟩

    · exact ⟨Witness.rising, case_45_44_2_checked⟩

    · exact ⟨Witness.rising, case_45_44_3_checked⟩

    · exact ⟨Witness.rising, case_45_44_4_checked⟩

    · exact ⟨Witness.rising, case_45_44_5_checked⟩

    · exact ⟨Witness.rising, case_45_44_6_checked⟩

    · exact ⟨Witness.rising, case_45_44_7_checked⟩

    · exact ⟨Witness.rising, case_45_44_8_checked⟩

    · exact ⟨Witness.linear .positive case_45_44_9, case_45_44_9_checked⟩

    · exact ⟨Witness.linear .positive case_45_44_10, case_45_44_10_checked⟩

    · exact ⟨Witness.linear .positive case_45_44_11, case_45_44_11_checked⟩

    · exact ⟨Witness.linear .positive case_45_44_12, case_45_44_12_checked⟩

    · exact ⟨Witness.linear .positive case_45_44_13, case_45_44_13_checked⟩

    · exact ⟨Witness.linear .positive case_45_44_14, case_45_44_14_checked⟩

    · exact ⟨Witness.linear .positive case_45_44_15, case_45_44_15_checked⟩

    · exact ⟨Witness.linear .positive case_45_44_16, case_45_44_16_checked⟩

    · exact ⟨Witness.linear .positive case_45_44_17, case_45_44_17_checked⟩

    · exact ⟨Witness.linear .positive case_45_44_18, case_45_44_18_checked⟩

    · exact ⟨Witness.linear .positive case_45_44_19, case_45_44_19_checked⟩

    · exact ⟨Witness.linear .positive case_45_44_20, case_45_44_20_checked⟩

    · exact ⟨Witness.linear .positive case_45_44_21, case_45_44_21_checked⟩

    · exact ⟨Witness.linear .positive case_45_44_22, case_45_44_22_checked⟩

    · exact ⟨Witness.linear .negative case_45_44_23, case_45_44_23_checked⟩

    · exact ⟨Witness.linear .negative case_45_44_24, case_45_44_24_checked⟩

    · exact ⟨Witness.linear .negative case_45_44_25, case_45_44_25_checked⟩

    · exact ⟨Witness.linear .negative case_45_44_26, case_45_44_26_checked⟩

    · exact ⟨Witness.linear .negative case_45_44_27, case_45_44_27_checked⟩

    · exact ⟨Witness.linear .negative case_45_44_28, case_45_44_28_checked⟩


#print axioms coverage_45
end ForestUnimodality.FiniteRows.FiniteData
