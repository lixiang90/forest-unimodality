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

theorem case_53_27_1_checked :
    (Witness.rising).check 53 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_27_2_checked :
    (Witness.rising).check 53 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_27_3_checked :
    (Witness.rising).check 53 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_27_4_checked :
    (Witness.rising).check 53 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_27_5_checked :
    (Witness.rising).check 53 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_27_6_checked :
    (Witness.rising).check 53 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_27_7_checked :
    (Witness.rising).check 53 27 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_27_8_checked :
    (Witness.rising).check 53 27 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_27_9_checked :
    (Witness.rising).check 53 27 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_27_10_checked :
    (Witness.rising).check 53 27 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_27_11 : Certificate := {
  objectiveScale := 8660805164440000000
  eta := 4703813624728605723336000
  rows := #[⟨.count 2, 1135084205836148790942720⟩, ⟨.count 3, 195533236156751174682000⟩, ⟨.count 4, 25729443836719346243520⟩, ⟨.count 5, 3896949203591656212000⟩, ⟨.count 6, 673024587116707425600⟩, ⟨.count 7, 134107302201813420480⟩, ⟨.count 8, 32816414346034999680⟩, ⟨.count 9, 11274913308833254080⟩, ⟨.count 10, 8681305799723356800⟩, ⟨.count 12, 1245578658221177280⟩, ⟨.path 11, 2654456132424096000⟩, ⟨.path 12, 1235532633689554200⟩, ⟨.privateRow 8 8, 330379404205310460⟩, ⟨.privateRow 8 9, 29166442410137760⟩, ⟨.privateRow 9 5, 226982381749643520⟩, ⟨.privateRow 9 6, 65027990037743040⟩, ⟨.privateRow 10 2, 120985589367262620⟩, ⟨.privateRow 11 0, 74934544946461200⟩, ⟨.hall 9 3, 4029108454322952⟩, ⟨.hall 9 4, 1739599136146872⟩, ⟨.hall 8 5, 4626317894278080⟩, ⟨.hall 7 7, 3003252737989581⟩, ⟨.hall 6 10, 1243115897173200⟩, ⟨.hall 6 11, 1101489822429480⟩, ⟨.hall 5 16, 38427575684425200⟩, ⟨.hall 10 16, 44405656264569600⟩, ⟨.hall 4 22, 788817485621846640960⟩]
  caps := #[0, 0, 64877909419921449280, 0, 0, 324297774345545000, 130655221952018400, 0, 107756941519492356, 41179368186896940, 0, 12571467268388600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_27_11_checked :
    (Witness.linear .positive case_53_27_11).check 53 27 11 = true := by
  change case_53_27_11.check 53 27 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_27_12 : Certificate := {
  objectiveScale := 611911872000000
  eta := 540277145412260256000
  rows := #[⟨.count 2, 147749260173965049600⟩, ⟨.count 3, 30450313943813443680⟩, ⟨.count 4, 4499912574625628160⟩, ⟨.count 5, 750324394626206400⟩, ⟨.count 6, 134271852668553600⟩, ⟨.count 7, 27674113683696480⟩, ⟨.count 8, 6483671336862720⟩, ⟨.count 9, 1789126288709760⟩, ⟨.count 10, 719608361472000⟩, ⟨.count 11, 612229301283600⟩, ⟨.path 12, 111543885367200⟩, ⟨.path 13, 119638459580640⟩, ⟨.privateRow 8 10, 59255251014960⟩, ⟨.privateRow 9 7, 15858036113920⟩, ⟨.privateRow 10 4, 4112047779840⟩, ⟨.privateRow 10 5, 42207798124800⟩, ⟨.privateRow 10 6, 37029846934080⟩, ⟨.privateRow 11 2, 17015739380640⟩, ⟨.privateRow 11 3, 80313433200⟩, ⟨.privateRow 12 0, 16104516553125⟩, ⟨.privateRow 13 0, 7986367797408⟩, ⟨.privateRow 14 0, 7370478498240⟩, ⟨.privateRow 15 0, 6025566808800⟩, ⟨.privateRow 16 0, 7964415459000⟩, ⟨.privateRow 17 0, 12184277938560⟩, ⟨.privateRow 18 0, 21748163813376⟩, ⟨.privateRow 19 0, 45025495394880⟩, ⟨.privateRow 20 0, 107656141532940⟩, ⟨.privateRow 21 0, 291530113617600⟩, ⟨.hall 10 3, 1240606326960⟩, ⟨.hall 21 4, 3123325166401440⟩, ⟨.hall 22 4, 68393557597292928⟩, ⟨.hall 9 5, 470897565600⟩, ⟨.hall 8 6, 695572859520⟩, ⟨.hall 20 6, 2697888848054400⟩, ⟨.hall 8 7, 7435224720⟩, ⟨.hall 19 7, 789910725223620⟩, ⟨.hall 7 8, 175769723976⟩, ⟨.hall 18 8, 288842800646400⟩, ⟨.hall 7 9, 244731318300⟩, ⟨.hall 17 9, 128450092522752⟩, ⟨.hall 16 10, 67872152275200⟩, ⟨.hall 15 11, 42773595965100⟩, ⟨.hall 14 12, 31586655481920⟩, ⟨.hall 6 13, 973067358120⟩, ⟨.hall 6 14, 65015636400⟩, ⟨.hall 11 15, 4638100767300⟩, ⟨.hall 5 21, 119023120770372000⟩, ⟨.hall 4 22, 89347942980616320⟩]
  caps := #[0, 0, 65006274148358400, 1625156853708960, 0, 57360751905600, 0, 0, 0, 9031318250240, 4151706683520, 0, 2130721756878, 0, 1817378259840, 198209434500, 0, 4497552259200, 0, 0, 151756247703060, 39529506931200, 0, 0, 0, 0, 0] }

theorem case_53_27_12_checked :
    (Witness.linear .positive case_53_27_12).check 53 27 12 = true := by
  change case_53_27_12.check 53 27 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_27_13 : Certificate := {
  objectiveScale := 104110006000000
  eta := 115773674016912912000
  rows := #[⟨.count 2, 34009282441370396160⟩, ⟨.count 3, 7411965373569556800⟩, ⟨.count 4, 1273057653096028800⟩, ⟨.count 5, 236307392434713600⟩, ⟨.count 6, 47662702982294400⟩, ⟨.count 7, 10653202117958400⟩, ⟨.count 8, 2640363012967680⟩, ⟨.count 9, 718708851020160⟩, ⟨.count 10, 242867821996800⟩, ⟨.count 11, 105130284058800⟩, ⟨.count 12, 103893457187520⟩, ⟨.path 13, 1451590940800⟩, ⟨.path 14, 29094790496772⟩, ⟨.privateRow 8 12, 145111649662980⟩, ⟨.privateRow 8 13, 2366569164960⟩, ⟨.privateRow 9 9, 25599401155328⟩, ⟨.privateRow 9 10, 36246939688960⟩, ⟨.privateRow 10 6, 2423680939680⟩, ⟨.privateRow 10 7, 20661482499840⟩, ⟨.privateRow 10 8, 4437584895744⟩, ⟨.privateRow 11 4, 5549864166000⟩, ⟨.privateRow 11 5, 11478128161500⟩, ⟨.privateRow 11 6, 4207937151600⟩, ⟨.privateRow 12 2, 4446687084840⟩, ⟨.privateRow 13 0, 3667289834208⟩, ⟨.privateRow 14 0, 2078205695280⟩, ⟨.privateRow 15 0, 2251659175920⟩, ⟨.privateRow 16 0, 1842747106200⟩, ⟨.privateRow 16 3, 583016033600⟩, ⟨.privateRow 17 0, 3679815484800⟩, ⟨.privateRow 18 0, 5833491856192⟩, ⟨.privateRow 18 4, 283179216320⟩, ⟨.privateRow 19 0, 14442140032320⟩, ⟨.privateRow 20 0, 37182442457160⟩, ⟨.privateRow 21 0, 112000269638400⟩, ⟨.privateRow 22 0, 395459775590880⟩, ⟨.privateRow 23 0, 1438182285924384⟩, ⟨.hall 11 3, 293066806725⟩, ⟨.hall 17 3, 103158143088⟩, ⟨.hall 23 3, 104135050703043360⟩, ⟨.hall 22 4, 12144650414472576⟩, ⟨.hall 10 5, 124770492000⟩, ⟨.hall 15 5, 18962893950⟩, ⟨.hall 21 5, 2098357992931200⟩, ⟨.hall 9 6, 193621729840⟩, ⟨.hall 20 6, 484236459907200⟩, ⟨.hall 19 7, 145270937972160⟩, ⟨.hall 8 8, 159672638720⟩, ⟨.hall 18 8, 53237692668160⟩, ⟨.hall 17 9, 21408348753792⟩, ⟨.hall 16 10, 12538630540800⟩, ⟨.hall 7 11, 217317624832⟩, ⟨.hall 12 14, 879521330688⟩, ⟨.hall 6 15, 346962530200⟩, ⟨.hall 6 16, 5692820115840⟩, ⟨.hall 5 21, 46211565798871200⟩, ⟨.hall 4 22, 36174568930980480⟩]
  caps := #[0, 0, 13360506674955440, 0, 481296452829192, 92291140661720, 53114031614280, 12091496266080, 20141627437932, 2228783023376, 253344263172, 1516130579320, 960875863948, 354271477560, 41979704052, 0, 1155621066600, 0, 1019445178752, 23220695738240, 0, 60941323185600, 0, 3462290688336480, 0, 0, 0] }

theorem case_53_27_13_checked :
    (Witness.linear .positive case_53_27_13).check 53 27 13 = true := by
  change case_53_27_13.check 53 27 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_27_14 : Certificate := {
  objectiveScale := 93699005400000
  eta := 145176511862478096000
  rows := #[⟨.count 2, 48367668255954727680⟩, ⟨.count 3, 12532959631672159680⟩, ⟨.count 4, 2430528063212208960⟩, ⟨.count 5, 495373898485065600⟩, ⟨.count 6, 112377447017035200⟩, ⟨.count 7, 26366675241947040⟩, ⟨.count 8, 6621296435994240⟩, ⟨.count 9, 1835001321753600⟩, ⟨.count 10, 575686689177600⟩, ⟨.count 11, 204076433761200⟩, ⟨.count 12, 93998842217280⟩, ⟨.count 13, 94175531770320⟩, ⟨.path 15, 16394442898680⟩, ⟨.path 16, 7338111580800⟩, ⟨.privateRow 9 11, 129023530435800⟩, ⟨.privateRow 9 12, 236171466410880⟩, ⟨.privateRow 9 13, 49131594031520⟩, ⟨.privateRow 10 8, 9399884221728⟩, ⟨.privateRow 10 9, 56869049677440⟩, ⟨.privateRow 10 10, 15910091116920⟩, ⟨.privateRow 11 6, 11601640486800⟩, ⟨.privateRow 11 7, 29374638192900⟩, ⟨.privateRow 11 8, 49722938865600⟩, ⟨.privateRow 12 4, 8193978022230⟩, ⟨.privateRow 12 5, 11318839852320⟩, ⟨.privateRow 13 2, 992179797840⟩, ⟨.privateRow 14 0, 4492962920160⟩, ⟨.privateRow 15 0, 1268540380800⟩, ⟨.privateRow 16 0, 866715799950⟩, ⟨.privateRow 16 3, 93699005400⟩, ⟨.privateRow 17 0, 1431039355200⟩, ⟨.privateRow 18 0, 1953936592608⟩, ⟨.privateRow 19 0, 4247688244800⟩, ⟨.privateRow 20 0, 11025026542530⟩, ⟨.privateRow 21 0, 32117724381600⟩, ⟨.privateRow 22 0, 121059114976800⟩, ⟨.privateRow 23 0, 399495079423440⟩, ⟨.hall 12 3, 748891874808⟩, ⟨.hall 23 3, 29862257186902140⟩, ⟨.hall 22 4, 3515556698926272⟩, ⟨.hall 11 5, 299759592825⟩, ⟨.hall 21 5, 605295574884000⟩, ⟨.hall 20 6, 148235650992000⟩, ⟨.hall 10 7, 234844936200⟩, ⟨.hall 19 7, 40857451304670⟩, ⟨.hall 9 8, 351224933808⟩, ⟨.hall 18 8, 15291677681280⟩, ⟨.hall 17 9, 6881254956576⟩, ⟨.hall 8 11, 567707226240⟩, ⟨.hall 13 12, 365999788440⟩, ⟨.hall 7 13, 573638696631⟩, ⟨.hall 7 14, 2083085055051⟩, ⟨.hall 12 14, 2803474241568⟩, ⟨.hall 6 20, 62189796779510400⟩, ⟨.hall 5 21, 71545936951288800⟩, ⟨.hall 4 22, 42242262311208960⟩]
  caps := #[0, 242532379557468000, 0, 0, 1352676321556560, 0, 0, 0, 6914789337456, 0, 1682571122232, 1017942689400, 0, 0, 1091795086800, 0, 23200591050, 0, 1868982827712, 7645838840640, 14916212381070, 195176940472800, 0, 1498106547837900, 0, 0, 0] }

theorem case_53_27_14_checked :
    (Witness.linear .positive case_53_27_14).check 53 27 14 = true := by
  change case_53_27_14.check 53 27 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_27_15 : Certificate := {
  objectiveScale := 19220308800000
  eta := 58193116569347760000
  rows := #[⟨.count 2, 19626394261914760320⟩, ⟨.count 3, 4747333193815212000⟩, ⟨.count 4, 1105802379844081920⟩, ⟨.count 5, 252045077381697600⟩, ⟨.count 6, 65337333768907200⟩, ⟨.count 7, 17105652946221840⟩, ⟨.count 8, 4582406078490240⟩, ⟨.count 9, 1422126024359040⟩, ⟨.count 10, 476740539475200⟩, ⟨.count 11, 177278518216800⟩, ⟨.count 12, 79156919761920⟩, ⟨.count 13, 58189759467840⟩, ⟨.count 14, 39578459880960⟩, ⟨.path 16, 7606184308800⟩, ⟨.privateRow 9 12, 152916776812800⟩, ⟨.privateRow 10 9, 8212197273280⟩, ⟨.privateRow 10 10, 58636837579320⟩, ⟨.privateRow 10 11, 17390535402240⟩, ⟨.privateRow 11 7, 5472021915360⟩, ⟨.privateRow 11 8, 27172711566000⟩, ⟨.privateRow 12 5, 3716727214200⟩, ⟨.privateRow 12 6, 14450260612788⟩, ⟨.privateRow 12 7, 15964228320040⟩, ⟨.privateRow 13 3, 1894504652040⟩, ⟨.privateRow 13 4, 3474894543120⟩, ⟨.privateRow 14 0, 689930635680⟩, ⟨.privateRow 15 0, 2975784309960⟩, ⟨.privateRow 16 0, 2233159628700⟩, ⟨.privateRow 17 0, 3352720775040⟩, ⟨.privateRow 18 0, 5380405110080⟩, ⟨.privateRow 18 6, 1274306473440⟩, ⟨.privateRow 19 0, 11043989436480⟩, ⟨.privateRow 20 0, 34804495555830⟩, ⟨.privateRow 20 3, 3458831856480⟩, ⟨.privateRow 20 7, 15564743354160⟩, ⟨.privateRow 21 0, 123529709160000⟩, ⟨.hall 13 2, 853298357340⟩, ⟨.hall 18 2, 930445996480⟩, ⟨.hall 13 3, 156419972280⟩, ⟨.hall 17 3, 54613134576⟩, ⟨.hall 21 3, 262294749116400⟩, ⟨.hall 12 4, 393686839392⟩, ⟨.hall 22 4, 11505458287395072⟩, ⟨.hall 11 6, 228970509075⟩, ⟨.hall 10 7, 310667512680⟩, ⟨.hall 10 8, 8455565440⟩, ⟨.hall 9 9, 354882616816⟩, ⟨.hall 8 11, 266850383800⟩, ⟨.hall 8 12, 509294829120⟩, ⟨.hall 14 12, 634270190400⟩, ⟨.hall 7 15, 8486475084087⟩, ⟨.hall 6 18, 268055134501440⟩, ⟨.hall 7 19, 829860233165964⟩, ⟨.hall 5 21, 60672627351554400⟩, ⟨.hall 4 22, 46225633537923840⟩, ⟨.assumptionRow 15, 49235046500640⟩]
  caps := #[0, 25401175703904000, 0, 0, 61166710725120, 21238441224000, 57261044131200, 7251410646480, 3568058125632, 3353438088000, 1424992008440, 0, 856891103068, 14385296640, 378674147280, 108620034600, 356524083300, 2671273463040, 444995911360, 0, 0, 49411883664000, 0, 0, 0, 0, 0] }

theorem case_53_27_15_checked :
    (Witness.linear .conditional case_53_27_15).check 53 27 15 = true := by
  change case_53_27_15.check 53 27 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_27_16 : Certificate := {
  objectiveScale := 42397740000000
  eta := 42266579402999952000
  rows := #[⟨.count 2, 12300187165394768640⟩, ⟨.count 3, 3087297973784344320⟩, ⟨.count 4, 854386809860263680⟩, ⟨.count 5, 241876111723646400⟩, ⟨.count 6, 70421816597932800⟩, ⟨.count 7, 21257980589926080⟩, ⟨.count 8, 6697754824400640⟩, ⟨.count 9, 2237682167360640⟩, ⟨.count 10, 791569197619200⟩, ⟨.count 11, 305083961582400⟩, ⟨.count 12, 123682687128000⟩, ⟨.count 13, 62783687846880⟩, ⟨.count 14, 49473074851200⟩, ⟨.count 15, 43288940494800⟩, ⟨.path 14, 5811212314908⟩, ⟨.privateRow 4 23, 94280838743931840⟩, ⟨.privateRow 11 8, 11910184686400⟩, ⟨.privateRow 11 9, 15062115118050⟩, ⟨.privateRow 13 4, 578256719040⟩, ⟨.privateRow 13 5, 7644767994864⟩, ⟨.privateRow 14 3, 6050278634400⟩, ⟨.privateRow 14 4, 4240549272960⟩, ⟨.privateRow 15 1, 2656887353120⟩, ⟨.privateRow 16 0, 4466319257400⟩, ⟨.privateRow 17 0, 3843362839680⟩, ⟨.privateRow 18 0, 6852937034944⟩, ⟨.privateRow 19 0, 12318295909920⟩, ⟨.privateRow 20 0, 35020672546860⟩, ⟨.privateRow 21 0, 121882646371200⟩, ⟨.privateRow 22 0, 443883421581600⟩, ⟨.privateRow 23 0, 2663300529489600⟩, ⟨.privateRow 24 0, 18376773653478240⟩, ⟨.privateRow 24 1, 3403106232125600⟩, ⟨.privateRow 25 0, 253191103670144640⟩, ⟨.privateRow 26 0, 6431870778717384000⟩, ⟨.hall 14 2, 961015440000⟩, ⟨.hall 14 3, 294647333904⟩, ⟨.hall 21 3, 60529557488400⟩, ⟨.hall 13 4, 658570152240⟩, ⟨.hall 18 4, 242725042560⟩, ⟨.hall 22 4, 2556768508310016⟩, ⟨.hall 12 5, 850196630976⟩, ⟨.hall 19 5, 1873533922260⟩, ⟨.hall 21 5, 161412153302400⟩, ⟨.hall 11 6, 686602629405⟩, ⟨.hall 18 6, 323633390080⟩, ⟨.hall 20 6, 118588520793600⟩, ⟨.hall 11 7, 202273728965⟩, ⟨.hall 19 7, 12105911497680⟩, ⟨.hall 10 8, 844076477440⟩, ⟨.hall 9 9, 152376278432⟩, ⟨.hall 9 10, 996121625240⟩, ⟨.hall 15 11, 858907549500⟩, ⟨.hall 8 12, 1178999754240⟩, ⟨.hall 8 13, 2495509016000⟩, ⟨.hall 7 15, 18838809695706⟩, ⟨.hall 5 20, 6690219315124800⟩, ⟨.hall 6 20, 109523087204044800⟩, ⟨.hall 4 22, 135666213058696320⟩, ⟨.assumptionRow 16, 43702369337088⟩]
  caps := #[0, 220226469291148320, 0, 1727940838183560, 826987133355768, 15074295988752, 31491091856952, 67820232480, 283545969168, 1808914394896, 0, 1814833376356, 0, 0, 543190557756, 539201266912, 0, 1947027559680, 4360959931328, 0, 11879440364220, 32941255776000, 0, 0, 10889939942801920, 0, 0] }

theorem case_53_27_16_checked :
    (Witness.linear .conditional case_53_27_16).check 53 27 16 = true := by
  change case_53_27_16.check 53 27 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_27_17 : Certificate := {
  objectiveScale := 60063465000000
  eta := 16539096288130416000
  rows := #[⟨.count 2, 4900472974260864000⟩, ⟨.count 3, 1543648986892172160⟩, ⟨.count 4, 493243258061473920⟩, ⟨.count 5, 160766504689190400⟩, ⟨.count 6, 53196833952662400⟩, ⟨.count 7, 17844113547580320⟩, ⟨.count 8, 6055504361786880⟩, ⟨.count 9, 2069473712866560⟩, ⟨.count 10, 863530033766400⟩, ⟨.count 11, 358679792671200⟩, ⟨.count 12, 143471917068480⟩, ⟨.count 13, 71971544604960⟩, ⟨.count 14, 42876664871040⟩, ⟨.count 15, 37104806138400⟩, ⟨.count 16, 35980418073600⟩, ⟨.count 18, 61166710725120⟩, ⟨.path 14, 5715014669364⟩, ⟨.privateRow 2 25, 24502364871304320⟩, ⟨.privateRow 3 24, 230730602538115680⟩, ⟨.privateRow 13 5, 1071916621776⟩, ⟨.privateRow 13 6, 1622926264960⟩, ⟨.privateRow 14 4, 7727223119616⟩, ⟨.privateRow 14 5, 11766215420960⟩, ⟨.privateRow 17 0, 2862078710400⟩, ⟨.hall 15 2, 2814093462180⟩, ⟨.hall 14 3, 2361791545344⟩, ⟨.hall 14 4, 136336057088⟩, ⟨.hall 13 5, 1320114876080⟩, ⟨.hall 12 6, 1608282220160⟩, ⟨.hall 11 7, 1041080038845⟩, ⟨.hall 11 8, 691690862940⟩, ⟨.hall 10 9, 1976937238080⟩, ⟨.hall 10 10, 67483987200⟩, ⟨.hall 16 10, 817736774400⟩, ⟨.hall 9 11, 3495167392640⟩, ⟨.hall 15 11, 5668789826700⟩, ⟨.hall 9 12, 131155726240⟩, ⟨.hall 14 12, 24355975311360⟩, ⟨.hall 8 13, 7644962124800⟩, ⟨.hall 7 16, 29234089684800⟩, ⟨.hall 8 18, 11964530547889920⟩, ⟨.hall 7 19, 97760077708365072⟩, ⟨.hall 6 20, 189425397214310400⟩, ⟨.hall 5 21, 259462699517548800⟩, ⟨.hall 4 22, 313945234589226240⟩, ⟨.hall 3 23, 303216765282390960⟩, ⟨.assumptionRow 17, 36446369236200⟩]
  caps := #[0, 140159750926595400, 29067790767985200, 0, 961021302194184, 0, 17792021443560, 0, 12525683041872, 1999010101088, 1969761313520, 583820412945, 0, 197283144828, 1124543792372, 0, 465951162600, 807831120600, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_27_17_checked :
    (Witness.linear .conditional case_53_27_17).check 53 27 17 = true := by
  change case_53_27_17.check 53 27 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_28_1_checked :
    (Witness.rising).check 53 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_28_2_checked :
    (Witness.rising).check 53 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_28_3_checked :
    (Witness.rising).check 53 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_28_4_checked :
    (Witness.rising).check 53 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_28_5_checked :
    (Witness.rising).check 53 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_28_6_checked :
    (Witness.rising).check 53 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_28_7_checked :
    (Witness.rising).check 53 28 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_28_8_checked :
    (Witness.rising).check 53 28 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_28_9_checked :
    (Witness.rising).check 53 28 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_28_10_checked :
    (Witness.rising).check 53 28 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_28_11 : Certificate := {
  objectiveScale := 43948426860000000
  eta := 33313569461863127236800
  rows := #[⟨.count 2, 7516505059398362827800⟩, ⟨.count 3, 1151900699604209034480⟩, ⟨.count 4, 152543304120993065280⟩, ⟨.count 5, 22596379003497499200⟩, ⟨.count 6, 3797611340378375520⟩, ⟨.count 7, 722442786960814920⟩, ⟨.count 8, 174345167290694400⟩, ⟨.count 9, 58456909032762240⟩, ⟨.count 10, 43746535542609900⟩, ⟨.count 12, 5741303565717720⟩, ⟨.path 11, 14469753691008000⟩, ⟨.path 12, 5829541666046280⟩, ⟨.privateRow 6 16, 104362483430513880⟩, ⟨.privateRow 6 17, 176719063541750730⟩, ⟨.privateRow 7 12, 16111361441595420⟩, ⟨.privateRow 7 13, 36685128950750280⟩, ⟨.privateRow 7 14, 54405032114372940⟩, ⟨.privateRow 7 15, 70983389539782720⟩, ⟨.privateRow 7 16, 41095646575663680⟩, ⟨.privateRow 8 9, 9534501336209850⟩, ⟨.privateRow 8 10, 12679648530232320⟩, ⟨.privateRow 8 11, 18324403520449026⟩, ⟨.privateRow 8 12, 2966289304598620⟩, ⟨.privateRow 8 13, 61611039586841745⟩, ⟨.privateRow 9 5, 985676926185952⟩, ⟨.privateRow 9 6, 2655467358944400⟩, ⟨.privateRow 9 7, 5482800509820480⟩, ⟨.privateRow 9 8, 6459602399209960⟩, ⟨.privateRow 9 9, 5329803242487360⟩, ⟨.privateRow 10 3, 2692094494929840⟩, ⟨.privateRow 10 4, 387789802245846⟩, ⟨.privateRow 11 0, 370341041630560⟩, ⟨.hall 6 12, 3680094107628⟩, ⟨.hall 5 16, 50342492101200⟩, ⟨.hall 7 20, 38138005344839400⟩, ⟨.hall 4 23, 6355971005041377720⟩]
  caps := #[0, 0, 415764630520668000, 320044436167448520, 58340584196986320, 23442873767303760, 5785835785598940, 1616328668336760, 732040641252967, 0, 313099569796014, 0, 88238100328560, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_28_11_checked :
    (Witness.linear .positive case_53_28_11).check 53 28 11 = true := by
  change case_53_28_11.check 53 28 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_28_12 : Certificate := {
  objectiveScale := 709261488000000
  eta := 873264284013285964800
  rows := #[⟨.count 2, 218316071003321491200⟩, ⟨.count 3, 37677978920742320160⟩, ⟨.count 4, 5671232147495154240⟩, ⟨.count 5, 942808387439318400⟩, ⟨.count 6, 168130357711636320⟩, ⟨.count 7, 33683743012439520⟩, ⟨.count 8, 7737588906727680⟩, ⟨.count 9, 2107552988661120⟩, ⟨.count 10, 853410541183200⟩, ⟨.count 11, 707464970372160⟩, ⟨.path 12, 142682550753600⟩, ⟨.path 13, 130955068504260⟩, ⟨.privateRow 6 17, 3804715042128000⟩, ⟨.privateRow 7 14, 1619757305105940⟩, ⟨.privateRow 7 15, 2597790774252960⟩, ⟨.privateRow 7 16, 3574429657999200⟩, ⟨.privateRow 8 10, 48423645990720⟩, ⟨.privateRow 8 11, 475889752506168⟩, ⟨.privateRow 8 12, 805220101605920⟩, ⟨.privateRow 8 13, 1223891723584530⟩, ⟨.privateRow 8 14, 1439784271205280⟩, ⟨.privateRow 8 15, 1393560320912760⟩, ⟨.privateRow 9 7, 20804062245120⟩, ⟨.privateRow 9 8, 149518626216960⟩, ⟨.privateRow 9 9, 260558194216320⟩, ⟨.privateRow 9 10, 383911060845312⟩, ⟨.privateRow 9 11, 466879239706880⟩, ⟨.privateRow 9 12, 535958310888000⟩, ⟨.privateRow 9 13, 373168336020480⟩, ⟨.privateRow 10 4, 2473653742560⟩, ⟨.privateRow 10 5, 54729589054140⟩, ⟨.privateRow 10 7, 313690215228390⟩, ⟨.privateRow 10 8, 73366321228200⟩, ⟨.privateRow 11 2, 20484945055575⟩, ⟨.privateRow 11 3, 39001274007696⟩, ⟨.privateRow 11 4, 18817437398760⟩, ⟨.privateRow 12 0, 16749130277880⟩, ⟨.privateRow 13 0, 8185483332180⟩, ⟨.privateRow 14 0, 7450409486520⟩, ⟨.privateRow 15 0, 9541235864160⟩, ⟨.privateRow 15 13, 3710480613840⟩, ⟨.privateRow 16 0, 14841922455360⟩, ⟨.privateRow 16 11, 927620153460⟩, ⟨.privateRow 17 0, 25286238257280⟩, ⟨.privateRow 17 6, 3298204990080⟩, ⟨.privateRow 18 0, 57343791304800⟩, ⟨.privateRow 19 0, 145980908721648⟩, ⟨.privateRow 20 0, 469248188529120⟩, ⟨.privateRow 21 0, 1854798583037400⟩, ⟨.privateRow 22 0, 9930306259954080⟩, ⟨.privateRow 23 0, 73240764560964000⟩, ⟨.privateRow 24 0, 849006942790694688⟩, ⟨.privateRow 25 3, 82474960156810341120⟩, ⟨.hall 14 5, 5285584920⟩, ⟨.hall 20 7, 142676814079800⟩, ⟨.hall 13 9, 4271615568⟩, ⟨.hall 18 9, 12615634087056⟩, ⟨.hall 15 11, 118925660700⟩, ⟨.hall 7 12, 139682510352⟩, ⟨.hall 6 13, 367606057104⟩, ⟨.hall 6 14, 57156393294⟩, ⟨.hall 5 18, 28297066374720⟩, ⟨.hall 8 19, 266330052948960⟩, ⟨.hall 4 22, 10273971281694120⟩]
  caps := #[0, 0, 69552167445446400, 0, 169022332051560, 0, 205123767488640, 0, 15787319611500, 21362073928816, 0, 10727571314070, 0, 0, 17945768937096, 0, 6136564092120, 8795213306880, 0, 42853106263968, 0, 913131610110720, 0, 0, 121286706112956384, 0] }

theorem case_53_28_12_checked :
    (Witness.linear .positive case_53_28_12).check 53 28 12 = true := by
  change case_53_28_12.check 53 28 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_28_13 : Certificate := {
  objectiveScale := 1908816000000
  eta := 3294847417400098560
  rows := #[⟨.count 2, 903704869076929920⟩, ⟨.count 3, 173145867364229760⟩, ⟨.count 4, 29917267872972480⟩, ⟨.count 5, 5481231189033600⟩, ⟨.count 6, 1078545157129440⟩, ⟨.count 7, 230724430896960⟩, ⟨.count 8, 54270463927680⟩, ⟨.count 9, 13968868193280⟩, ⟨.count 10, 4762114156800⟩, ⟨.count 11, 2037126611520⟩, ⟨.count 12, 1933191580320⟩, ⟨.path 13, 105287904540⟩, ⟨.path 14, 486547654320⟩, ⟨.privateRow 7 15, 8549938631520⟩, ⟨.privateRow 7 16, 19291286654640⟩, ⟨.privateRow 8 12, 1882308908480⟩, ⟨.privateRow 8 13, 5298678755370⟩, ⟨.privateRow 8 14, 8727393074400⟩, ⟨.privateRow 8 15, 13392711171840⟩, ⟨.privateRow 9 9, 328698115200⟩, ⟨.privateRow 9 10, 1485074118528⟩, ⟨.privateRow 9 11, 2533915063680⟩, ⟨.privateRow 9 12, 3758983628400⟩, ⟨.privateRow 9 13, 5389503799680⟩, ⟨.privateRow 9 14, 6014373805440⟩, ⟨.privateRow 10 6, 8394752520⟩, ⟨.privateRow 10 7, 428259571740⟩, ⟨.privateRow 10 8, 755805239280⟩, ⟨.privateRow 10 9, 1214339109984⟩, ⟨.privateRow 10 10, 839984024880⟩, ⟨.privateRow 10 11, 3505858521165⟩, ⟨.privateRow 11 4, 85037752800⟩, ⟨.privateRow 11 5, 247772392560⟩, ⟨.privateRow 11 6, 421645524300⟩, ⟨.privateRow 11 7, 541149336000⟩, ⟨.privateRow 11 8, 110454592248⟩, ⟨.privateRow 12 2, 110864033280⟩, ⟨.privateRow 12 3, 145509043680⟩, ⟨.privateRow 13 0, 57863829870⟩, ⟨.privateRow 14 0, 32566309776⟩, ⟨.privateRow 15 0, 23621598000⟩, ⟨.privateRow 16 0, 41210603280⟩, ⟨.privateRow 17 0, 35274919680⟩, ⟨.privateRow 18 0, 64737494640⟩, ⟨.privateRow 19 0, 134926567776⟩, ⟨.privateRow 20 0, 339101162400⟩, ⟨.privateRow 21 0, 1068168661560⟩, ⟨.privateRow 22 0, 3662292553920⟩, ⟨.privateRow 23 0, 15666473702880⟩, ⟨.privateRow 25 3, 25943680451969280⟩, ⟨.hall 14 3, 563284260⟩, ⟨.hall 15 4, 262095120⟩, ⟨.hall 23 4, 1297184022598464⟩, ⟨.hall 22 5, 211497394988880⟩, ⟨.hall 21 6, 43947510647040⟩, ⟨.hall 20 7, 12970619461800⟩, ⟨.hall 19 8, 4272674646240⟩, ⟨.hall 18 9, 1821508664976⟩, ⟨.hall 17 10, 899510451840⟩, ⟨.hall 16 11, 529123795200⟩, ⟨.hall 7 12, 780628464⟩, ⟨.hall 7 13, 1792754964⟩, ⟨.hall 8 14, 390654264⟩, ⟨.hall 6 15, 11507092740⟩, ⟨.hall 8 15, 8393264880⟩, ⟨.hall 6 16, 3407236560⟩, ⟨.hall 5 21, 60181744240800⟩, ⟨.hall 4 22, 54197949045240⟩]
  caps := #[0, 0, 4537790100480, 0, 9829309602840, 4374404994960, 1353455943840, 0, 184754698310, 73816300740, 22771743561, 33594794520, 0, 15311824500, 0, 25958979900, 129737084400, 11223838080, 0, 0, 6442922085600, 0, 97050752678880, 0, 0, 0] }

theorem case_53_28_13_checked :
    (Witness.linear .positive case_53_28_13).check 53 28 13 = true := by
  change case_53_28_13.check 53 28 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_28_14 : Certificate := {
  objectiveScale := 240411921750000
  eta := 559021454538808060800
  rows := #[⟨.count 2, 167228640246651984000⟩, ⟨.count 3, 35398459997552171520⟩, ⟨.count 4, 6849669996325316160⟩, ⟨.count 5, 1439323700437022400⟩, ⟨.count 6, 316867045203989280⟩, ⟨.count 7, 71863239263175360⟩, ⟨.count 8, 18222582570192000⟩, ⟨.count 9, 4841165251802880⟩, ⟨.count 10, 1512864141188400⟩, ⟨.count 11, 530598727779120⟩, ⟨.count 12, 234290347331040⟩, ⟨.count 13, 234290347331040⟩, ⟨.path 15, 48704433025248⟩, ⟨.path 16, 12939254952624⟩, ⟨.privateRow 4 24, 26911441259342640⟩, ⟨.privateRow 7 16, 2644641041842800⟩, ⟨.privateRow 8 13, 160482971498850⟩, ⟨.privateRow 8 14, 1747711328322960⟩, ⟨.privateRow 8 15, 3550642603828320⟩, ⟨.privateRow 9 11, 301002849347200⟩, ⟨.privateRow 9 12, 711362848996800⟩, ⟨.privateRow 9 13, 1617619629225600⟩, ⟨.privateRow 9 14, 2254273137916800⟩, ⟨.privateRow 10 8, 17341130472120⟩, ⟨.privateRow 10 9, 181105185597336⟩, ⟨.privateRow 10 10, 367618677786360⟩, ⟨.privateRow 10 11, 639952494506325⟩, ⟨.privateRow 10 12, 986337304472520⟩, ⟨.privateRow 10 13, 1136840662617660⟩, ⟨.privateRow 11 6, 28503237442680⟩, ⟨.privateRow 11 7, 86506329021840⟩, ⟨.privateRow 11 8, 177158583489888⟩, ⟨.privateRow 11 9, 298837361222400⟩, ⟨.privateRow 11 10, 392650367078970⟩, ⟨.privateRow 11 11, 274382813184480⟩, ⟨.privateRow 12 4, 23588055330840⟩, ⟨.privateRow 12 5, 49480436915910⟩, ⟨.privateRow 12 6, 80289339170040⟩, ⟨.privateRow 12 7, 141722690493384⟩, ⟨.privateRow 12 8, 5104364865600⟩, ⟨.privateRow 13 2, 7875305792640⟩, ⟨.privateRow 13 3, 51131238348960⟩, ⟨.privateRow 14 0, 10948862636712⟩, ⟨.privateRow 15 0, 3445446284280⟩, ⟨.privateRow 16 0, 3541822404120⟩, ⟨.privateRow 17 0, 6171641155680⟩, ⟨.privateRow 18 0, 13553987035680⟩, ⟨.privateRow 19 0, 34078595975424⟩, ⟨.privateRow 20 0, 112412035335600⟩, ⟨.privateRow 21 0, 438406937808840⟩, ⟨.privateRow 22 0, 2428099963248960⟩, ⟨.privateRow 23 0, 17311453441682400⟩, ⟨.privateRow 24 0, 191118445996173696⟩, ⟨.privateRow 25 0, 5016859207399559520⟩, ⟨.hall 8 12, 566599529496⟩, ⟨.hall 8 13, 464765853552⟩, ⟨.hall 7 14, 3045767188464⟩, ⟨.hall 9 14, 713203178688⟩, ⟨.hall 9 15, 6303883425840⟩, ⟨.hall 10 17, 337410118445400⟩, ⟨.hall 6 18, 187280141275656⟩, ⟨.hall 5 22, 363745796426812800⟩, ⟨.hall 4 23, 311842227224487960⟩]
  caps := #[0, 0, 0, 10716407719041024, 899532939601296, 0, 145768204934352, 80028320512140, 0, 9384114839736, 0, 10731027926892, 6121574418960, 6121574418960, 0, 2044188226080, 0, 32482321872000, 0, 208731400349472, 0, 3102572175262560, 0, 0, 1528947567969389568, 0] }

theorem case_53_28_14_checked :
    (Witness.linear .positive case_53_28_14).check 53 28 14 = true := by
  change case_53_28_14.check 53 28 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_28_15 : Certificate := {
  objectiveScale := 4383579200000
  eta := 11467106759770421760
  rows := #[⟨.count 2, 3516089359032169920⟩, ⟨.count 3, 807779050594195680⟩, ⟨.count 4, 178392711829812480⟩, ⟨.count 5, 44169282807249600⟩, ⟨.count 6, 10853814365634240⟩, ⟨.count 7, 2756324902050720⟩, ⟨.count 8, 771380185255680⟩, ⟨.count 9, 223978102508160⟩, ⟨.count 10, 68587671952800⟩, ⟨.count 11, 22675159306800⟩, ⟨.count 12, 8834477652000⟩, ⟨.count 13, 4240549272960⟩, ⟨.count 14, 4535031861360⟩, ⟨.path 17, 876719211984⟩, ⟨.privateRow 4 24, 7118275960635840⟩, ⟨.privateRow 6 22, 10980061728395760⟩, ⟨.privateRow 8 14, 6856982452320⟩, ⟨.privateRow 8 15, 95785369920240⟩, ⟨.privateRow 8 16, 161242245772608⟩, ⟨.privateRow 9 12, 8470390088160⟩, ⟨.privateRow 9 14, 165509923138560⟩, ⟨.privateRow 10 10, 4916074483320⟩, ⟨.privateRow 10 11, 17245301943870⟩, ⟨.privateRow 10 12, 19130659788240⟩, ⟨.privateRow 10 13, 83973048639480⟩, ⟨.privateRow 11 8, 2439922100616⟩, ⟨.privateRow 11 9, 7754113246880⟩, ⟨.privateRow 11 10, 15390061636950⟩, ⟨.privateRow 11 11, 15827100569280⟩, ⟨.privateRow 11 12, 14991840864000⟩, ⟨.privateRow 12 6, 1188638811360⟩, ⟨.privateRow 12 7, 3616246185552⟩, ⟨.privateRow 12 8, 549700831680⟩, ⟨.privateRow 12 9, 18372032483805⟩, ⟨.privateRow 12 10, 16394266385640⟩, ⟨.privateRow 13 4, 607087182240⟩, ⟨.privateRow 13 5, 1749597252480⟩, ⟨.privateRow 13 6, 3457678637952⟩, ⟨.privateRow 13 7, 1002750967680⟩, ⟨.privateRow 13 8, 11104258833360⟩, ⟨.privateRow 14 3, 1136211986910⟩, ⟨.privateRow 14 4, 2307672647280⟩, ⟨.privateRow 14 5, 2588501952036⟩, ⟨.privateRow 14 6, 899807909000⟩, ⟨.privateRow 14 8, 3647377202040⟩, ⟨.privateRow 15 1, 795720784320⟩, ⟨.privateRow 15 2, 762085243920⟩, ⟨.privateRow 15 3, 2252183366160⟩, ⟨.privateRow 15 4, 2533621106016⟩, ⟨.privateRow 15 6, 2173816925280⟩, ⟨.privateRow 16 0, 1474678192680⟩, ⟨.privateRow 16 1, 468495027000⟩, ⟨.privateRow 16 2, 1615030129440⟩, ⟨.privateRow 16 3, 4969795246416⟩, ⟨.privateRow 16 5, 1651444970175⟩, ⟨.privateRow 17 0, 5113883494720⟩, ⟨.privateRow 17 3, 7162768412800⟩, ⟨.privateRow 17 5, 4883056738560⟩, ⟨.privateRow 18 0, 13998063534000⟩, ⟨.privateRow 18 3, 14813812753740⟩, ⟨.privateRow 18 8, 4460072657040⟩, ⟨.privateRow 19 0, 45001222890624⟩, ⟨.privateRow 19 4, 25031020014000⟩, ⟨.privateRow 20 0, 160067052024880⟩, ⟨.privateRow 20 4, 19023575210640⟩, ⟨.privateRow 21 0, 620860318238160⟩, ⟨.privateRow 22 0, 2988430723998720⟩, ⟨.privateRow 23 0, 19308928838799600⟩, ⟨.privateRow 23 3, 1864310370642720⟩, ⟨.privateRow 24 0, 232772466277391040⟩, ⟨.privateRow 24 4, 388975042331956080⟩, ⟨.privateRow 25 0, 5751930153538689120⟩, ⟨.hall 22 5, 33690751698043440⟩, ⟨.hall 21 6, 7699359712524480⟩, ⟨.hall 20 7, 2179064069582400⟩, ⟨.hall 11 8, 8179937304⟩, ⟨.hall 19 8, 748260624951840⟩, ⟨.hall 10 9, 22583862840⟩, ⟨.hall 18 9, 305068969741536⟩, ⟨.hall 17 10, 148282935091200⟩, ⟨.hall 9 11, 25675178760⟩, ⟨.hall 16 11, 86727799398240⟩, ⟨.hall 9 12, 24760280160⟩, ⟨.hall 15 12, 59808795908400⟩, ⟨.hall 8 13, 109292022840⟩, ⟨.hall 14 13, 47382248473560⟩, ⟨.hall 13 14, 45444553041888⟩, ⟨.hall 7 15, 368373295290⟩, ⟨.hall 12 15, 62327239834860⟩, ⟨.hall 11 16, 28519772561280⟩, ⟨.hall 8 19, 68047965681696⟩, ⟨.hall 5 20, 26964956803200⟩, ⟨.hall 6 20, 296044562988720⟩, ⟨.hall 6 21, 3759593008363920⟩, ⟨.hall 4 23, 14242604877020520⟩]
  caps := #[0, 0, 1022560150131520, 150248357274400, 11871744068800, 6844846200192, 0, 5977655820864, 1753688432496, 0, 747739198206, 119455905184, 428935694759, 275175932724, 0, 42170031904, 0, 0, 2958901015980, 9175006608768, 192157325360, 0, 0, 3329125661862000, 39816342915869520, 0] }

theorem case_53_28_15_checked :
    (Witness.linear .positive case_53_28_15).check 53 28 15 = true := by
  change case_53_28_15.check 53 28 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_28_16 : Certificate := {
  objectiveScale := 17851680000000
  eta := 29402837845565184000
  rows := #[⟨.count 2, 7565105154015208800⟩, ⟨.count 3, 1957525889174856000⟩, ⟨.count 4, 512806411041724800⟩, ⟨.count 5, 136796799923784000⟩, ⟨.count 6, 39586330597413600⟩, ⟨.count 7, 11812821008788800⟩, ⟨.count 8, 3661507267017600⟩, ⟨.count 9, 1187353796428800⟩, ⟨.count 10, 407590673490000⟩, ⟨.count 11, 150480602672400⟩, ⟨.count 12, 60074448033600⟩, ⟨.count 13, 31804119547200⟩, ⟨.count 14, 22675159306800⟩, ⟨.count 15, 19676791134000⟩, ⟨.path 14, 2541960723120⟩, ⟨.privateRow 3 25, 83893966678922400⟩, ⟨.privateRow 7 16, 117873348793200⟩, ⟨.privateRow 8 14, 69631746584400⟩, ⟨.privateRow 8 15, 678391210096600⟩, ⟨.privateRow 9 12, 30420943753200⟩, ⟨.privateRow 9 13, 250863470457600⟩, ⟨.privateRow 9 14, 628574572225600⟩, ⟨.privateRow 10 10, 11931006687600⟩, ⟨.privateRow 10 11, 96556825064700⟩, ⟨.privateRow 10 12, 248610232470600⟩, ⟨.privateRow 10 13, 430312682299500⟩, ⟨.privateRow 11 8, 4291414447320⟩, ⟨.privateRow 11 9, 38603990224800⟩, ⟨.privateRow 11 10, 103888772237250⟩, ⟨.privateRow 11 11, 190342836684000⟩, ⟨.privateRow 11 12, 271008756618600⟩, ⟨.privateRow 12 6, 1271629359000⟩, ⟨.privateRow 12 7, 15828439126500⟩, ⟨.privateRow 12 8, 44483230992200⟩, ⟨.privateRow 12 9, 78810902720550⟩, ⟨.privateRow 12 10, 138953712783600⟩, ⟨.privateRow 12 11, 113302175886900⟩, ⟨.privateRow 13 4, 113262534000⟩, ⟨.privateRow 13 5, 6845175691200⟩, ⟨.privateRow 13 6, 18348530508000⟩, ⟨.privateRow 13 7, 42828339523200⟩, ⟨.privateRow 13 8, 56795497674300⟩, ⟨.privateRow 14 3, 2785314481950⟩, ⟨.privateRow 14 4, 9958865716800⟩, ⟨.privateRow 14 5, 18022334410080⟩, ⟨.privateRow 15 1, 1628921170800⟩, ⟨.privateRow 15 2, 4950430785300⟩, ⟨.privateRow 16 0, 1751450639400⟩, ⟨.privateRow 17 0, 1499184086400⟩, ⟨.privateRow 18 0, 2992689445200⟩, ⟨.privateRow 19 0, 7645838840640⟩, ⟨.privateRow 20 0, 15372586028800⟩, ⟨.privateRow 20 1, 2161769910300⟩, ⟨.privateRow 21 0, 69176637129600⟩, ⟨.privateRow 22 0, 389118583854000⟩, ⟨.privateRow 23 0, 3107183951071200⟩, ⟨.privateRow 23 5, 1331650264744800⟩, ⟨.privateRow 24 0, 36753547306956480⟩, ⟨.privateRow 25 0, 826954814406520800⟩, ⟨.hall 19 3, 823531394400⟩, ⟨.hall 20 3, 2470594183200⟩, ⟨.hall 21 5, 34588318564800⟩, ⟨.hall 20 7, 21617699103000⟩, ⟨.hall 10 10, 47127336375⟩, ⟨.hall 9 11, 275205961800⟩, ⟨.hall 10 11, 202297788000⟩, ⟨.hall 9 12, 142775186400⟩, ⟨.hall 8 13, 1009319110800⟩, ⟨.hall 7 16, 9926176740480⟩, ⟨.hall 11 16, 307994142456000⟩, ⟨.hall 7 17, 6547188648000⟩, ⟨.hall 6 21, 97680556019592000⟩, ⟨.hall 5 22, 143361061251408000⟩, ⟨.hall 4 23, 176352865742453400⟩, ⟨.hall 3 24, 158999041610529120⟩, ⟨.assumptionRow 16, 20940883867904⟩]
  caps := #[0, 6933907469885760, 0, 2078839644537600, 308667232873664, 53028342318952, 17702143787328, 12762101992640, 0, 0, 1309791262416, 0, 1062706215610, 64570402400, 2559693820502, 1264092733904, 0, 0, 0, 33860143437120, 0, 0, 3605832210380400, 5770484480560800, 0, 0] }

theorem case_53_28_16_checked :
    (Witness.linear .conditional case_53_28_16).check 53 28 16 = true := by
  change case_53_28_16.check 53 28 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_28_17 : Certificate := {
  objectiveScale := 70662900000000
  eta := 62848565894895580800
  rows := #[⟨.count 2, 16906631761199980800⟩, ⟨.count 3, 4757986395933170400⟩, ⟨.count 4, 1364094107558582400⟩, ⟨.count 5, 397938605088024000⟩, ⟨.count 6, 119070286659324000⟩, ⟨.count 7, 37560183304644000⟩, ⟨.count 8, 12284314403961600⟩, ⟨.count 9, 4169230944278400⟩, ⟨.count 10, 1467326424564000⟩, ⟨.count 11, 531835554650400⟩, ⟨.count 12, 196125403874400⟩, ⟨.count 13, 106013731824000⟩, ⟨.count 14, 55657209207600⟩, ⟨.count 15, 59030373402000⟩, ⟨.count 16, 53970627110400⟩, ⟨.count 18, 57343791304800⟩, ⟨.path 13, 8394579074700⟩, ⟨.privateRow 3 25, 663161831842910400⟩, ⟨.privateRow 8 15, 2042607084718200⟩, ⟨.privateRow 9 13, 617663843596800⟩, ⟨.privateRow 9 14, 2308243765027200⟩, ⟨.privateRow 10 11, 180464284400400⟩, ⟨.privateRow 10 12, 799560384222600⟩, ⟨.privateRow 10 13, 1784825504361900⟩, ⟨.privateRow 11 9, 49847870872800⟩, ⟨.privateRow 11 10, 284540454648450⟩, ⟨.privateRow 11 11, 711175450986000⟩, ⟨.privateRow 11 12, 1234484396145000⟩, ⟨.privateRow 12 7, 10866407511960⟩, ⟨.privateRow 12 8, 102136377743400⟩, ⟨.privateRow 12 9, 291924270913275⟩, ⟨.privateRow 12 10, 564396915139200⟩, ⟨.privateRow 12 11, 840747789882000⟩, ⟨.privateRow 13 6, 35269953087600⟩, ⟨.privateRow 13 7, 120103591053600⟩, ⟨.privateRow 13 8, 255197478482100⟩, ⟨.privateRow 13 9, 415958274151200⟩, ⟨.privateRow 13 10, 393813830718000⟩, ⟨.privateRow 14 4, 8392753769400⟩, ⟨.privateRow 14 5, 50444867392920⟩, ⟨.privateRow 14 6, 119118207007800⟩, ⟨.privateRow 14 7, 197892299404800⟩, ⟨.privateRow 15 2, 1358635578300⟩, ⟨.privateRow 15 3, 19881225327600⟩, ⟨.privateRow 15 4, 57456230111280⟩, ⟨.privateRow 15 5, 19676791134000⟩, ⟨.privateRow 16 1, 8714007502200⟩, ⟨.privateRow 16 2, 12266051616000⟩, ⟨.privateRow 17 0, 3498096201600⟩, ⟨.hall 10 10, 874814731875⟩, ⟨.hall 11 10, 1113576641100⟩, ⟨.hall 9 11, 297163528200⟩, ⟨.hall 10 11, 1105142519250⟩, ⟨.hall 9 12, 3466541232000⟩, ⟨.hall 8 14, 11679718009960⟩, ⟨.hall 8 15, 3977440587120⟩, ⟨.hall 12 15, 383637192038100⟩, ⟨.hall 7 17, 243476372379240⟩, ⟨.hall 6 19, 2176773154976160⟩, ⟨.hall 4 21, 3282592069247400⟩, ⟨.hall 5 21, 29907274977216000⟩, ⟨.hall 3 24, 827434208501828928⟩, ⟨.assumptionRow 17, 55584240465600⟩]
  caps := #[0, 0, 0, 5354066880254400, 21840386349600, 92066236554600, 17210558164800, 0, 0, 7047796239120, 0, 0, 6664753692870, 0, 0, 0, 10980079475400, 0, 13319108695200, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_28_17_checked :
    (Witness.linear .conditional case_53_28_17).check 53 28 17 = true := by
  change case_53_28_17.check 53 28 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_28_18 : Certificate := {
  objectiveScale := 32515560000000
  eta := 27197625007147795200
  rows := #[⟨.count 2, 7595733110104339200⟩, ⟨.count 3, 2141293625709638400⟩, ⟨.count 4, 610137939483072000⟩, ⟨.count 5, 175881599902008000⟩, ⟨.count 6, 53387069704768800⟩, ⟨.count 7, 16534126492884000⟩, ⟨.count 8, 5182179658656000⟩, ⟨.count 9, 1632611470089600⟩, ⟨.count 10, 508785599322000⟩, ⟨.count 11, 150480602672400⟩, ⟨.count 12, 56540656972800⟩, ⟨.count 13, 17668955304000⟩, ⟨.count 14, 10306890594000⟩, ⟨.count 15, 11243880648000⟩, ⟨.count 16, 8995104518400⟩, ⟨.count 17, 8495376489600⟩, ⟨.count 19, 51882477847200⟩, ⟨.path 13, 5558967291150⟩, ⟨.privateRow 2 26, 45941934133695600⟩, ⟨.privateRow 8 15, 789185078481800⟩, ⟨.privateRow 9 13, 210885228153600⟩, ⟨.privateRow 9 14, 993875761278400⟩, ⟨.privateRow 10 11, 50983971313275⟩, ⟨.privateRow 10 12, 313824740229000⟩, ⟨.privateRow 10 13, 847179557324100⟩, ⟨.privateRow 11 9, 9432366543600⟩, ⟨.privateRow 11 10, 96018055783650⟩, ⟨.privateRow 11 11, 303450921774000⟩, ⟨.privateRow 11 12, 628595394226800⟩, ⟨.privateRow 12 8, 27010597413800⟩, ⟨.privateRow 12 9, 108590454472500⟩, ⟨.privateRow 12 10, 259649505086400⟩, ⟨.privateRow 12 11, 455000139293700⟩, ⟨.privateRow 13 6, 4349281305600⟩, ⟨.privateRow 13 7, 36908484412800⟩, ⟨.privateRow 13 8, 105996742443900⟩, ⟨.privateRow 13 9, 212668205983200⟩, ⟨.privateRow 13 10, 333422247589200⟩, ⟨.privateRow 13 11, 150349218132960⟩, ⟨.privateRow 14 5, 9806270193720⟩, ⟨.privateRow 14 6, 41947408703200⟩, ⟨.privateRow 14 7, 98099512260750⟩, ⟨.privateRow 14 8, 172419555508200⟩, ⟨.privateRow 14 9, 107068961099100⟩, ⟨.privateRow 15 3, 919953871200⟩, ⟨.privateRow 15 4, 14823182654280⟩, ⟨.privateRow 15 5, 44933878589600⟩, ⟨.privateRow 15 6, 72077959903950⟩, ⟨.privateRow 16 2, 3143175726600⟩, ⟨.privateRow 16 3, 19480023222660⟩, ⟨.privateRow 16 4, 14710743847800⟩, ⟨.privateRow 17 1, 7450490611200⟩, ⟨.privateRow 17 2, 1099401663360⟩, ⟨.privateRow 18 0, 1544613907200⟩, ⟨.hall 11 10, 826437946950⟩, ⟨.hall 10 11, 1311869356875⟩, ⟨.hall 11 11, 621417113625⟩, ⟨.hall 9 12, 104075294400⟩, ⟨.hall 10 12, 1103678787750⟩, ⟨.hall 9 13, 5368015052400⟩, ⟨.hall 12 13, 13001406277860⟩, ⟨.hall 12 14, 27916949380320⟩, ⟨.hall 8 15, 11288812334800⟩, ⟨.hall 8 16, 47559642530400⟩, ⟨.hall 7 20, 154773623388384000⟩, ⟨.hall 6 21, 244163657337818400⟩, ⟨.hall 5 22, 345116227279824000⟩, ⟨.hall 4 23, 436508903827596600⟩, ⟨.hall 3 24, 462934898035882272⟩, ⟨.hall 2 25, 340441511913795600⟩, ⟨.assumptionRow 18, 11170155689000⟩]
  caps := #[0, 122163872237024800, 11233042525959800, 1892355638465600, 377984341338912, 0, 46361523731600, 0, 971555635050, 369227909050, 0, 4588244670100, 201590684050, 55074743150, 863265095000, 128639840420, 3416832852300, 3071979781360, 1894767107800, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_28_18_checked :
    (Witness.linear .conditional case_53_28_18).check 53 28 18 = true := by
  change case_53_28_18.check 53 28 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_29_1_checked :
    (Witness.rising).check 53 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_29_2_checked :
    (Witness.rising).check 53 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_29_3_checked :
    (Witness.rising).check 53 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_29_4_checked :
    (Witness.rising).check 53 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_29_5_checked :
    (Witness.rising).check 53 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_29_6_checked :
    (Witness.rising).check 53 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_29_7_checked :
    (Witness.rising).check 53 29 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_29_8_checked :
    (Witness.rising).check 53 29 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_29_9_checked :
    (Witness.rising).check 53 29 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_29_10_checked :
    (Witness.rising).check 53 29 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_29_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_29_11_checked :
    (Witness.linear .positive case_53_29_11).check 53 29 11 = true := by
  change case_53_29_11.check 53 29 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_29_12 : Certificate := {
  objectiveScale := 24345360000000
  eta := 39785714959780389600
  rows := #[⟨.count 2, 8932709975908118400⟩, ⟨.count 3, 1347751127036714400⟩, ⟨.count 4, 204832022540745600⟩, ⟨.count 5, 33879258034221600⟩, ⟨.count 6, 6045673997563200⟩, ⟨.count 7, 1191476552666400⟩, ⟨.count 8, 272851503724800⟩, ⟨.count 9, 74209612276800⟩, ⟨.count 10, 29234089684800⟩, ⟨.count 11, 24736537425600⟩, ⟨.path 12, 5164203135000⟩, ⟨.path 13, 4345045286400⟩, ⟨.privateRow 4 25, 7938019110621600⟩, ⟨.privateRow 5 21, 1255555963902240⟩, ⟨.privateRow 6 17, 117418239338400⟩, ⟨.privateRow 6 18, 367273330023600⟩, ⟨.privateRow 6 19, 483326240997600⟩, ⟨.privateRow 6 20, 831484973919600⟩, ⟨.privateRow 7 14, 54613134576000⟩, ⟨.privateRow 7 15, 104220065149200⟩, ⟨.privateRow 7 16, 154217089540800⟩, ⟨.privateRow 7 17, 209198646056400⟩, ⟨.privateRow 7 18, 257045820071040⟩, ⟨.privateRow 7 19, 273520782334800⟩, ⟨.privateRow 8 10, 687126039600⟩, ⟨.privateRow 8 11, 17274689359200⟩, ⟨.privateRow 8 12, 32682213083520⟩, ⟨.privateRow 8 13, 49098278829600⟩, ⟨.privateRow 8 14, 61841343564000⟩, ⟨.privateRow 8 15, 69926229172800⟩, ⟨.privateRow 8 16, 87952133068800⟩, ⟨.privateRow 8 17, 46774543495680⟩, ⟨.privateRow 9 7, 495266171400⟩, ⟨.privateRow 9 8, 5232729070800⟩, ⟨.privateRow 9 9, 10587987610200⟩, ⟨.privateRow 9 10, 16014011832000⟩, ⟨.privateRow 9 11, 20445122978280⟩, ⟨.privateRow 9 12, 23591327359600⟩, ⟨.privateRow 9 13, 5387692810500⟩, ⟨.privateRow 10 4, 21082276215⟩, ⟨.privateRow 10 5, 1956435232752⟩, ⟨.privateRow 10 7, 12947761023120⟩, ⟨.privateRow 10 8, 1021319158860⟩, ⟨.privateRow 11 2, 703923620400⟩, ⟨.privateRow 11 3, 1591209895275⟩, ⟨.privateRow 11 4, 342670648320⟩, ⟨.privateRow 12 0, 521007656400⟩, ⟨.privateRow 13 0, 255840076800⟩, ⟨.privateRow 14 0, 276077426625⟩, ⟨.privateRow 15 0, 389787862464⟩, ⟨.privateRow 16 0, 655893037800⟩, ⟨.privateRow 17 0, 1326201307200⟩, ⟨.privateRow 18 0, 3185766183600⟩, ⟨.privateRow 19 0, 9681419311200⟩, ⟨.privateRow 20 0, 37355384049984⟩, ⟨.privateRow 21 0, 184471032345600⟩, ⟨.privateRow 22 0, 1316517875372700⟩, ⟨.privateRow 23 0, 14267681407980000⟩, ⟨.privateRow 24 0, 336907516980434400⟩, ⟨.hall 5 21, 6963804256500⟩, ⟨.hall 6 21, 32282190813600⟩, ⟨.hall 5 22, 121435074961200⟩, ⟨.hall 6 22, 165976439428800⟩, ⟨.hall 4 24, 11140205643350784⟩]
  caps := #[0, 0, 2270177573484600, 340010106493200, 11988831956400, 11829527642400, 9143665474320, 1503094699080, 0, 2180859979040, 538181308323, 0, 69419109000, 0, 215842351725, 397283782896, 843291048600, 0, 5006204002800, 18618114060000, 0, 420824542538400, 0, 38237386173386400, 0] }

theorem case_53_29_12_checked :
    (Witness.linear .positive case_53_29_12).check 53 29 12 = true := by
  change case_53_29_12.check 53 29 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_29_13 : Certificate := {
  objectiveScale := 11361168000000
  eta := 26738205665810839200
  rows := #[⟨.count 2, 6463830385071259200⟩, ⟨.count 3, 1078636714443288000⟩, ⟨.count 4, 187607039895475200⟩, ⟨.count 5, 34449965290540800⟩, ⟨.count 6, 6766567373966400⟩, ⟨.count 7, 1439966314987200⟩, ⟨.count 8, 332818867180800⟩, ⟨.count 9, 86015686957200⟩, ⟨.count 10, 28109701620000⟩, ⟨.count 11, 12368268712800⟩, ⟨.count 12, 11416863427200⟩, ⟨.path 13, 788331398400⟩, ⟨.path 14, 2788130872800⟩, ⟨.privateRow 4 25, 9442610968190400⟩, ⟨.privateRow 5 21, 544766017395600⟩, ⟨.privateRow 6 18, 187505095377600⟩, ⟨.privateRow 6 19, 536847112882080⟩, ⟨.privateRow 6 20, 865618183029600⟩, ⟨.privateRow 7 15, 47672715390300⟩, ⟨.privateRow 7 16, 137443055349600⟩, ⟨.privateRow 7 17, 218149132000800⟩, ⟨.privateRow 7 18, 363359388712320⟩, ⟨.privateRow 7 19, 405957633681600⟩, ⟨.privateRow 8 12, 10231931389680⟩, ⟨.privateRow 8 13, 36563434107200⟩, ⟨.privateRow 8 14, 61794494061300⟩, ⟨.privateRow 8 15, 91396686981600⟩, ⟨.privateRow 8 16, 129304627452000⟩, ⟨.privateRow 8 17, 148269306144960⟩, ⟨.privateRow 8 18, 129679423473600⟩, ⟨.privateRow 9 9, 1655349095400⟩, ⟨.privateRow 9 10, 9898022206800⟩, ⟨.privateRow 9 11, 17877770230320⟩, ⟨.privateRow 9 12, 27755727599600⟩, ⟨.privateRow 9 13, 35418224041200⟩, ⟨.privateRow 9 14, 48991194252000⟩, ⟨.privateRow 9 15, 43632503514600⟩, ⟨.privateRow 10 7, 2698531355520⟩, ⟨.privateRow 10 8, 5415802512120⟩, ⟨.privateRow 10 9, 8954217679680⟩, ⟨.privateRow 10 10, 11941001248176⟩, ⟨.privateRow 10 11, 14004878007120⟩, ⟨.privateRow 11 4, 487234828080⟩, ⟨.privateRow 11 5, 1784105551800⟩, ⟨.privateRow 11 6, 3101334112800⟩, ⟨.privateRow 11 7, 3339700263900⟩, ⟨.privateRow 12 2, 726295999275⟩, ⟨.privateRow 12 3, 774715732560⟩, ⟨.privateRow 13 0, 307807592400⟩, ⟨.privateRow 14 0, 175685635125⟩, ⟨.privateRow 15 0, 224877612960⟩, ⟨.privateRow 16 0, 374796021600⟩, ⟨.privateRow 17 0, 691931116800⟩, ⟨.privateRow 17 5, 140548508100⟩, ⟨.privateRow 18 0, 1820437819200⟩, ⟨.privateRow 19 0, 5461313457600⟩, ⟨.privateRow 20 0, 19715341581936⟩, ⟨.privateRow 21 0, 103764955694400⟩, ⟨.privateRow 22 0, 726354689860800⟩, ⟨.privateRow 23 0, 7989901588468800⟩, ⟨.privateRow 24 0, 183767736534782400⟩, ⟨.hall 19 3, 172941592824⟩, ⟨.hall 6 18, 251925785280⟩, ⟨.hall 6 19, 335819895840⟩, ⟨.hall 7 21, 297724330612800⟩, ⟨.hall 5 22, 314866486935000⟩, ⟨.hall 4 24, 14078829188616192⟩]
  caps := #[0, 0, 3164086424116800, 0, 147455463355200, 32221749399840, 1768457691000, 11411374894920, 713882332800, 1038863840560, 804486645144, 0, 0, 626142333600, 0, 0, 2623572151200, 0, 0, 46421164389600, 0, 0, 0, 0, 0] }

theorem case_53_29_13_checked :
    (Witness.linear .positive case_53_29_13).check 53 29 13 = true := by
  change case_53_29_13.check 53 29 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_29_14 : Certificate := {
  objectiveScale := 129514840000000
  eta := 422849561766534302400
  rows := #[⟨.count 2, 103297442686518880800⟩, ⟨.count 3, 20523514939361834400⟩, ⟨.count 4, 4099442104618660800⟩, ⟨.count 5, 892326736493992800⟩, ⟨.count 6, 194567483897186400⟩, ⟨.count 7, 44106932811942000⟩, ⟨.count 8, 10933549542115200⟩, ⟨.count 9, 2795509826109000⟩, ⟨.count 10, 855097123280400⟩, ⟨.count 11, 292862934163800⟩, ⟨.count 12, 127216478188800⟩, ⟨.count 13, 137817851371200⟩, ⟨.path 15, 33208900124400⟩, ⟨.privateRow 5 23, 282873645718503840⟩, ⟨.privateRow 7 16, 950853682350000⟩, ⟨.privateRow 7 17, 5079249070295400⟩, ⟨.privateRow 7 19, 29521471227147900⟩, ⟨.privateRow 8 14, 977514873835500⟩, ⟨.privateRow 8 15, 2039077755514800⟩, ⟨.privateRow 8 16, 4489868940757200⟩, ⟨.privateRow 8 18, 18647694957691800⟩, ⟨.privateRow 9 11, 109627836318000⟩, ⟨.privateRow 9 12, 437699287225200⟩, ⟨.privateRow 9 13, 946453653545400⟩, ⟨.privateRow 9 14, 1678872007612800⟩, ⟨.privateRow 9 15, 2610360591438600⟩, ⟨.privateRow 9 16, 1112357112506640⟩, ⟨.privateRow 9 17, 4802612796031050⟩, ⟨.privateRow 10 9, 98067082669920⟩, ⟨.privateRow 10 10, 206977354968384⟩, ⟨.privateRow 10 11, 379555931074320⟩, ⟨.privateRow 10 12, 696958969391685⟩, ⟨.privateRow 10 13, 481736035020240⟩, ⟨.privateRow 10 14, 2086948577373660⟩, ⟨.privateRow 10 16, 837008530287930⟩, ⟨.privateRow 10 17, 408546403345080⟩, ⟨.privateRow 11 6, 10721843332200⟩, ⟨.privateRow 11 7, 49854563658900⟩, ⟨.privateRow 11 8, 110339705385000⟩, ⟨.privateRow 11 9, 170549591071860⟩, ⟨.privateRow 11 10, 295299108304200⟩, ⟨.privateRow 11 11, 196351285405275⟩, ⟨.privateRow 11 12, 811022258475000⟩, ⟨.privateRow 11 13, 738943820514900⟩, ⟨.privateRow 11 17, 3771980625312900⟩, ⟨.privateRow 12 4, 12210510183300⟩, ⟨.privateRow 12 6, 109437091914150⟩, ⟨.privateRow 12 7, 59873664450600⟩, ⟨.privateRow 12 8, 6890892568560⟩, ⟨.privateRow 12 9, 462337663788000⟩, ⟨.privateRow 12 11, 440524917775800⟩, ⟨.privateRow 12 12, 484791961153500⟩, ⟨.privateRow 13 3, 17511196774500⟩, ⟨.privateRow 13 4, 36391252174200⟩, ⟨.privateRow 13 5, 72884440629000⟩, ⟨.privateRow 13 6, 51802164414000⟩, ⟨.privateRow 13 8, 339096700542600⟩, ⟨.privateRow 13 9, 66755521757925⟩, ⟨.privateRow 13 12, 1222073293601160⟩, ⟨.privateRow 14 0, 4698335842200⟩, ⟨.privateRow 14 2, 37810417015800⟩, ⟨.privateRow 14 3, 19154753818200⟩, ⟨.privateRow 14 4, 55727483461650⟩, ⟨.privateRow 14 5, 26481529292400⟩, ⟨.privateRow 14 7, 241529264776800⟩, ⟨.privateRow 14 9, 244089733516200⟩, ⟨.privateRow 14 11, 360205747902000⟩, ⟨.privateRow 14 12, 1325322235487250⟩, ⟨.privateRow 15 0, 27041532958440⟩, ⟨.privateRow 15 3, 42024003921900⟩, ⟨.privateRow 15 6, 182713060530000⟩, ⟨.privateRow 15 8, 273129923626560⟩, ⟨.privateRow 16 0, 83525970528000⟩, ⟨.privateRow 16 2, 97446965616000⟩, ⟨.privateRow 16 5, 459218825465400⟩, ⟨.privateRow 16 7, 258408471321000⟩, ⟨.privateRow 16 8, 284423330891700⟩, ⟨.privateRow 17 0, 303022583463600⟩, ⟨.privateRow 17 2, 36542612106000⟩, ⟨.privateRow 17 4, 516468917764800⟩, ⟨.privateRow 17 5, 344414119099050⟩, ⟨.privateRow 17 10, 1746736858666800⟩, ⟨.privateRow 18 0, 912608234237700⟩, ⟨.privateRow 18 3, 402316758043200⟩, ⟨.privateRow 18 4, 687784163566500⟩, ⟨.privateRow 19 0, 392097482103600⟩, ⟨.privateRow 19 2, 479230255904400⟩, ⟨.privateRow 19 3, 1238011494419700⟩, ⟨.privateRow 19 4, 4122901566669600⟩, ⟨.privateRow 19 9, 22603693736824200⟩, ⟨.privateRow 20 0, 2286460798726104⟩, ⟨.privateRow 20 2, 2858075998407630⟩, ⟨.privateRow 20 4, 19020116378783520⟩, ⟨.privateRow 21 0, 16524569194333200⟩, ⟨.privateRow 21 2, 7804607024728800⟩, ⟨.privateRow 22 0, 17704895565357000⟩, ⟨.privateRow 22 3, 410753577116282400⟩, ⟨.privateRow 23 0, 255962204459161200⟩, ⟨.privateRow 23 2, 1090621566825991200⟩, ⟨.privateRow 23 5, 10244052574115560200⟩, ⟨.hall 14 2, 24848976232080⟩, ⟨.hall 21 2, 6323176987627500⟩, ⟨.hall 17 3, 41388067555380⟩, ⟨.hall 20 4, 5564395749112200⟩, ⟨.hall 23 4, 25562092151988231840⟩, ⟨.hall 11 7, 17420928525⟩, ⟨.hall 21 7, 608163162670012950⟩, ⟨.hall 14 8, 2639148089760⟩, ⟨.hall 19 9, 44312824329293520⟩, ⟨.hall 9 10, 247807233765⟩, ⟨.hall 10 10, 138214603800⟩, ⟨.hall 11 11, 505136624850⟩, ⟨.hall 17 11, 20106963267791400⟩, ⟨.hall 12 12, 1617960057120⟩, ⟨.hall 16 12, 11994971875286400⟩, ⟨.hall 8 13, 361026425760⟩, ⟨.hall 14 13, 40614503169240⟩, ⟨.hall 15 13, 9361434165583500⟩, ⟨.hall 10 14, 1445488464420⟩, ⟨.hall 8 15, 1602207406800⟩, ⟨.hall 13 15, 3533735845314675⟩, ⟨.hall 12 16, 2187936341791200⟩, ⟨.hall 7 17, 16565040546600⟩, ⟨.hall 11 17, 2209870964000700⟩, ⟨.hall 6 18, 18799486992000⟩, ⟨.hall 9 19, 5709417715441440⟩, ⟨.hall 5 21, 2080566825942150⟩, ⟨.hall 7 21, 643814384194800⟩, ⟨.hall 6 22, 87386595359263200⟩, ⟨.hall 4 24, 217557756707106816⟩, ⟨.hall 3 25, 481300776369012600⟩]
  caps := #[0, 131970653770737600, 0, 8032410650373200, 208927419209600, 236525440431280, 367311255811500, 57527901631200, 27837470761100, 19408187318520, 3831633964886, 35577157506150, 2298361811200, 12809718139620, 47233269200, 5106499725600, 9128960240400, 37479602160000, 0, 2063871138162600, 0, 19174281455815200, 0, 567568366409444400, 0] }

theorem case_53_29_14_checked :
    (Witness.linear .positive case_53_29_14).check 53 29 14 = true := by
  change case_53_29_14.check 53 29 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_29_15 : Certificate := {
  objectiveScale := 55506360000000
  eta := 198285387721030209600
  rows := #[⟨.count 2, 48091217660993707200⟩, ⟨.count 3, 11543591908612764000⟩, ⟨.count 4, 2719471958838835200⟩, ⟨.count 5, 699427683858103200⟩, ⟨.count 6, 179977584995208000⟩, ⟨.count 7, 46301925712442400⟩, ⟨.count 8, 11888529805152000⟩, ⟨.count 9, 3442314060385200⟩, ⟨.count 10, 1037810183810400⟩, ⟨.count 11, 333059807480400⟩, ⟨.count 12, 116615105006400⟩, ⟨.count 13, 57424104738000⟩, ⟨.count 14, 58468179369600⟩, ⟨.path 16, 9251134008480⟩, ⟨.privateRow 3 26, 500458381314091200⟩, ⟨.privateRow 6 23, 985332904676920800⟩, ⟨.privateRow 8 16, 5369327805441600⟩, ⟨.privateRow 9 13, 496065959338950⟩, ⟨.privateRow 9 14, 991174850265600⟩, ⟨.privateRow 9 15, 3734248928209800⟩, ⟨.privateRow 9 16, 3008675063394000⟩, ⟨.privateRow 9 17, 3592747813554900⟩, ⟨.privateRow 10 10, 25872169371048⟩, ⟨.privateRow 10 11, 177678300639840⟩, ⟨.privateRow 10 12, 590163185511900⟩, ⟨.privateRow 10 14, 4305206940914880⟩, ⟨.privateRow 11 8, 20027249751600⟩, ⟨.privateRow 11 9, 76635077959440⟩, ⟨.privateRow 11 10, 208118876565600⟩, ⟨.privateRow 11 11, 452214824811750⟩, ⟨.privateRow 11 12, 140353461190800⟩, ⟨.privateRow 11 13, 1842965737212600⟩, ⟨.privateRow 12 6, 12221027418600⟩, ⟨.privateRow 12 7, 37586686737600⟩, ⟨.privateRow 12 8, 91260154145160⟩, ⟨.privateRow 12 9, 181106791866000⟩, ⟨.privateRow 12 10, 329194723507650⟩, ⟨.privateRow 12 11, 170631625507200⟩, ⟨.privateRow 12 12, 895374310030200⟩, ⟨.privateRow 12 13, 569647119000960⟩, ⟨.privateRow 13 4, 7203497162400⟩, ⟨.privateRow 13 5, 13178095830900⟩, ⟨.privateRow 13 6, 57825671904000⟩, ⟨.privateRow 13 7, 81895607834040⟩, ⟨.privateRow 13 8, 17570794441200⟩, ⟨.privateRow 13 9, 558780711489000⟩, ⟨.privateRow 13 11, 821017456459200⟩, ⟨.privateRow 14 3, 20238985166400⟩, ⟨.privateRow 14 4, 12006858263400⟩, ⟨.privateRow 14 5, 59512254001200⟩, ⟨.privateRow 14 6, 80498154096360⟩, ⟨.privateRow 14 7, 29234089684800⟩, ⟨.privateRow 14 8, 410321330218800⟩, ⟨.privateRow 14 9, 201506403898800⟩, ⟨.privateRow 14 11, 692430295677120⟩, ⟨.privateRow 14 12, 4176298526400⟩, ⟨.privateRow 15 1, 6473262715920⟩, ⟨.privateRow 15 3, 42145812628920⟩, ⟨.privateRow 15 5, 179497310664672⟩, ⟨.privateRow 15 7, 335278466072550⟩, ⟨.privateRow 15 9, 799552352879280⟩, ⟨.privateRow 15 11, 551062590558480⟩, ⟨.privateRow 15 14, 19293037487483760⟩, ⟨.privateRow 16 0, 15139082158200⟩, ⟨.privateRow 16 2, 17053218982800⟩, ⟨.privateRow 16 3, 106305780672000⟩, ⟨.privateRow 16 5, 406570395431200⟩, ⟨.privateRow 16 6, 144038796051150⟩, ⟨.privateRow 16 7, 229696418952000⟩, ⟨.privateRow 16 8, 535552281864600⟩, ⟨.privateRow 16 9, 686513872764720⟩, ⟨.privateRow 17 0, 53970627110400⟩, ⟨.privateRow 17 2, 152371618963200⟩, ⟨.privateRow 17 3, 53108596260720⟩, ⟨.privateRow 17 4, 457459366364000⟩, ⟨.privateRow 17 6, 1224351517989600⟩, ⟨.privateRow 17 7, 182713060530000⟩, ⟨.privateRow 17 11, 9418249226786400⟩, ⟨.privateRow 18 0, 223838000185800⟩, ⟨.privateRow 18 1, 139842723384000⟩, ⟨.privateRow 18 2, 184592394866880⟩, ⟨.privateRow 18 3, 633714631950400⟩, ⟨.privateRow 18 4, 457043669982900⟩, ⟨.privateRow 18 5, 1223854339593600⟩, ⟨.privateRow 18 6, 25637832620400⟩, ⟨.privateRow 18 7, 312387129774720⟩, ⟨.privateRow 18 9, 4405762928767200⟩, ⟨.privateRow 19 0, 1336035864945600⟩, ⟨.privateRow 19 3, 3540979113071400⟩, ⟨.privateRow 19 4, 826608801189600⟩, ⟨.privateRow 19 5, 1822258257019200⟩, ⟨.privateRow 20 0, 4802242149536832⟩, ⟨.privateRow 20 3, 790096019787360⟩, ⟨.privateRow 20 6, 17873513618360400⟩, ⟨.privateRow 20 9, 98742731838791040⟩, ⟨.privateRow 21 0, 34847730954036000⟩, ⟨.privateRow 22 0, 177639118839081900⟩, ⟨.privateRow 22 4, 402491292519115800⟩, ⟨.privateRow 22 7, 878162820041707200⟩, ⟨.privateRow 23 0, 2574460433255911200⟩, ⟨.privateRow 23 2, 706307300420641920⟩, ⟨.privateRow 23 3, 1519080039507630600⟩, ⟨.privateRow 23 4, 3981634291586952000⟩, ⟨.hall 14 2, 3702984693408⟩, ⟨.hall 19 2, 2952689461481760⟩, ⟨.hall 21 2, 64580714300302200⟩, ⟨.hall 18 3, 61530798288960⟩, ⟨.hall 20 3, 9587140727907600⟩, ⟨.hall 22 5, 143437757088225600⟩, ⟨.hall 11 8, 558467069160⟩, ⟨.hall 18 8, 506445801301440⟩, ⟨.hall 10 9, 508553791200⟩, ⟨.hall 15 9, 6809849013240⟩, ⟨.hall 19 9, 9779847074197200⟩, ⟨.hall 18 10, 16206695926948800⟩, ⟨.hall 17 11, 15378755290298400⟩, ⟨.hall 12 12, 2549606265360⟩, ⟨.hall 13 12, 7930521277965⟩, ⟨.hall 14 12, 36783552405600⟩, ⟨.hall 16 12, 2218792447872000⟩, ⟨.hall 11 13, 4272492797430⟩, ⟨.hall 15 13, 2057871098883600⟩, ⟨.hall 9 14, 5581893427110⟩, ⟨.hall 10 14, 5188623520080⟩, ⟨.hall 8 15, 2934447115600⟩, ⟨.hall 11 15, 17912192147850⟩, ⟨.hall 13 15, 13770300316172400⟩, ⟨.hall 12 16, 15594619951310400⟩, ⟨.hall 9 17, 149138734284540⟩, ⟨.hall 10 18, 17468907222967200⟩, ⟨.hall 8 20, 93083197689081600⟩, ⟨.hall 7 21, 265247761291858800⟩, ⟨.hall 6 22, 379355892427512000⟩, ⟨.hall 4 24, 965304629833864320⟩, ⟨.hall 3 25, 886334310302641200⟩]
  caps := #[0, 0, 32458571810683200, 5231552138904000, 0, 143141577371520, 85985346326880, 36013009032000, 18937725206400, 18898805452800, 0, 7963178307630, 9612408432660, 0, 16291408068390, 23020391360148, 2022925020480, 21438048499140, 98775662324300, 203540315518800, 429735152225808, 0, 0, 0, 0] }

theorem case_53_29_15_checked :
    (Witness.linear .positive case_53_29_15).check 53 29 15 = true := by
  change case_53_29_15.check 53 29 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_29_16 : Certificate := {
  objectiveScale := 1657656000000
  eta := 4364483742701082000
  rows := #[⟨.count 2, 1038687206500944000⟩, ⟨.count 3, 272383008697800000⟩, ⟨.count 4, 72116644207608000⟩, ⟨.count 5, 19352164237005600⟩, ⟨.count 6, 5292012740414400⟩, ⟨.count 7, 1487752807741200⟩, ⟨.count 8, 434763385056000⟩, ⟨.count 9, 135769858824600⟩, ⟨.count 10, 45537716624400⟩, ⟨.count 11, 16343783656200⟩, ⟨.count 12, 6523921958400⟩, ⟨.count 13, 3533791060800⟩, ⟨.count 14, 2248776129600⟩, ⟨.count 15, 2529873145800⟩, ⟨.path 14, 276276873600⟩, ⟨.privateRow 3 26, 30506896974153600⟩, ⟨.privateRow 5 21, 811960778308680⟩, ⟨.privateRow 6 19, 366454133004960⟩, ⟨.privateRow 6 20, 1311397894006200⟩, ⟨.privateRow 7 17, 149275901174400⟩, ⟨.privateRow 7 18, 484145438016240⟩, ⟨.privateRow 7 19, 963580493175300⟩, ⟨.privateRow 8 15, 58093383348000⟩, ⟨.privateRow 8 16, 182119633495800⟩, ⟨.privateRow 8 17, 359729221531680⟩, ⟨.privateRow 8 18, 559523610746100⟩, ⟨.privateRow 9 13, 22218376655475⟩, ⟨.privateRow 9 14, 69886072456200⟩, ⟨.privateRow 9 15, 139127406518100⟩, ⟨.privateRow 9 16, 216913197501000⟩, ⟨.privateRow 9 17, 275006580849000⟩, ⟨.privateRow 10 10, 146170448424⟩, ⟨.privateRow 10 11, 8364197882040⟩, ⟨.privateRow 10 12, 27456151057335⟩, ⟨.privateRow 10 13, 55930274880480⟩, ⟨.privateRow 10 14, 88433121296520⟩, ⟨.privateRow 10 15, 114923704103208⟩, ⟨.privateRow 10 16, 119142970316370⟩, ⟨.privateRow 11 8, 102217096800⟩, ⟨.privateRow 11 9, 3308913447840⟩, ⟨.privateRow 11 10, 11025249635400⟩, ⟨.privateRow 11 11, 23451522494400⟩, ⟨.privateRow 11 12, 38183300812800⟩, ⟨.privateRow 11 13, 51039186798600⟩, ⟨.privateRow 11 14, 40558283766000⟩, ⟨.privateRow 12 6, 22652506800⟩, ⟨.privateRow 12 7, 1396218146400⟩, ⟨.privateRow 12 8, 4675477403520⟩, ⟨.privateRow 12 9, 10238933073600⟩, ⟨.privateRow 12 10, 17554276988325⟩, ⟨.privateRow 12 11, 15940892642400⟩, ⟨.privateRow 13 5, 594628303500⟩, ⟨.privateRow 13 6, 2137572914400⟩, ⟨.privateRow 13 7, 4774015808100⟩, ⟨.privateRow 13 8, 6006689719800⟩, ⟨.privateRow 14 3, 194605626600⟩, ⟨.privateRow 14 4, 1198008711900⟩, ⟨.privateRow 14 5, 1788799194000⟩, ⟨.privateRow 15 1, 164642538060⟩, ⟨.privateRow 15 2, 467053503840⟩, ⟨.privateRow 16 0, 147241294200⟩, ⟨.privateRow 17 0, 129737084400⟩, ⟨.privateRow 18 0, 265480515300⟩, ⟨.privateRow 19 0, 868845322800⟩, ⟨.privateRow 20 0, 3112948670832⟩, ⟨.privateRow 21 0, 17294159282400⟩, ⟨.privateRow 22 0, 113492920290750⟩, ⟨.privateRow 23 0, 1141414512638400⟩, ⟨.privateRow 24 0, 30627956089130400⟩, ⟨.hall 8 17, 1122384142880⟩, ⟨.hall 8 18, 2170998910080⟩, ⟨.hall 7 19, 13980134979720⟩, ⟨.hall 9 19, 312017687982000⟩, ⟨.hall 7 20, 86574230379000⟩, ⟨.hall 6 22, 10666657527926400⟩, ⟨.hall 5 23, 20449262466482850⟩, ⟨.hall 4 24, 33117623259424704⟩, ⟨.hall 3 25, 37463139965512800⟩, ⟨.assumptionRow 16, 2118867470720⟩]
  caps := #[0, 9286610642290800, 1921506190531200, 131776766867200, 0, 18702321477840, 8140063911980, 1442045004400, 142642980480, 359063780075, 409392787713, 0, 179907624400, 0, 475551612900, 0, 492230819080, 0, 4513168760100, 0, 59146024745808, 0, 0, 25111119278044800, 0] }

theorem case_53_29_16_checked :
    (Witness.linear .conditional case_53_29_16).check 53 29 16 = true := by
  change case_53_29_16.check 53 29 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_29_17 : Certificate := {
  objectiveScale := 2008314000000
  eta := 1699851562946737200
  rows := #[⟨.count 2, 471404193719659200⟩, ⟨.count 3, 136191504348900000⟩, ⟨.count 4, 40260802809427200⟩, ⟨.count 5, 12218323533015600⟩, ⟨.count 6, 3809266136676000⟩, ⟨.count 7, 1220148448318800⟩, ⟨.count 8, 401781335155200⟩, ⟨.count 9, 136613149873200⟩, ⟨.count 10, 47786492754000⟩, ⟨.count 11, 17227231421400⟩, ⟨.count 12, 7339412203200⟩, ⟨.count 13, 3533791060800⟩, ⟨.count 14, 1686582097200⟩, ⟨.count 15, 1686582097200⟩, ⟨.count 16, 1499184086400⟩, ⟨.path 13, 173491718400⟩, ⟨.privateRow 2 27, 69911638899102000⟩, ⟨.privateRow 5 21, 1971534158193600⟩, ⟨.privateRow 6 19, 595283166878400⟩, ⟨.privateRow 6 20, 1942520930450100⟩, ⟨.privateRow 7 17, 178554609433200⟩, ⟨.privateRow 7 18, 648257907417120⟩, ⟨.privateRow 7 19, 1382736301046100⟩, ⟨.privateRow 8 15, 52899781334400⟩, ⟨.privateRow 8 16, 218037585565800⟩, ⟨.privateRow 8 17, 493981156468800⟩, ⟨.privateRow 8 18, 857299049907300⟩, ⟨.privateRow 9 13, 15284650255875⟩, ⟨.privateRow 9 14, 73888358544000⟩, ⟨.privateRow 9 15, 180339352393200⟩, ⟨.privateRow 9 16, 323861242264560⟩, ⟨.privateRow 9 17, 462217193638200⟩, ⟨.privateRow 10 11, 4178975640840⟩, ⟨.privateRow 10 12, 25193320076925⟩, ⟨.privateRow 10 13, 67391001798120⟩, ⟨.privateRow 10 14, 128058430680180⟩, ⟨.privateRow 10 15, 193518429832728⟩, ⟨.privateRow 10 16, 230429279029950⟩, ⟨.privateRow 11 9, 983839556700⟩, ⟨.privateRow 11 10, 8602461067200⟩, ⟨.privateRow 11 11, 25750494519750⟩, ⟨.privateRow 11 12, 52507775291400⟩, ⟨.privateRow 11 13, 84007851127200⟩, ⟨.privateRow 11 14, 109378864675080⟩, ⟨.privateRow 11 15, 108433173999150⟩, ⟨.privateRow 12 7, 111203215200⟩, ⟨.privateRow 12 8, 2905183997100⟩, ⟨.privateRow 12 9, 10061488437000⟩, ⟨.privateRow 12 10, 22370766246675⟩, ⟨.privateRow 12 11, 38323187397000⟩, ⟨.privateRow 12 12, 53561852328600⟩, ⟨.privateRow 12 13, 11219786618040⟩, ⟨.privateRow 13 6, 837113092200⟩, ⟨.privateRow 13 7, 4016289455640⟩, ⟨.privateRow 13 8, 9910471725000⟩, ⟨.privateRow 13 9, 18488692893825⟩, ⟨.privateRow 13 10, 10547977987800⟩, ⟨.privateRow 14 4, 217515548250⟩, ⟨.privateRow 14 5, 1533256452000⟩, ⟨.privateRow 14 6, 4553771662440⟩, ⟨.privateRow 14 7, 6273371504400⟩, ⟨.privateRow 15 2, 17298277920⟩, ⟨.privateRow 15 3, 641838186990⟩, ⟨.privateRow 15 4, 2069896210200⟩, ⟨.privateRow 15 5, 404779703328⟩, ⟨.privateRow 16 1, 252266553000⟩, ⟨.privateRow 16 2, 390412522500⟩, ⟨.privateRow 17 0, 100906621200⟩, ⟨.hall 9 15, 320737787370⟩, ⟨.hall 8 16, 247057050240⟩, ⟨.hall 8 17, 2269316329280⟩, ⟨.hall 10 18, 95484218029200⟩, ⟨.hall 7 19, 11260511207400⟩, ⟨.hall 7 20, 303840725861400⟩, ⟨.hall 6 22, 17712820406080800⟩, ⟨.hall 5 23, 32207129008604550⟩, ⟨.hall 4 24, 52998988770471744⟩, ⟨.hall 3 25, 76204384817992200⟩, ⟨.hall 2 26, 79455132463106400⟩, ⟨.assumptionRow 17, 1818481785120⟩]
  caps := #[0, 0, 1676804451537600, 242876882999520, 81882634125600, 4007237406480, 3651584096160, 804880276200, 107381514240, 779777478480, 145137497505, 0, 98838870900, 317959034580, 131899687920, 959286842892, 319297698720, 0, 2008314000000, 0, 0, 0, 0, 0, 0] }

theorem case_53_29_17_checked :
    (Witness.linear .conditional case_53_29_17).check 53 29 17 = true := by
  change case_53_29_17.check 53 29 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_29_18 : Certificate := {
  objectiveScale := 5198186070000000
  eta := 10202738790476985152400
  rows := #[⟨.count 2, 1619285390279412055200⟩, ⟨.count 3, 324872304005900851200⟩, ⟨.count 4, 85730191334890502400⟩, ⟨.count 5, 26105810143331318400⟩, ⟨.count 6, 8243940045262521600⟩, ⟨.count 7, 2617224793176193200⟩, ⟨.count 8, 831179140365974400⟩, ⟨.count 9, 271093616684490600⟩, ⟨.count 10, 91674169893306000⟩, ⟨.count 11, 36357851052923400⟩, ⟨.count 12, 12664563501744000⟩, ⟨.count 13, 6859971896778000⟩, ⟨.count 14, 3492349329268800⟩, ⟨.count 15, 2619261996951600⟩, ⟨.count 16, 2328232886179200⟩, ⟨.count 17, 4947494883130800⟩, ⟨.path 4, 2487082148591040000⟩, ⟨.path 13, 523037666642400⟩, ⟨.privateRow 2 27, 161308123169596603200⟩, ⟨.privateRow 5 21, 4286509566744525120⟩, ⟨.privateRow 6 19, 1146263885923075920⟩, ⟨.privateRow 6 20, 4495152493815984000⟩, ⟨.privateRow 7 17, 292726780585239000⟩, ⟨.privateRow 7 18, 1400847836909320800⟩, ⟨.privateRow 7 19, 3416245216801817400⟩, ⟨.privateRow 8 15, 68350265444260800⟩, ⟨.privateRow 8 16, 430577569387765800⟩, ⟨.privateRow 8 17, 1162486680069274560⟩, ⟨.privateRow 8 18, 2299712033323504800⟩, ⟨.privateRow 9 13, 12750712915715775⟩, ⟨.privateRow 9 14, 128967471659426400⟩, ⟨.privateRow 9 15, 397351745907916800⟩, ⟨.privateRow 9 16, 839910013689146400⟩, ⟨.privateRow 9 17, 1417675555850053500⟩, ⟨.privateRow 10 10, 602430259298868⟩, ⟨.privateRow 10 12, 36647840774014470⟩, ⟨.privateRow 10 13, 135390899890045800⟩, ⟨.privateRow 10 14, 313482006668490660⟩, ⟨.privateRow 10 15, 559928367961666704⟩, ⟨.privateRow 10 16, 798853081886930070⟩, ⟨.privateRow 11 10, 7989442017156600⟩, ⟨.privateRow 11 11, 45322587054394650⟩, ⟨.privateRow 11 12, 118918058283367200⟩, ⟨.privateRow 11 13, 229486847740850700⟩, ⟨.privateRow 11 14, 354922473263117760⟩, ⟨.privateRow 11 15, 433253997817190550⟩, ⟨.privateRow 12 8, 1456424802700560⟩, ⟨.privateRow 12 9, 13573363197471000⟩, ⟨.privateRow 12 10, 45262622265087150⟩, ⟨.privateRow 12 11, 97087448416048200⟩, ⟨.privateRow 12 12, 162642897803994300⟩, ⟨.privateRow 12 13, 220278974507000640⟩, ⟨.privateRow 12 14, 157383586016464500⟩, ⟨.privateRow 13 7, 3862691868031920⟩, ⟨.privateRow 13 8, 16364257746929400⟩, ⟨.privateRow 13 9, 41872213077641100⟩, ⟨.privateRow 13 10, 78060449440809000⟩, ⟨.privateRow 13 11, 100736048853455400⟩, ⟨.privateRow 14 5, 578278622703600⟩, ⟨.privateRow 14 6, 5874630478877160⟩, ⟨.privateRow 14 7, 17766634286200800⟩, ⟨.privateRow 14 8, 38587341919376250⟩, ⟨.privateRow 14 9, 18361561141895400⟩, ⟨.privateRow 15 4, 1619180143570080⟩, ⟨.privateRow 15 5, 7604590664482812⟩, ⟨.privateRow 15 6, 15502150633809840⟩, ⟨.privateRow 16 2, 254650471925850⟩, ⟨.privateRow 16 3, 2870605319891400⟩, ⟨.privateRow 16 4, 3579658062500520⟩, ⟨.privateRow 17 1, 1042854313601100⟩, ⟨.privateRow 17 2, 423315070214400⟩, ⟨.privateRow 18 0, 235594994434800⟩, ⟨.hall 10 15, 795205509523425⟩, ⟨.hall 9 16, 4182574872015540⟩, ⟨.hall 10 16, 6766351740548400⟩, ⟨.hall 9 17, 10485855447737670⟩, ⟨.hall 8 18, 37083673278812160⟩, ⟨.hall 8 19, 342776858373549600⟩, ⟨.hall 7 21, 28407616074412848000⟩, ⟨.hall 5 22, 3869497975904911350⟩, ⟨.hall 6 22, 52421258858667098400⟩, ⟨.hall 4 24, 139347013253959615104⟩, ⟨.hall 3 25, 194650052340074007600⟩, ⟨.hall 2 26, 202209613090092608000⟩, ⟨.assumptionRow 18, 2887925045793480⟩]
  caps := #[0, 0, 2138222936721853800, 350033249151265680, 0, 19261649762197920, 3884124408927840, 1031797617570720, 308628894941640, 0, 64034025636672, 171084816240000, 238534385861520, 45307864631400, 762502903884930, 268663048841880, 2254072885851150, 0, 2210531761681320, 5198186070000000, 0, 0, 0, 0, 0] }

theorem case_53_29_18_checked :
    (Witness.linear .conditional case_53_29_18).check 53 29 18 = true := by
  change case_53_29_18.check 53 29 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_30_1_checked :
    (Witness.rising).check 53 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_30_2_checked :
    (Witness.rising).check 53 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_30_3_checked :
    (Witness.rising).check 53 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_30_4_checked :
    (Witness.rising).check 53 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_30_5_checked :
    (Witness.rising).check 53 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_30_6_checked :
    (Witness.rising).check 53 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_30_7_checked :
    (Witness.rising).check 53 30 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_30_8_checked :
    (Witness.rising).check 53 30 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_30_9_checked :
    (Witness.rising).check 53 30 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_30_10_checked :
    (Witness.rising).check 53 30 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_30_11_checked :
    (Witness.linear .positive case_53_30_11).check 53 30 11 = true := by
  change case_53_30_11.check 53 30 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_30_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_30_12_checked :
    (Witness.linear .positive case_53_30_12).check 53 30 12 = true := by
  change case_53_30_12.check 53 30 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_30_13 : Certificate := {
  objectiveScale := 9467640000000
  eta := 28563898178775960000
  rows := #[⟨.count 2, 5832628159582224000⟩, ⟨.count 3, 925687169749742400⟩, ⟨.count 4, 161624294989597440⟩, ⟨.count 5, 29736851776632000⟩, ⟨.count 6, 5827221459259200⟩, ⟨.count 7, 1236826871280000⟩, ⟨.count 8, 284470180394400⟩, ⟨.count 9, 74209612276800⟩, ⟨.count 10, 24736537425600⟩, ⟨.count 11, 10465458141600⟩, ⟨.count 12, 8970392692800⟩, ⟨.path 13, 746615565696⟩, ⟨.path 14, 2263642180800⟩, ⟨.privateRow 5 21, 442147937527296⟩, ⟨.privateRow 5 22, 2090590791569280⟩, ⟨.privateRow 5 23, 3003722401680000⟩, ⟨.privateRow 6 18, 151616464084800⟩, ⟨.privateRow 6 19, 510076563396400⟩, ⟨.privateRow 6 20, 766282959361920⟩, ⟨.privateRow 6 21, 1339993938082800⟩, ⟨.privateRow 6 22, 1465149038152800⟩, ⟨.privateRow 7 15, 38217295916800⟩, ⟨.privateRow 7 16, 131780958309000⟩, ⟨.privateRow 7 17, 217580563886400⟩, ⟨.privateRow 7 18, 320986021356000⟩, ⟨.privateRow 7 19, 444786501519360⟩, ⟨.privateRow 7 20, 509160395343600⟩, ⟨.privateRow 7 21, 431515152868800⟩, ⟨.privateRow 8 12, 8058114464400⟩, ⟨.privateRow 8 13, 34734221301780⟩, ⟨.privateRow 8 14, 62070385577200⟩, ⟨.privateRow 8 15, 93535032140550⟩, ⟨.privateRow 8 16, 117940276654200⟩, ⟨.privateRow 8 17, 163106543650050⟩, ⟨.privateRow 8 18, 158416908429780⟩, ⟨.privateRow 8 19, 66092935934025⟩, ⟨.privateRow 9 9, 1226255701440⟩, ⟨.privateRow 9 10, 9253297333280⟩, ⟨.privateRow 9 11, 18240073051200⟩, ⟨.privateRow 9 12, 28969233829536⟩, ⟨.privateRow 9 13, 38479058217600⟩, ⟨.privateRow 9 14, 46552789182900⟩, ⟨.privateRow 9 15, 34788209776320⟩, ⟨.privateRow 10 7, 2372688283680⟩, ⟨.privateRow 10 8, 5599699680960⟩, ⟨.privateRow 10 9, 9526511734740⟩, ⟨.privateRow 10 10, 13412343344400⟩, ⟨.privateRow 10 11, 8975829294432⟩, ⟨.privateRow 11 4, 416239812450⟩, ⟨.privateRow 11 5, 1821261546720⟩, ⟨.privateRow 11 6, 3339626716800⟩, ⟨.privateRow 11 7, 2174640652800⟩, ⟨.privateRow 12 2, 681573954600⟩, ⟨.privateRow 12 3, 576223141725⟩, ⟨.privateRow 13 0, 234075903600⟩, ⟨.privateRow 14 0, 135115540560⟩, ⟨.privateRow 15 0, 188959660890⟩, ⟨.privateRow 16 0, 377919321780⟩, ⟨.privateRow 17 0, 841378824000⟩, ⟨.privateRow 18 0, 2310555693600⟩, ⟨.privateRow 19 0, 8009926404480⟩, ⟨.privateRow 20 0, 41505982277760⟩, ⟨.privateRow 21 0, 266330052948960⟩, ⟨.privateRow 22 1, 2996213095675800⟩, ⟨.privateRow 23 0, 21972229368289200⟩, ⟨.privateRow 23 3, 52733350483894080⟩, ⟨.hall 21 8, 887766843163200⟩, ⟨.hall 6 23, 760943008425600⟩, ⟨.hall 5 24, 4159554781846464⟩, ⟨.hall 4 25, 12098993833967040⟩, ⟨.hall 3 26, 22659191806451200⟩]
  caps := #[0, 24691888997717760, 0, 0, 73448597878656, 5957481271872, 5061939442560, 4866586110672, 1572556744759, 0, 0, 0, 497247307200, 765683935296, 0, 2645435252460, 0, 0, 0, 144178675280640, 0, 5326601058979200, 0, 0] }

theorem case_53_30_13_checked :
    (Witness.linear .positive case_53_30_13).check 53 30 13 = true := by
  change case_53_30_13.check 53 30 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_30_14 : Certificate := {
  objectiveScale := 109403840000000
  eta := 474887790812231596800
  rows := #[⟨.count 2, 99260726497617484800⟩, ⟨.count 3, 18963460712974377600⟩, ⟨.count 4, 3884959941198336000⟩, ⟨.count 5, 808940671966627200⟩, ⟨.count 6, 171244944776505600⟩, ⟨.count 7, 39115211998262400⟩, ⟨.count 8, 9471845057875200⟩, ⟨.count 9, 2420582625901440⟩, ⟨.count 10, 714147048014400⟩, ⟨.count 11, 254432956377600⟩, ⟨.count 12, 95412358641600⟩, ⟨.count 13, 112760060212800⟩, ⟨.path 15, 28653300093600⟩, ⟨.privateRow 3 27, 250903662869059200⟩, ⟨.privateRow 7 16, 394660210744800⟩, ⟨.privateRow 7 17, 4141694910038400⟩, ⟨.privateRow 7 18, 7045415614036800⟩, ⟨.privateRow 7 19, 10689653708173440⟩, ⟨.privateRow 8 14, 747905461102800⟩, ⟨.privateRow 8 15, 1823933126740725⟩, ⟨.privateRow 8 16, 3531582441387000⟩, ⟨.privateRow 8 17, 5722573055799600⟩, ⟨.privateRow 8 18, 7215704186450760⟩, ⟨.privateRow 8 22, 163816875809987400⟩, ⟨.privateRow 9 11, 80260864407360⟩, ⟨.privateRow 9 12, 420386209667424⟩, ⟨.privateRow 9 13, 862730468920320⟩, ⟨.privateRow 9 14, 1395927782449200⟩, ⟨.privateRow 9 15, 2455663533523200⟩, ⟨.privateRow 9 16, 3146562519740640⟩, ⟨.privateRow 9 17, 3517445670875136⟩, ⟨.privateRow 10 9, 87389046664920⟩, ⟨.privateRow 10 11, 809993099195280⟩, ⟨.privateRow 10 12, 409694885439840⟩, ⟨.privateRow 10 13, 988060027614660⟩, ⟨.privateRow 10 15, 4387619231835840⟩, ⟨.privateRow 11 6, 9086891299200⟩, ⟨.privateRow 11 7, 51820698283200⟩, ⟨.privateRow 11 8, 80955940665600⟩, ⟨.privateRow 11 9, 107240336985600⟩, ⟨.privateRow 11 10, 540380903942880⟩, ⟨.privateRow 11 11, 304869792427200⟩, ⟨.privateRow 11 13, 1302729779894400⟩, ⟨.privateRow 11 14, 1314088394018400⟩, ⟨.privateRow 11 16, 774141182614800⟩, ⟨.privateRow 12 4, 11661510500640⟩, ⟨.privateRow 12 5, 30478947899400⟩, ⟨.privateRow 12 6, 56268826891200⟩, ⟨.privateRow 12 7, 72663578687700⟩, ⟨.privateRow 12 8, 85051925758800⟩, ⟨.privateRow 12 9, 447377948297280⟩, ⟨.privateRow 12 10, 215561254708800⟩, ⟨.privateRow 12 12, 719378894520000⟩, ⟨.privateRow 12 15, 404839938402900⟩, ⟨.privateRow 13 3, 43754758407360⟩, ⟨.privateRow 13 4, 22923748504800⟩, ⟨.privateRow 13 5, 52265511144000⟩, ⟨.privateRow 13 6, 63126358495200⟩, ⟨.privateRow 13 7, 79378876886400⟩, ⟨.privateRow 13 8, 372686455421280⟩, ⟨.privateRow 13 9, 257645493705600⟩, ⟨.privateRow 13 11, 441540309038400⟩, ⟨.privateRow 13 12, 136372209573600⟩, ⟨.privateRow 13 13, 181572609778560⟩, ⟨.privateRow 14 1, 23491679211000⟩, ⟨.privateRow 14 2, 7767915259104⟩, ⟨.privateRow 14 3, 95846051180880⟩, ⟨.privateRow 14 5, 102736943749440⟩, ⟨.privateRow 14 6, 69364521888480⟩, ⟨.privateRow 14 7, 377746201712880⟩, ⟨.privateRow 14 8, 303616902869280⟩, ⟨.privateRow 14 11, 995420753767440⟩, ⟨.privateRow 15 0, 52621361432640⟩, ⟨.privateRow 15 2, 127794734907840⟩, ⟨.privateRow 15 4, 56519240057280⟩, ⟨.privateRow 15 5, 257259989226240⟩, ⟨.privateRow 15 6, 354317166979776⟩, ⟨.privateRow 15 7, 429416295147840⟩, ⟨.privateRow 15 8, 135207664792200⟩, ⟨.privateRow 15 15, 11635167694550400⟩, ⟨.privateRow 16 0, 193675844161800⟩, ⟨.privateRow 16 2, 223472127879000⟩, ⟨.privateRow 16 4, 328883508954000⟩, ⟨.privateRow 16 5, 505384325425980⟩, ⟨.privateRow 16 7, 350809076217600⟩, ⟨.privateRow 16 9, 84048007843800⟩, ⟨.privateRow 16 10, 173211981382440⟩, ⟨.privateRow 17 0, 828696950452800⟩, ⟨.privateRow 17 2, 64732627159200⟩, ⟨.privateRow 17 3, 530769576355200⟩, ⟨.privateRow 17 4, 949690284903360⟩, ⟨.privateRow 17 6, 1409500752660000⟩, ⟨.privateRow 17 8, 555447704011200⟩, ⟨.privateRow 17 9, 486121148472960⟩, ⟨.privateRow 17 11, 2012975889724800⟩, ⟨.privateRow 17 13, 851964899385600⟩, ⟨.privateRow 18 0, 3238558880356800⟩, ⟨.privateRow 18 4, 3534076619673600⟩, ⟨.privateRow 18 6, 2069057612793600⟩, ⟨.privateRow 19 0, 13674036635138880⟩, ⟨.privateRow 19 6, 25729339961445120⟩, ⟨.privateRow 20 0, 56729244595907520⟩, ⟨.privateRow 20 5, 128891639715798960⟩, ⟨.privateRow 21 3, 1131957078105110400⟩, ⟨.privateRow 22 2, 3957802940095804800⟩, ⟨.hall 18 2, 290442579336000⟩, ⟨.hall 17 3, 111956925880800⟩, ⟨.hall 15 4, 5686191070560⟩, ⟨.hall 20 6, 2119769809185600⟩, ⟨.hall 21 7, 1277113133447751600⟩, ⟨.hall 19 10, 33110454044304000⟩, ⟨.hall 12 11, 56393320500⟩, ⟨.hall 18 11, 16293828700749600⟩, ⟨.hall 8 12, 21551034960⟩, ⟨.hall 9 12, 22537490976⟩, ⟨.hall 11 12, 22452130800⟩, ⟨.hall 13 16, 2429868748507200⟩, ⟨.hall 12 17, 2560231623549600⟩, ⟨.hall 11 18, 3808124840520000⟩, ⟨.hall 9 20, 488626927588800⟩, ⟨.hall 7 21, 321690536294400⟩, ⟨.hall 8 21, 5409635413946400⟩, ⟨.hall 6 23, 302660530506734400⟩, ⟨.hall 5 24, 688762503259294464⟩, ⟨.hall 4 25, 977963954428581120⟩, ⟨.hall 3 26, 909188541794332800⟩]
  caps := #[0, 468305312068339200, 10503264239395200, 4879435332844800, 2097422590099200, 446987439953600, 104534001572000, 0, 0, 11041421664000, 7480315135800, 0, 75321198133920, 0, 17216025458632, 108787188151824, 18572116366440, 0, 184195208433600, 0, 23710764035059920, 0, 0, 0] }

theorem case_53_30_14_checked :
    (Witness.linear .positive case_53_30_14).check 53 30 14 = true := by
  change case_53_30_14.check 53 30 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_30_15 : Certificate := {
  objectiveScale := 7949760000000
  eta := 35107627579731907200
  rows := #[⟨.count 2, 8649431646862406400⟩, ⟨.count 3, 2123238523418812800⟩, ⟨.count 4, 515296769978390400⟩, ⟨.count 5, 122966933811321600⟩, ⟨.count 6, 32043346493558400⟩, ⟨.count 7, 8399928436099200⟩, ⟨.count 8, 2212046119483200⟩, ⟨.count 9, 584681793696000⟩, ⟨.count 10, 175404538108800⟩, ⟨.count 11, 56540656972800⟩, ⟨.count 12, 21202746364800⟩, ⟨.count 13, 8352597052800⟩, ⟨.count 14, 5846817936960⟩, ⟨.path 15, 813047508000⟩, ⟨.path 16, 632363659200⟩, ⟨.privateRow 8 15, 129117229441200⟩, ⟨.privateRow 8 16, 486016741009800⟩, ⟨.privateRow 8 17, 949498871220900⟩, ⟨.privateRow 9 13, 70594912868480⟩, ⟨.privateRow 9 14, 212759208261600⟩, ⟨.privateRow 9 15, 522222929067840⟩, ⟨.privateRow 9 16, 874099281575520⟩, ⟨.privateRow 9 17, 839343197172480⟩, ⟨.privateRow 9 19, 340631282031040⟩, ⟨.privateRow 10 11, 32282787609072⟩, ⟨.privateRow 10 12, 88955158612320⟩, ⟨.privateRow 10 13, 213147836041140⟩, ⟨.privateRow 10 14, 404862311430720⟩, ⟨.privateRow 10 15, 624287024721360⟩, ⟨.privateRow 10 17, 2029889898756720⟩, ⟨.privateRow 10 19, 1891445602606560⟩, ⟨.privateRow 11 8, 1472412942000⟩, ⟨.privateRow 11 9, 12704124888000⟩, ⟨.privateRow 11 10, 37843689723840⟩, ⟨.privateRow 11 11, 89736876028800⟩, ⟨.privateRow 11 12, 172071530631000⟩, ⟨.privateRow 11 13, 50161475707200⟩, ⟨.privateRow 11 14, 906417407095200⟩, ⟨.privateRow 12 6, 1404455421600⟩, ⟨.privateRow 12 7, 5914191983700⟩, ⟨.privateRow 12 8, 15527263752000⟩, ⟨.privateRow 12 9, 39931838987040⟩, ⟨.privateRow 12 10, 78332368514400⟩, ⟨.privateRow 12 11, 136014145517250⟩, ⟨.privateRow 12 12, 74672370630000⟩, ⟨.privateRow 12 13, 157302782637000⟩, ⟨.privateRow 12 14, 599154274358640⟩, ⟨.privateRow 13 4, 1032601284000⟩, ⟨.privateRow 13 5, 3212537328000⟩, ⟨.privateRow 13 6, 7335293565600⟩, ⟨.privateRow 13 7, 17844184612800⟩, ⟨.privateRow 13 8, 38935952415360⟩, ⟨.privateRow 13 9, 70568736638400⟩, ⟨.privateRow 13 11, 320198184820800⟩, ⟨.privateRow 13 13, 347082532917120⟩, ⟨.privateRow 13 15, 499656639081600⟩, ⟨.privateRow 14 2, 779575724928⟩, ⟨.privateRow 14 4, 7934967200160⟩, ⟨.privateRow 14 5, 7308522421200⟩, ⟨.privateRow 14 6, 20008266576480⟩, ⟨.privateRow 14 7, 41053014514512⟩, ⟨.privateRow 14 8, 71553914752320⟩, ⟨.privateRow 14 9, 21403529947800⟩, ⟨.privateRow 14 10, 224267230867680⟩, ⟨.privateRow 14 11, 160161048487440⟩, ⟨.privateRow 14 13, 578208530980080⟩, ⟨.privateRow 14 15, 437676085566720⟩, ⟨.privateRow 15 0, 974469656160⟩, ⟨.privateRow 15 2, 1624116093600⟩, ⟨.privateRow 15 3, 10394342999040⟩, ⟨.privateRow 15 4, 9474010546000⟩, ⟨.privateRow 15 5, 24922799690880⟩, ⟨.privateRow 15 6, 49632987820416⟩, ⟨.privateRow 15 8, 219742907464080⟩, ⟨.privateRow 15 9, 100973617704960⟩, ⟨.privateRow 15 10, 255635873132640⟩, ⟨.privateRow 16 0, 3167026382520⟩, ⟨.privateRow 16 2, 3654261210600⟩, ⟨.privateRow 16 3, 42531540201150⟩, ⟨.privateRow 16 4, 23697330274800⟩, ⟨.privateRow 16 5, 71867137141800⟩, ⟨.privateRow 16 6, 25444485466400⟩, ⟨.privateRow 16 7, 220626020589975⟩, ⟨.privateRow 16 8, 254058160356000⟩, ⟨.privateRow 16 10, 532791284505480⟩, ⟨.privateRow 17 0, 16506322747200⟩, ⟨.privateRow 17 2, 74013290551200⟩, ⟨.privateRow 17 4, 227190639836160⟩, ⟨.privateRow 17 5, 28770056515200⟩, ⟨.privateRow 17 6, 273895578356400⟩, ⟨.privateRow 17 8, 1192565245872000⟩, ⟨.privateRow 17 11, 858461363760000⟩, ⟨.privateRow 18 0, 81919701864000⟩, ⟨.privateRow 18 2, 268211172028800⟩, ⟨.privateRow 18 3, 269000028417120⟩, ⟨.privateRow 18 5, 938739102100800⟩, ⟨.privateRow 18 6, 94662766598400⟩, ⟨.privateRow 18 7, 1192487907010400⟩, ⟨.privateRow 18 10, 5335298706337600⟩, ⟨.privateRow 18 12, 7367918666908800⟩, ⟨.privateRow 19 0, 492246386311680⟩, ⟨.privateRow 19 2, 1613053542836736⟩, ⟨.privateRow 19 4, 1501588135167120⟩, ⟨.privateRow 19 5, 1821582094400640⟩, ⟨.privateRow 19 7, 5054991736354560⟩, ⟨.privateRow 20 0, 3691202469383520⟩, ⟨.privateRow 20 1, 2549504961411408⟩, ⟨.privateRow 20 4, 12545183143452960⟩, ⟨.privateRow 20 7, 37635549430358880⟩, ⟨.privateRow 21 0, 41547488260037760⟩, ⟨.privateRow 21 3, 27364301173123200⟩, ⟨.privateRow 21 5, 100361465147623680⟩, ⟨.privateRow 22 0, 516196066261075200⟩, ⟨.privateRow 23 1, 13443580129855075200⟩, ⟨.hall 15 1, 1218087070200⟩, ⟨.hall 14 3, 70765058364⟩, ⟨.hall 21 8, 117508047604147200⟩, ⟨.hall 20 9, 169427419657816320⟩, ⟨.hall 18 11, 1940586715267200⟩, ⟨.hall 9 13, 3803491692⟩, ⟨.hall 16 13, 2972132451288000⟩, ⟨.hall 15 14, 2478401158833600⟩, ⟨.hall 14 15, 2307300528372840⟩, ⟨.hall 12 16, 11548336800⟩, ⟨.hall 11 18, 8507322995371200⟩, ⟨.hall 8 19, 201915596784720⟩, ⟨.hall 10 19, 13732087184655840⟩, ⟨.hall 9 20, 16897582257716160⟩, ⟨.hall 7 22, 85702487846976000⟩, ⟨.hall 6 23, 155907604446594000⟩, ⟨.hall 5 24, 244246977121859712⟩, ⟨.hall 4 25, 342984684552269760⟩, ⟨.hall 3 26, 399387471321238400⟩, ⟨.hall 2 27, 308908273102228800⟩]
  caps := #[0, 0, 8052072298233600, 2163702300177600, 0, 0, 22125101526528, 0, 0, 0, 3108011503428, 0, 1115353330140, 479039720640, 13943238374520, 0, 21224626525830, 0, 7463795058720, 209813260539168, 3643376257986192, 0, 153180133483977600, 0] }

theorem case_53_30_15_checked :
    (Witness.linear .positive case_53_30_15).check 53 30 15 = true := by
  change case_53_30_15.check 53 30 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_30_16 : Certificate := {
  objectiveScale := 1371333600000
  eta := 6439860680305852800
  rows := #[⟨.count 2, 1572194726203701600⟩, ⟨.count 3, 379727855363656800⟩, ⟨.count 4, 90514170852225120⟩, ⟨.count 5, 23890515720271200⟩, ⟨.count 6, 6401569591216800⟩, ⟨.count 7, 1749173032807200⟩, ⟨.count 8, 489671002220400⟩, ⟨.count 9, 143247039455520⟩, ⟨.count 10, 44895209158800⟩, ⟨.count 11, 15018612008400⟩, ⟨.count 12, 6184134356400⟩, ⟨.count 13, 3132223894800⟩, ⟨.count 14, 1461704484240⟩, ⟨.count 15, 2436174140400⟩, ⟨.path 13, 207396859488⟩, ⟨.path 14, 130689322400⟩, ⟨.privateRow 2 28, 4721305484095200⟩, ⟨.privateRow 4 24, 6890857766072280⟩, ⟨.privateRow 5 22, 2985427001597040⟩, ⟨.privateRow 5 23, 7137572601519360⟩, ⟨.privateRow 6 19, 150211403942600⟩, ⟨.privateRow 6 20, 1026696589398480⟩, ⟨.privateRow 6 21, 2637245513202300⟩, ⟨.privateRow 6 22, 4423512197504400⟩, ⟨.privateRow 7 17, 100529471671200⟩, ⟨.privateRow 7 18, 387351688323600⟩, ⟨.privateRow 7 19, 945513986376960⟩, ⟨.privateRow 7 20, 1623536052138000⟩, ⟨.privateRow 7 21, 2269818249098400⟩, ⟨.privateRow 8 15, 49028004575550⟩, ⟨.privateRow 8 16, 152521902432900⟩, ⟨.privateRow 8 17, 355427656358775⟩, ⟨.privateRow 8 18, 605084752121850⟩, ⟨.privateRow 8 19, 847027296440325⟩, ⟨.privateRow 8 20, 967567162762200⟩, ⟨.privateRow 9 13, 21384195232400⟩, ⟨.privateRow 9 14, 61696110105630⟩, ⟨.privateRow 9 15, 140161218877680⟩, ⟨.privateRow 9 16, 237175086868720⟩, ⟨.privateRow 9 17, 331482094703760⟩, ⟨.privateRow 9 18, 383778632917680⟩, ⟨.privateRow 9 19, 330561762250720⟩, ⟨.privateRow 10 11, 8937278846496⟩, ⟨.privateRow 10 12, 25568227644960⟩, ⟨.privateRow 10 13, 58063600449855⟩, ⟨.privateRow 10 14, 98903698316280⟩, ⟨.privateRow 10 15, 139523173269480⟩, ⟨.privateRow 10 16, 164191176565416⟩, ⟨.privateRow 10 17, 58181058845910⟩, ⟨.privateRow 11 9, 3701719148400⟩, ⟨.privateRow 11 10, 10898532885240⟩, ⟨.privateRow 11 11, 25316578887600⟩, ⟨.privateRow 11 12, 44272780051500⟩, ⟨.privateRow 11 13, 64193379822000⟩, ⟨.privateRow 11 14, 23839704088200⟩, ⟨.privateRow 12 7, 1558303696950⟩, ⟨.privateRow 12 8, 4812113205900⟩, ⟨.privateRow 12 9, 11639424306510⟩, ⟨.privateRow 12 10, 21382707946600⟩, ⟨.privateRow 12 11, 10785424800150⟩, ⟨.privateRow 13 5, 685753160400⟩, ⟨.privateRow 13 6, 2235390557400⟩, ⟨.privateRow 13 7, 5673048872400⟩, ⟨.privateRow 13 8, 4537708975800⟩, ⟨.privateRow 14 3, 328137741360⟩, ⟨.privateRow 14 4, 1124388064800⟩, ⟨.privateRow 14 5, 1496506971960⟩, ⟨.privateRow 15 1, 184066490608⟩, ⟨.privateRow 15 2, 359625706440⟩, ⟨.privateRow 16 0, 121808707020⟩, ⟨.privateRow 17 0, 99435679200⟩, ⟨.privateRow 18 0, 151703151600⟩, ⟨.privateRow 18 2, 179285542800⟩, ⟨.privateRow 19 0, 1183284582480⟩, ⟨.privateRow 20 0, 3065782781880⟩, ⟨.privateRow 21 0, 22482407067120⟩, ⟨.privateRow 22 0, 262294749116400⟩, ⟨.privateRow 23 0, 6491795040630900⟩, ⟨.hall 7 21, 101414174097600⟩, ⟨.hall 8 21, 415367690938200⟩, ⟨.hall 7 22, 450374454129600⟩, ⟨.hall 6 23, 7841232499900800⟩, ⟨.hall 5 24, 18088634755455264⟩, ⟨.hall 4 25, 35466861856345920⟩, ⟨.hall 3 26, 58604141088292800⟩, ⟨.hall 2 27, 60871117134227400⟩, ⟨.assumptionRow 16, 1827465985800⟩]
  caps := #[0, 22937155354844640, 1953723072450240, 0, 73030032388040, 2511917314816, 21093506574868, 0, 4629437004192, 1399909173208, 633855455493, 296701726048, 0, 0, 496450823960, 691702920272, 0, 2962304467200, 5626807804800, 0, 58249872855720, 449648141342400, 5508189731444400, 0] }

theorem case_53_30_16_checked :
    (Witness.linear .conditional case_53_30_16).check 53 30 16 = true := by
  change case_53_30_16.check 53 30 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_30_17 : Certificate := {
  objectiveScale := 745945200000
  eta := 2085364314590356800
  rows := #[⟨.count 2, 536049761117270400⟩, ⟨.count 3, 138837510719107200⟩, ⟨.count 4, 36546017395567680⟩, ⟨.count 5, 10223578792627200⟩, ⟨.count 6, 2921802699816000⟩, ⟨.count 7, 854534929248000⟩, ⟨.count 8, 256360478774400⟩, ⟨.count 9, 79606674987840⟩, ⟨.count 10, 25539671757600⟩, ⟨.count 11, 9378137815200⟩, ⟨.count 12, 3669706101600⟩, ⟨.count 13, 1445641797600⟩, ⟨.count 14, 674632838880⟩, ⟨.count 15, 1124388064800⟩, ⟨.path 13, 114838686144⟩, ⟨.privateRow 2 28, 34865025113318400⟩, ⟨.privateRow 4 24, 4643481767324400⟩, ⟨.privateRow 5 22, 1604806959515760⟩, ⟨.privateRow 5 23, 4330821571876800⟩, ⟨.privateRow 6 19, 22755472740000⟩, ⟨.privateRow 6 20, 523011785456160⟩, ⟨.privateRow 6 21, 1505502076478400⟩, ⟨.privateRow 6 22, 2825319495398400⟩, ⟨.privateRow 7 17, 13538550168000⟩, ⟨.privateRow 7 18, 176903722195200⟩, ⟨.privateRow 7 19, 523836336703680⟩, ⟨.privateRow 7 20, 1016768064312000⟩, ⟨.privateRow 7 21, 1598237320680000⟩, ⟨.privateRow 8 15, 5586803196975⟩, ⟨.privateRow 8 16, 61098444306900⟩, ⟨.privateRow 8 17, 186976365275700⟩, ⟨.privateRow 8 18, 374533664384880⟩, ⟨.privateRow 8 19, 597787942076325⟩, ⟨.privateRow 8 20, 792880983694800⟩, ⟨.privateRow 9 13, 1890637708960⟩, ⟨.privateRow 9 14, 21382113032280⟩, ⟨.privateRow 9 15, 68512712748480⟩, ⟨.privateRow 9 16, 142822270631040⟩, ⟨.privateRow 9 17, 233542896979392⟩, ⟨.privateRow 9 18, 315240933767760⟩, ⟨.privateRow 9 19, 327621695681280⟩, ⟨.privateRow 10 11, 501155823168⟩, ⟨.privateRow 10 12, 7528045805280⟩, ⟨.privateRow 10 13, 25780612057200⟩, ⟨.privateRow 10 14, 56600318380320⟩, ⟨.privateRow 10 15, 96127148197080⟩, ⟨.privateRow 10 16, 134020632249504⟩, ⟨.privateRow 10 17, 151286414118840⟩, ⟨.privateRow 10 18, 110864663189280⟩, ⟨.privateRow 11 9, 50546916000⟩, ⟨.privateRow 11 10, 2639222974080⟩, ⟨.privateRow 11 11, 9954747079200⟩, ⟨.privateRow 11 12, 23385109463100⟩, ⟨.privateRow 11 13, 41918316739200⟩, ⟨.privateRow 11 14, 61347107052000⟩, ⟨.privateRow 11 15, 56876737800960⟩, ⟨.privateRow 12 8, 830935135800⟩, ⟨.privateRow 12 9, 3934740431160⟩, ⟨.privateRow 12 10, 10084140943800⟩, ⟨.privateRow 12 11, 19423108799325⟩, ⟨.privateRow 12 12, 29988682930800⟩, ⟨.privateRow 13 6, 259474168800⟩, ⟨.privateRow 13 7, 1513037685600⟩, ⟨.privateRow 13 8, 4533384406320⟩, ⟨.privateRow 13 9, 9567595144800⟩, ⟨.privateRow 13 10, 4114518962400⟩, ⟨.privateRow 14 4, 74135476800⟩, ⟨.privateRow 14 5, 610382092320⟩, ⟨.privateRow 14 6, 2037040714800⟩, ⟨.privateRow 14 7, 2823820311312⟩, ⟨.privateRow 15 3, 213345427680⟩, ⟨.privateRow 15 4, 1099401663360⟩, ⟨.privateRow 16 1, 90352612350⟩, ⟨.privateRow 16 2, 172982779200⟩, ⟨.privateRow 17 0, 45893390400⟩, ⟨.privateRow 18 0, 70016839200⟩, ⟨.privateRow 19 0, 273065672880⟩, ⟨.privateRow 20 0, 1414976668560⟩, ⟨.privateRow 21 0, 10376495569440⟩, ⟨.privateRow 22 0, 121059114976800⟩, ⟨.hall 8 19, 3855044793600⟩, ⟨.hall 9 20, 6232322416320⟩, ⟨.hall 7 21, 33291664005600⟩, ⟨.hall 7 22, 1881932301849600⟩, ⟨.hall 6 23, 6306679269891000⟩, ⟨.hall 5 24, 12972803987183040⟩, ⟨.hall 4 25, 23639253291118080⟩, ⟨.hall 3 26, 38127856497931200⟩, ⟨.hall 2 27, 47628114663729600⟩, ⟨.assumptionRow 17, 750108930480⟩]
  caps := #[0, 2279008940448240, 0, 165381421645440, 0, 27087305999040, 6372116464896, 92536123680, 1459946547696, 28327323024, 0, 0, 806011458087, 179075174544, 79639822080, 0, 750108930480, 3474214258320, 1936231466400, 4915182111840, 26884556702640, 207529911388800, 0, 0] }

theorem case_53_30_17_checked :
    (Witness.linear .conditional case_53_30_17).check 53 30 17 = true := by
  change case_53_30_17.check 53 30 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_30_18 : Certificate := {
  objectiveScale := 382536000000
  eta := 926828584262380800
  rows := #[⟨.count 2, 232433500755456000⟩, ⟨.count 3, 59249789701502400⟩, ⟨.count 4, 15793026256687680⟩, ⟨.count 5, 4254363183470400⟩, ⟨.count 6, 1161439328649600⟩, ⟨.count 7, 320075802446400⟩, ⟨.count 8, 96322577551200⟩, ⟨.count 9, 29908722523680⟩, ⟨.count 10, 9637611984000⟩, ⟨.count 11, 3126045938400⟩, ⟨.count 12, 1495065448800⟩, ⟨.count 13, 642507465600⟩, ⟨.count 14, 449755225920⟩, ⟨.count 15, 374796021600⟩, ⟨.path 11, 18317448864⟩, ⟨.path 12, 71768498256⟩, ⟨.privateRow 2 28, 23606527420476000⟩, ⟨.privateRow 4 24, 2564723821579920⟩, ⟨.privateRow 5 21, 21189896215488⟩, ⟨.privateRow 5 22, 788340597604560⟩, ⟨.privateRow 5 23, 2294115739755840⟩, ⟨.privateRow 6 19, 9911272571200⟩, ⟨.privateRow 6 20, 244970249203680⟩, ⟨.privateRow 6 21, 757150429635600⟩, ⟨.privateRow 6 22, 1544439218722400⟩, ⟨.privateRow 7 17, 2508838675200⟩, ⟨.privateRow 7 18, 75994355236800⟩, ⟨.privateRow 7 19, 252119929501440⟩, ⟨.privateRow 7 20, 538688967616800⟩, ⟨.privateRow 7 21, 931350266246400⟩, ⟨.privateRow 8 16, 23143654333800⟩, ⟨.privateRow 8 17, 84563352373500⟩, ⟨.privateRow 8 18, 191820603854880⟩, ⟨.privateRow 8 19, 342188767720800⟩, ⟨.privateRow 8 20, 511549719981300⟩, ⟨.privateRow 9 14, 6249723660180⟩, ⟨.privateRow 9 15, 28409538437280⟩, ⟨.privateRow 9 16, 69774526021200⟩, ⟨.privateRow 9 17, 130349059032192⟩, ⟨.privateRow 9 18, 200796968572200⟩, ⟨.privateRow 9 19, 253753564224160⟩, ⟨.privateRow 10 12, 1620546607680⟩, ⟨.privateRow 10 13, 9161754892290⟩, ⟨.privateRow 10 14, 25858630820880⟩, ⟨.privateRow 10 15, 51582641029920⟩, ⟨.privateRow 10 16, 83114765750016⟩, ⟨.privateRow 10 17, 110161920648780⟩, ⟨.privateRow 10 18, 110720099009520⟩, ⟨.privateRow 11 10, 342258784560⟩, ⟨.privateRow 11 11, 2921486937600⟩, ⟨.privateRow 11 12, 9515597345100⟩, ⟨.privateRow 11 13, 21158618104800⟩, ⟨.privateRow 11 14, 36398459790000⟩, ⟨.privateRow 11 15, 51348702414240⟩, ⟨.privateRow 11 16, 55660298185800⟩, ⟨.privateRow 12 8, 22652506800⟩, ⟨.privateRow 12 9, 873254137140⟩, ⟨.privateRow 12 10, 3530015643000⟩, ⟨.privateRow 12 11, 8840140778700⟩, ⟨.privateRow 12 12, 16801687900800⟩, ⟨.privateRow 12 13, 25744573978200⟩, ⟨.privateRow 12 14, 8836742902680⟩, ⟨.privateRow 13 7, 176352573600⟩, ⟨.privateRow 13 8, 1281308157360⟩, ⟨.privateRow 13 9, 3786400833600⟩, ⟨.privateRow 13 10, 8068411058400⟩, ⟨.privateRow 13 11, 9266934600000⟩, ⟨.privateRow 14 5, 22755472740⟩, ⟨.privateRow 14 6, 385504479360⟩, ⟨.privateRow 14 7, 1620725081976⟩, ⟨.privateRow 14 8, 4029949603680⟩, ⟨.privateRow 14 9, 1305093289500⟩, ⟨.privateRow 15 4, 99945605760⟩, ⟨.privateRow 15 5, 617845562880⟩, ⟨.privateRow 15 6, 1456707203952⟩, ⟨.privateRow 16 2, 14415231600⟩, ⟨.privateRow 16 3, 230343388275⟩, ⟨.privateRow 16 4, 315169381800⟩, ⟨.privateRow 17 1, 82372752000⟩, ⟨.privateRow 17 2, 35694859200⟩, ⟨.privateRow 18 0, 23338946400⟩, ⟨.hall 8 20, 7301221200⟩, ⟨.hall 9 20, 164995917166080⟩, ⟨.hall 8 21, 744413043628800⟩, ⟨.hall 7 22, 1928798100028800⟩, ⟨.hall 6 23, 4119271526970600⟩, ⟨.hall 5 24, 7827372899970624⟩, ⟨.hall 4 25, 13544519485986720⟩, ⟨.hall 3 26, 21321776821945600⟩, ⟨.hall 2 27, 27757125648252000⟩, ⟨.assumptionRow 18, 261133036164⟩]
  caps := #[0, 0, 0, 0, 0, 3082882616352, 0, 76468752360, 253915814256, 151741715216, 0, 251766719544, 0, 156955958208, 0, 0, 524182926897, 261133036164, 0, 382536000000, 0, 0, 0, 0] }

theorem case_53_30_18_checked :
    (Witness.linear .conditional case_53_30_18).check 53 30 18 = true := by
  change case_53_30_18.check 53 30 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_30_19 : Certificate := {
  objectiveScale := 2042040000000
  eta := 7190911429621920000
  rows := #[⟨.count 2, 1795548793335897600⟩, ⟨.count 3, 450132377802307200⟩, ⟨.count 4, 113684885458784640⟩, ⟨.count 5, 29818771478496000⟩, ⟨.count 6, 7820600871283200⟩, ⟨.count 7, 2050883830195200⟩, ⟨.count 8, 530711166585600⟩, ⟨.count 9, 134926567776000⟩, ⟨.count 10, 34695403142400⟩, ⟨.count 11, 8154902448000⟩, ⟨.count 12, 1630980489600⟩, ⟨.path 12, 647859244032⟩, ⟨.path 13, 98281677312⟩, ⟨.privateRow 2 28, 145997292662020800⟩, ⟨.privateRow 4 24, 16425992486423520⟩, ⟨.privateRow 5 22, 5213369826624960⟩, ⟨.privateRow 5 23, 15440225407326720⟩, ⟨.privateRow 6 19, 43387101357600⟩, ⟨.privateRow 6 20, 1569217400150400⟩, ⟨.privateRow 6 21, 5048074072641600⟩, ⟨.privateRow 6 22, 10632570489340800⟩, ⟨.privateRow 7 17, 21937040611200⟩, ⟨.privateRow 7 18, 477704300673600⟩, ⟨.privateRow 7 19, 1636209511896960⟩, ⟨.privateRow 7 20, 3644462971749600⟩, ⟨.privateRow 7 21, 6588271552262400⟩, ⟨.privateRow 8 15, 7062562532025⟩, ⟨.privateRow 8 16, 144202769310600⟩, ⟨.privateRow 8 17, 532866243709800⟩, ⟨.privateRow 8 18, 1262687796770400⟩, ⟨.privateRow 8 19, 2375621158160250⟩, ⟨.privateRow 8 20, 3771478666355400⟩, ⟨.privateRow 9 13, 1482526485440⟩, ⟨.privateRow 9 14, 42295731037560⟩, ⟨.privateRow 9 15, 173284263472320⟩, ⟨.privateRow 9 16, 443958380785920⟩, ⟨.privateRow 9 17, 880560764987904⟩, ⟨.privateRow 9 18, 1453421492162640⟩, ⟨.privateRow 9 19, 1995663883012800⟩, ⟨.privateRow 10 12, 11661510500640⟩, ⟨.privateRow 10 13, 55645162192620⟩, ⟨.privateRow 10 14, 157932924383520⟩, ⟨.privateRow 10 15, 336368720928240⟩, ⟨.privateRow 10 16, 585060873100704⟩, ⟨.privateRow 10 17, 847603879962840⟩, ⟨.privateRow 10 18, 965174714824320⟩, ⟨.privateRow 11 10, 2587328140320⟩, ⟨.privateRow 11 11, 17240616993600⟩, ⟨.privateRow 11 12, 56380030106400⟩, ⟨.privateRow 11 13, 132183555134400⟩, ⟨.privateRow 11 14, 246784646354400⟩, ⟨.privateRow 11 15, 381723570043200⟩, ⟨.privateRow 11 16, 480138415495200⟩, ⟨.privateRow 11 17, 358815707712000⟩, ⟨.privateRow 12 8, 475702642800⟩, ⟨.privateRow 12 9, 4716251915760⟩, ⟨.privateRow 12 10, 19836045121200⟩, ⟨.privateRow 12 11, 53074823432400⟩, ⟨.privateRow 12 12, 108965029852800⟩, ⟨.privateRow 12 13, 182839708636200⟩, ⟨.privateRow 12 14, 252720426863520⟩, ⟨.privateRow 13 6, 12355912800⟩, ⟨.privateRow 13 7, 1105292563200⟩, ⟨.privateRow 13 8, 6427545838560⟩, ⟨.privateRow 13 9, 21400440969600⟩, ⟨.privateRow 13 10, 50004379101600⟩, ⟨.privateRow 13 11, 92987069472000⟩, ⟨.privateRow 13 12, 66128845305600⟩, ⟨.privateRow 14 5, 80313433200⟩, ⟨.privateRow 14 6, 1857430673280⟩, ⟨.privateRow 14 7, 8201607798384⟩, ⟨.privateRow 14 8, 23408688663360⟩, ⟨.privateRow 14 9, 49790312912340⟩, ⟨.privateRow 14 10, 1721002140000⟩, ⟨.privateRow 15 4, 212384412240⟩, ⟨.privateRow 15 5, 2875707656640⟩, ⟨.privateRow 15 6, 10659198854304⟩, ⟨.privateRow 15 7, 15441596089920⟩, ⟨.privateRow 16 3, 491919778350⟩, ⟨.privateRow 16 4, 4523106533400⟩, ⟨.privateRow 16 5, 4047797033280⟩, ⟨.privateRow 17 2, 1070845776000⟩, ⟨.privateRow 17 3, 1401834470400⟩, ⟨.privateRow 18 1, 606812606400⟩, ⟨.hall 9 19, 4465426885920⟩, ⟨.hall 9 20, 1958748259628160⟩, ⟨.hall 8 21, 6628267641996000⟩, ⟨.hall 7 22, 15433643896070400⟩, ⟨.hall 6 23, 31081700215566000⟩, ⟨.hall 5 24, 56881108828672128⟩, ⟨.hall 4 25, 95926710579638400⟩, ⟨.hall 3 26, 147784355787868800⟩, ⟨.hall 2 27, 184753503613879200⟩, ⟨.assumptionRow 19, 358902925920⟩]
  caps := #[0, 14709688722630720, 2090433027926880, 0, 37862775457920, 0, 3921535123968, 5905306513392, 915920189184, 647593160032, 435306523680, 1773636204480, 0, 2152340671872, 358902925920, 527144409120, 358902925920, 4073437149600, 358902925920, 20061497074080, 2042040000000, 0, 0, 0] }

theorem case_53_30_19_checked :
    (Witness.linear .conditional case_53_30_19).check 53 30 19 = true := by
  change case_53_30_19.check 53 30 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_31_1_checked :
    (Witness.rising).check 53 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_31_2_checked :
    (Witness.rising).check 53 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_31_3_checked :
    (Witness.rising).check 53 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_31_4_checked :
    (Witness.rising).check 53 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_31_5_checked :
    (Witness.rising).check 53 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_31_6_checked :
    (Witness.rising).check 53 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_31_7_checked :
    (Witness.rising).check 53 31 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_31_8_checked :
    (Witness.rising).check 53 31 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_31_9_checked :
    (Witness.rising).check 53 31 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_31_10_checked :
    (Witness.rising).check 53 31 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_31_11_checked :
    (Witness.linear .positive case_53_31_11).check 53 31 11 = true := by
  change case_53_31_11.check 53 31 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_31_12_checked :
    (Witness.linear .positive case_53_31_12).check 53 31 12 = true := by
  change case_53_31_12.check 53 31 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_31_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_31_13_checked :
    (Witness.linear .positive case_53_31_13).check 53 31 13 = true := by
  change case_53_31_13.check 53 31 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_31_14 : Certificate := {
  objectiveScale := 1390072320000
  eta := 9234873526890211200
  rows := #[⟨.count 2, 2012625080648582400⟩, ⟨.count 3, 413181677079531360⟩, ⟨.count 4, 92182602113521920⟩, ⟨.count 5, 19453198535971200⟩, ⟨.count 6, 4502049811459200⟩, ⟨.count 7, 993959049283200⟩, ⟨.count 8, 245566353352320⟩, ⟨.count 9, 58885809222240⟩, ⟨.count 10, 16383940372800⟩, ⟨.count 11, 4417238826000⟩, ⟨.count 12, 1927522396800⟩, ⟨.count 13, 1252889557920⟩, ⟨.path 14, 463353875712⟩, ⟨.privateRow 3 28, 100631254032429120⟩, ⟨.privateRow 6 24, 21862922785704000⟩, ⟨.privateRow 7 17, 51224911612875⟩, ⟨.privateRow 7 18, 179133376078800⟩, ⟨.privateRow 7 19, 329579558708400⟩, ⟨.privateRow 7 20, 549392071147920⟩, ⟨.privateRow 7 21, 818685020503350⟩, ⟨.privateRow 7 22, 958634524247400⟩, ⟨.privateRow 7 23, 2934632770769700⟩, ⟨.privateRow 8 15, 37760699176200⟩, ⟨.privateRow 8 16, 84626599202145⟩, ⟨.privateRow 8 18, 615499396572060⟩, ⟨.privateRow 8 20, 1168023691614780⟩, ⟨.privateRow 8 21, 638927271222240⟩, ⟨.privateRow 9 12, 3277761570720⟩, ⟨.privateRow 9 13, 16315406243136⟩, ⟨.privateRow 9 14, 38452881987520⟩, ⟨.privateRow 9 15, 66385745325900⟩, ⟨.privateRow 9 16, 45183572628480⟩, ⟨.privateRow 9 18, 791269360801920⟩, ⟨.privateRow 10 10, 2891283595200⟩, ⟨.privateRow 10 11, 7508575882080⟩, ⟨.privateRow 10 12, 16364665148832⟩, ⟨.privateRow 10 13, 29330465804640⟩, ⟨.privateRow 10 14, 52898442777180⟩, ⟨.privateRow 10 15, 40546810418400⟩, ⟨.privateRow 10 16, 24688349365680⟩, ⟨.privateRow 10 17, 331418200905792⟩, ⟨.privateRow 11 7, 269623668600⟩, ⟨.privateRow 11 8, 1532133187200⟩, ⟨.privateRow 11 9, 3935358226800⟩, ⟨.privateRow 11 10, 7483751730000⟩, ⟨.privateRow 11 11, 13227622448040⟩, ⟨.privateRow 11 12, 24977477725200⟩, ⟨.privateRow 11 13, 38972093460300⟩, ⟨.privateRow 11 14, 32572833836400⟩, ⟨.privateRow 11 15, 24508982698200⟩, ⟨.privateRow 11 16, 150635875309920⟩, ⟨.privateRow 12 5, 310545275040⟩, ⟨.privateRow 12 6, 860501070000⟩, ⟨.privateRow 12 7, 2069615394000⟩, ⟨.privateRow 12 8, 4002286087800⟩, ⟨.privateRow 12 9, 6673316176800⟩, ⟨.privateRow 12 10, 12657397072320⟩, ⟨.privateRow 12 11, 21149204076000⟩, ⟨.privateRow 12 12, 31412591560350⟩, ⟨.privateRow 12 13, 28706315695200⟩, ⟨.privateRow 12 14, 23223967767000⟩, ⟨.privateRow 12 15, 78434098863120⟩, ⟨.privateRow 12 17, 102453169618800⟩, ⟨.privateRow 13 3, 307198881990⟩, ⟨.privateRow 13 4, 520431047136⟩, ⟨.privateRow 13 5, 1197817489440⟩, ⟨.privateRow 13 6, 2357508162240⟩, ⟨.privateRow 13 7, 4095985093200⟩, ⟨.privateRow 13 8, 7429722693120⟩, ⟨.privateRow 13 9, 12750560654832⟩, ⟨.privateRow 13 10, 20388903575040⟩, ⟨.privateRow 13 11, 29454951626100⟩, ⟨.privateRow 13 12, 29615004825120⟩, ⟨.privateRow 13 14, 101426228519616⟩, ⟨.privateRow 14 2, 1035374009670⟩, ⟨.privateRow 14 3, 445471842816⟩, ⟨.privateRow 14 4, 1590970867200⟩, ⟨.privateRow 14 5, 2880575137440⟩, ⟨.privateRow 14 6, 5463990572040⟩, ⟨.privateRow 14 7, 9061302257280⟩, ⟨.privateRow 14 8, 14867622753984⟩, ⟨.privateRow 14 9, 22737625310400⟩, ⟨.privateRow 14 10, 31531053874320⟩, ⟨.privateRow 14 11, 32515467098400⟩, ⟨.privateRow 14 13, 57577235683968⟩, ⟨.privateRow 15 0, 501565264200⟩, ⟨.privateRow 15 1, 1278991423710⟩, ⟨.privateRow 15 2, 812058046800⟩, ⟨.privateRow 15 3, 2383970408820⟩, ⟨.privateRow 15 4, 4684950270000⟩, ⟨.privateRow 15 6, 5226700883040⟩, ⟨.privateRow 15 7, 61318503113868⟩, ⟨.privateRow 15 8, 7064905007160⟩, ⟨.privateRow 15 9, 43759777996935⟩, ⟨.privateRow 15 10, 50672422120320⟩, ⟨.privateRow 15 12, 111186987767856⟩, ⟨.privateRow 15 14, 150636767681400⟩, ⟨.privateRow 15 16, 12180870702000⟩, ⟨.privateRow 16 0, 1109329296075⟩, ⟨.privateRow 16 3, 26423119522800⟩, ⟨.privateRow 16 6, 89842622049180⟩, ⟨.privateRow 16 7, 44141155258200⟩, ⟨.privateRow 16 8, 55074936816900⟩, ⟨.privateRow 16 9, 88149729610800⟩, ⟨.privateRow 17 0, 4269105160320⟩, ⟨.privateRow 17 2, 55791064929600⟩, ⟨.privateRow 17 3, 8816630222400⟩, ⟨.privateRow 17 6, 275635702742400⟩, ⟨.privateRow 17 7, 296517195374400⟩, ⟨.privateRow 18 0, 26370342123840⟩, ⟨.privateRow 18 3, 16781126806080⟩, ⟨.privateRow 18 4, 673525584347616⟩, ⟨.privateRow 18 10, 685121773255920⟩, ⟨.privateRow 18 13, 8784704740331520⟩, ⟨.privateRow 19 0, 158924221616160⟩, ⟨.privateRow 19 3, 1708189623268128⟩, ⟨.privateRow 19 8, 3876440292204480⟩, ⟨.privateRow 20 0, 1292738406359400⟩, ⟨.privateRow 20 2, 5355309363387984⟩, ⟨.privateRow 20 4, 6070249908122400⟩, ⟨.privateRow 20 7, 4937136591939552⟩, ⟨.privateRow 20 8, 16794358079138640⟩, ⟨.privateRow 21 2, 104768016932779200⟩, ⟨.privateRow 21 8, 279231495773630400⟩, ⟨.hall 16 7, 113141887040⟩, ⟨.hall 13 8, 17185706720⟩, ⟨.hall 18 10, 6652872757440⟩, ⟨.hall 19 11, 1382668034627880⟩, ⟨.hall 18 12, 439089601991040⟩, ⟨.hall 14 13, 202468590324⟩, ⟨.hall 12 14, 68212544400⟩, ⟨.hall 11 18, 2224893450780⟩, ⟨.hall 6 19, 185516321328⟩, ⟨.hall 10 20, 1327558104100800⟩, ⟨.hall 9 21, 2154685291995600⟩, ⟨.hall 8 22, 3600029855822400⟩, ⟨.hall 7 23, 4761806879179350⟩, ⟨.hall 3 27, 77569122040221240⟩]
  caps := #[0, 13487505035921280, 1048174997425920, 0, 8396175820032, 2851107831936, 8673850785600, 2434816460934, 0, 0, 1198734903756, 903639304638, 133716784842, 513879672258, 1225046406948, 527368161684, 968780787975, 10808403365760, 51293081550672, 0, 0, 0, 0] }

theorem case_53_31_14_checked :
    (Witness.linear .positive case_53_31_14).check 53 31 14 = true := by
  change case_53_31_14.check 53 31 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_31_15 : Certificate := {
  objectiveScale := 1737590400000
  eta := 12634213475438755200
  rows := #[⟨.count 2, 2902928400506534400⟩, ⟨.count 3, 722764422393773760⟩, ⟨.count 4, 178742235891098880⟩, ⟨.count 5, 43781529551760000⟩, ⟨.count 6, 10557682674739200⟩, ⟨.count 7, 2791855564898400⟩, ⟨.count 8, 744494817306240⟩, ⟨.count 9, 200462329267200⟩, ⟨.count 10, 53970627110400⟩, ⟨.count 11, 17668955304000⟩, ⟨.count 12, 5782567190400⟩, ⟨.count 13, 2505779115840⟩, ⟨.count 14, 3897878624640⟩, ⟨.path 14, 434390471424⟩, ⟨.privateRow 2 29, 248205774021004800⟩, ⟨.privateRow 3 28, 417633193678821120⟩, ⟨.privateRow 6 25, 206868771206697600⟩, ⟨.privateRow 7 18, 431948590444800⟩, ⟨.privateRow 7 19, 936012907229400⟩, ⟨.privateRow 7 20, 1788917473783440⟩, ⟨.privateRow 7 21, 3157020667300500⟩, ⟨.privateRow 7 22, 5261788118386800⟩, ⟨.privateRow 8 15, 20680411591840⟩, ⟨.privateRow 8 16, 173455598796480⟩, ⟨.privateRow 8 19, 1913273722904544⟩, ⟨.privateRow 8 20, 5649487831587600⟩, ⟨.privateRow 9 13, 16259722262784⟩, ⟨.privateRow 9 14, 68398489199040⟩, ⟨.privateRow 9 15, 166181878863000⟩, ⟨.privateRow 9 16, 154562819748480⟩, ⟨.privateRow 9 17, 235589640205920⟩, ⟨.privateRow 9 18, 1005207213314304⟩, ⟨.privateRow 9 19, 2260908812242080⟩, ⟨.privateRow 9 20, 1510149547146240⟩, ⟨.privateRow 10 11, 9111924057600⟩, ⟨.privateRow 10 12, 25057791158400⟩, ⟨.privateRow 10 13, 74573699840640⟩, ⟨.privateRow 10 15, 442972182818880⟩, ⟨.privateRow 10 16, 71575331667840⟩, ⟨.privateRow 10 18, 2161330863531840⟩, ⟨.privateRow 10 19, 665509232868480⟩, ⟨.privateRow 11 9, 4564480120200⟩, ⟨.privateRow 11 10, 13054583505600⟩, ⟨.privateRow 11 11, 25925176236960⟩, ⟨.privateRow 11 12, 69872686884000⟩, ⟨.privateRow 11 13, 20098436658300⟩, ⟨.privateRow 11 14, 286902530085600⟩, ⟨.privateRow 11 16, 389134646540640⟩, ⟨.privateRow 12 6, 195046909200⟩, ⟨.privateRow 12 7, 2014013786400⟩, ⟨.privateRow 12 8, 6438460228200⟩, ⟨.privateRow 12 9, 13521861662400⟩, ⟨.privateRow 12 11, 117275459901600⟩, ⟨.privateRow 12 13, 194289668258400⟩, ⟨.privateRow 12 14, 87996751642800⟩, ⟨.privateRow 12 15, 188479565033760⟩, ⟨.privateRow 12 18, 259894269835200⟩, ⟨.privateRow 13 4, 231302687616⟩, ⟨.privateRow 13 5, 1032601284000⟩, ⟨.privateRow 13 6, 3113690025600⟩, ⟨.privateRow 13 7, 6119883609840⟩, ⟨.privateRow 13 8, 18153756391680⟩, ⟨.privateRow 13 10, 106763323867200⟩, ⟨.privateRow 13 11, 24527722499280⟩, ⟨.privateRow 13 12, 136496121727680⟩, ⟨.privateRow 13 13, 129497379691680⟩, ⟨.privateRow 13 14, 134039907473472⟩, ⟨.privateRow 14 2, 226216170180⟩, ⟨.privateRow 14 3, 649646437440⟩, ⟨.privateRow 14 4, 1690406546400⟩, ⟨.privateRow 14 5, 3983546286720⟩, ⟨.privateRow 14 6, 8352597052800⟩, ⟨.privateRow 14 7, 22374835741440⟩, ⟨.privateRow 14 8, 2227359214080⟩, ⟨.privateRow 14 9, 107006048909760⟩, ⟨.privateRow 14 10, 57772129615200⟩, ⟨.privateRow 14 11, 117890941259520⟩, ⟨.privateRow 14 12, 164082128770560⟩, ⟨.privateRow 14 14, 275705307717840⟩, ⟨.privateRow 15 2, 2890926646608⟩, ⟨.privateRow 15 3, 382827364920⟩, ⟨.privateRow 15 4, 8732747303280⟩, ⟨.privateRow 15 5, 11409415557540⟩, ⟨.privateRow 15 6, 31847440126320⟩, ⟨.privateRow 15 7, 8380439042976⟩, ⟨.privateRow 15 8, 121213197785680⟩, ⟨.privateRow 15 9, 111272253862770⟩, ⟨.privateRow 15 12, 674138108131488⟩, ⟨.privateRow 15 13, 268222772858040⟩, ⟨.privateRow 15 16, 3846718967691600⟩, ⟨.privateRow 16 0, 652546644750⟩, ⟨.privateRow 16 1, 5150768182560⟩, ⟨.privateRow 16 2, 745767594000⟩, ⟨.privateRow 16 3, 8593537352400⟩, ⟨.privateRow 16 4, 24361741404000⟩, ⟨.privateRow 16 6, 151808451434640⟩, ⟨.privateRow 16 7, 91762559288400⟩, ⟨.privateRow 16 9, 297710423524800⟩, ⟨.privateRow 16 10, 208640913881400⟩, ⟨.privateRow 16 12, 251099948899800⟩, ⟨.privateRow 17 0, 16333967569920⟩, ⟨.privateRow 17 2, 18846885657600⟩, ⟨.privateRow 17 3, 44315167696800⟩, ⟨.privateRow 17 4, 26829554169600⟩, ⟨.privateRow 17 5, 245566353352320⟩, ⟨.privateRow 17 6, 264189551225600⟩, ⟨.privateRow 17 8, 532179755078400⟩, ⟨.privateRow 17 9, 290020731000000⟩, ⟨.privateRow 17 10, 807417715104000⟩, ⟨.privateRow 17 12, 550343339145600⟩, ⟨.privateRow 18 0, 100748230165440⟩, ⟨.privateRow 18 2, 117539601859680⟩, ⟨.privateRow 18 3, 94662766598400⟩, ⟨.privateRow 18 4, 517805333293248⟩, ⟨.privateRow 18 5, 769923835000320⟩, ⟨.privateRow 18 7, 1440226377532800⟩, ⟨.privateRow 18 9, 2735753954693760⟩, ⟨.privateRow 19 0, 783152349819840⟩, ⟨.privateRow 19 2, 406619611070400⟩, ⟨.privateRow 19 5, 7199103399808320⟩, ⟨.privateRow 19 8, 18257607793833408⟩, ⟨.privateRow 20 0, 7126923040277040⟩, ⟨.privateRow 20 4, 9577505410593120⟩, ⟨.privateRow 20 7, 140829797868439680⟩, ⟨.privateRow 21 0, 75050362500422400⟩, ⟨.privateRow 21 3, 51597124219040400⟩, ⟨.privateRow 21 4, 31989253484073600⟩, ⟨.privateRow 21 10, 5889491355302755200⟩, ⟨.privateRow 22 0, 1914961504349013120⟩, ⟨.hall 21 5, 56655665809142400⟩, ⟨.hall 17 7, 5538544152960⟩, ⟨.hall 12 9, 3634787520⟩, ⟨.hall 15 9, 509168913435⟩, ⟨.hall 16 10, 2606744574720⟩, ⟨.hall 19 10, 1698443661161520⟩, ⟨.hall 18 11, 858518475534720⟩, ⟨.hall 9 13, 18721222416⟩, ⟨.hall 8 14, 22931347712⟩, ⟨.hall 15 15, 174947755457475⟩, ⟨.hall 7 16, 38647012950⟩, ⟨.hall 13 17, 2198125124395200⟩, ⟨.hall 12 18, 2794501681171200⟩, ⟨.hall 8 19, 2401674283008⟩, ⟨.hall 11 19, 3974543150858280⟩, ⟨.hall 7 20, 5624969272650⟩, ⟨.hall 9 20, 121416388067520⟩, ⟨.hall 10 20, 6879969941644800⟩, ⟨.hall 6 24, 27286264052087040⟩, ⟨.hall 4 26, 205967247564798720⟩, ⟨.hall 3 27, 262841821021699920⟩]
  caps := #[0, 9167121289872000, 1428547205030400, 132122898835200, 8635638945024, 0, 2349685578240, 5711616452256, 1242721133472, 4785328204800, 929864819520, 0, 298956438144, 1138321997568, 4801516243524, 100560993078, 17529924986340, 0, 91146720981888, 0, 0, 11366170679335680, 0] }

theorem case_53_31_15_checked :
    (Witness.linear .positive case_53_31_15).check 53 31 15 = true := by
  change case_53_31_15.check 53 31 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_31_16 : Certificate := {
  objectiveScale := 32420115000000
  eta := 246452146269769440000
  rows := #[⟨.count 2, 54141233402755699200⟩, ⟨.count 3, 13073699568786816960⟩, ⟨.count 4, 3142728120853601280⟩, ⟨.count 5, 743954682696825600⟩, ⟨.count 6, 196202504770272000⟩, ⟨.count 7, 52562893253270400⟩, ⟨.count 8, 14355886974549120⟩, ⟨.count 9, 4069385284124160⟩, ⟨.count 10, 1229759289158400⟩, ⟨.count 11, 409919763052800⟩, ⟨.count 12, 167694448521600⟩, ⟨.count 13, 72667594359360⟩, ⟨.count 14, 113038480114560⟩, ⟨.path 13, 10806743001600⟩, ⟨.privateRow 2 29, 2660118404181638400⟩, ⟨.privateRow 4 24, 96357230120511360⟩, ⟨.privateRow 4 25, 474374055977902080⟩, ⟨.privateRow 5 22, 64018535795165952⟩, ⟨.privateRow 5 23, 169860501815004000⟩, ⟨.privateRow 5 24, 362094548515539840⟩, ⟨.privateRow 6 20, 30305078240236800⟩, ⟨.privateRow 6 21, 64092818224955520⟩, ⟨.privateRow 6 22, 129146463530884800⟩, ⟨.privateRow 6 23, 195018292121452800⟩, ⟨.privateRow 7 17, 1491199592582700⟩, ⟨.privateRow 7 18, 11181293536842000⟩, ⟨.privateRow 7 19, 24994624643188200⟩, ⟨.privateRow 7 20, 47930334112861200⟩, ⟨.privateRow 7 21, 70941738993325200⟩, ⟨.privateRow 7 22, 89209564797553200⟩, ⟨.privateRow 8 15, 1125674864474160⟩, ⟨.privateRow 8 16, 4385539783194570⟩, ⟨.privateRow 8 17, 9464954165306640⟩, ⟨.privateRow 8 18, 18670188965588160⟩, ⟨.privateRow 8 19, 27157494847523040⟩, ⟨.privateRow 8 20, 33579493499031480⟩, ⟨.privateRow 8 21, 33614818024067280⟩, ⟨.privateRow 9 13, 602333615467584⟩, ⟨.privateRow 9 14, 1852575090766400⟩, ⟨.privateRow 9 15, 3773668545967320⟩, ⟨.privateRow 9 16, 7407480809139840⟩, ⟨.privateRow 9 17, 11145055860818880⟩, ⟨.privateRow 9 18, 13719641815047168⟩, ⟨.privateRow 9 19, 13782620396825280⟩, ⟨.privateRow 9 20, 379486326098880⟩, ⟨.privateRow 10 11, 284572397491200⟩, ⟨.privateRow 10 12, 825056686726272⟩, ⟨.privateRow 10 13, 1626015060109440⟩, ⟨.privateRow 10 14, 3137982367960440⟩, ⟨.privateRow 10 15, 4829600117422080⟩, ⟨.privateRow 10 16, 6175813884720480⟩, ⟨.privateRow 11 9, 128488107547800⟩, ⟨.privateRow 11 10, 381970688299200⟩, ⟨.privateRow 11 11, 759749015385360⟩, ⟨.privateRow 11 12, 1462668245438400⟩, ⟨.privateRow 11 13, 2294153219358000⟩, ⟨.privateRow 11 14, 107138119888800⟩, ⟨.privateRow 12 6, 332727080400⟩, ⟨.privateRow 12 7, 57331435392000⟩, ⟨.privateRow 12 8, 183609893867400⟩, ⟨.privateRow 12 9, 382817629958400⟩, ⟨.privateRow 12 10, 759283197472800⟩, ⟨.privateRow 12 11, 48134517631200⟩, ⟨.privateRow 13 5, 27150529760640⟩, ⟨.privateRow 13 6, 92016953804160⟩, ⟨.privateRow 13 7, 207288971089200⟩, ⟨.privateRow 13 8, 30998064726720⟩, ⟨.privateRow 14 3, 13456961918400⟩, ⟨.privateRow 14 4, 50175243724320⟩, ⟨.privateRow 14 5, 13042901551680⟩, ⟨.privateRow 15 0, 1662330589920⟩, ⟨.privateRow 15 1, 5298678755370⟩, ⟨.privateRow 15 2, 6593911340016⟩, ⟨.privateRow 16 0, 1892385269775⟩, ⟨.hall 7 23, 46548892865925450⟩, ⟨.hall 6 24, 219165464587829760⟩, ⟨.hall 5 25, 609280513270228800⟩, ⟨.hall 4 26, 1363093352208107520⟩, ⟨.hall 3 27, 2606189533172493840⟩, ⟨.hall 2 28, 3884959941198336000⟩, ⟨.assumptionRow 16, 44319964525200⟩]
  caps := #[0, 137217888121532400, 71321592327476400, 0, 1934109850615488, 448228529985600, 175647366367200, 0, 21350269820880, 21250405283536, 0, 0, 30707957871000, 0, 0, 5462986985820, 0, 32420115000000, 0, 0, 0, 0, 0] }

theorem case_53_31_16_checked :
    (Witness.linear .conditional case_53_31_16).check 53 31 16 = true := by
  change case_53_31_16.check 53 31 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_31_17 : Certificate := {
  objectiveScale := 17290728000000
  eta := 142120737682233710400
  rows := #[⟨.count 2, 30982555531056729600⟩, ⟨.count 3, 7417036021071156480⟩, ⟨.count 4, 1766549218876041600⟩, ⟨.count 5, 420705000454939200⟩, ⟨.count 6, 100523505530448000⟩, ⟨.count 7, 26175473051527800⟩, ⟨.count 8, 7008385767102720⟩, ⟨.count 9, 1925691250523040⟩, ⟨.count 10, 558981495072000⟩, ⟨.count 11, 179339896335600⟩, ⟨.count 12, 83847224260800⟩, ⟨.count 13, 36333797179680⟩, ⟨.path 11, 8021151238464⟩, ⟨.path 12, 2339154666576⟩, ⟨.privateRow 2 29, 1916850026542651200⟩, ⟨.privateRow 4 24, 50340475992446640⟩, ⟨.privateRow 4 25, 289689364913588640⟩, ⟨.privateRow 5 22, 31130797423549824⟩, ⟨.privateRow 5 23, 100200538444406400⟩, ⟨.privateRow 5 24, 231010282468405440⟩, ⟨.privateRow 6 20, 13860670775952000⟩, ⟨.privateRow 6 21, 36180387813810240⟩, ⟨.privateRow 6 22, 81044553153564000⟩, ⟨.privateRow 6 23, 134058254631100800⟩, ⟨.privateRow 7 18, 5430605042748600⟩, ⟨.privateRow 7 19, 13408180431445800⟩, ⟨.privateRow 7 20, 29409181000519320⟩, ⟨.privateRow 7 21, 48713781614548050⟩, ⟨.privateRow 7 22, 68262121451323800⟩, ⟨.privateRow 8 15, 112253490669320⟩, ⟨.privateRow 8 16, 1883680297534035⟩, ⟨.privateRow 8 17, 5046360719400000⟩, ⟨.privateRow 8 18, 11097788282080500⟩, ⟨.privateRow 8 19, 18505812175754904⟩, ⟨.privateRow 8 20, 25991785521341640⟩, ⟨.privateRow 8 21, 30155369538894600⟩, ⟨.privateRow 9 13, 71052758929152⟩, ⟨.privateRow 9 14, 684062230852000⟩, ⟨.privateRow 9 15, 1872704462969340⟩, ⟨.privateRow 9 16, 4361209115440320⟩, ⟨.privateRow 9 17, 7433625763724160⟩, ⟨.privateRow 9 18, 10581209156437920⟩, ⟨.privateRow 9 19, 12576540184888680⟩, ⟨.privateRow 9 20, 11184081050382240⟩, ⟨.privateRow 10 11, 28457239749120⟩, ⟨.privateRow 10 12, 258249450723264⟩, ⟨.privateRow 10 13, 726365398318560⟩, ⟨.privateRow 10 14, 1751708260181880⟩, ⟨.privateRow 10 15, 3179406889470240⟩, ⟨.privateRow 10 16, 4670756209239120⟩, ⟨.privateRow 10 17, 5753596528776096⟩, ⟨.privateRow 10 18, 1268887993813440⟩, ⟨.privateRow 11 9, 7569541079100⟩, ⟨.privateRow 11 10, 98456967882000⟩, ⟨.privateRow 11 11, 296260192388160⟩, ⟨.privateRow 11 12, 745308660096000⟩, ⟨.privateRow 11 13, 1428896446777800⟩, ⟨.privateRow 11 14, 2251896880147200⟩, ⟨.privateRow 11 15, 1166485689369000⟩, ⟨.privateRow 12 8, 36489069817200⟩, ⟨.privateRow 12 9, 125770836391200⟩, ⟨.privateRow 12 10, 339115440343680⟩, ⟨.privateRow 12 11, 693033538797600⟩, ⟨.privateRow 12 12, 724929126421500⟩, ⟨.privateRow 13 6, 10104665487840⟩, ⟨.privateRow 13 7, 54267786813240⟩, ⟨.privateRow 13 8, 163883211055200⟩, ⟨.privateRow 13 9, 334829915548128⟩, ⟨.privateRow 14 4, 2883634696800⟩, ⟨.privateRow 14 5, 20185442877600⟩, ⟨.privateRow 14 6, 82423891750200⟩, ⟨.privateRow 14 7, 45141990435360⟩, ⟨.privateRow 15 0, 415582647480⟩, ⟨.privateRow 15 3, 8578813222980⟩, ⟨.privateRow 15 4, 25542348872040⟩, ⟨.privateRow 16 1, 3027816431640⟩, ⟨.privateRow 16 2, 3244089033900⟩, ⟨.hall 7 22, 1835147471832675⟩, ⟨.hall 8 22, 4155392823341760⟩, ⟨.hall 7 23, 19503553385391075⟩, ⟨.hall 6 24, 195679298090884608⟩, ⟨.hall 5 25, 469195092426060000⟩, ⟨.hall 4 26, 961467632361075840⟩, ⟨.hall 3 27, 1736481704074242840⟩, ⟨.hall 2 28, 2527921850626972800⟩, ⟨.assumptionRow 17, 18245554420275⟩]
  caps := #[0, 261237344286755655, 0, 6088597146875880, 414760387527486, 0, 219583740841920, 16456058672508, 14018008771403, 10136819564235, 6355390244112, 22168496276784, 12157182648156, 1579109705055, 62637730598040, 5362492348395, 18245554420275, 206533909579725, 17290728000000, 0, 0, 0, 0] }

theorem case_53_31_17_checked :
    (Witness.linear .conditional case_53_31_17).check 53 31 17 = true := by
  change case_53_31_17.check 53 31 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_31_18 : Certificate := {
  objectiveScale := 106309361213471773656000000
  eta := 1144213985824508790229453245230400
  rows := #[⟨.count 2, 224094454306874986233921877555200⟩, ⟨.count 3, 47602991170218032517830813471520⟩, ⟨.count 4, 9924593932717826733081264153600⟩, ⟨.count 5, 2043651286870035577283038089600⟩, ⟨.count 6, 426216043785729344994858211200⟩, ⟨.count 7, 93928814860347611544307307400⟩, ⟨.count 8, 23690420299752698084081448960⟩, ⟨.count 9, 7138854331398692503015615200⟩, ⟨.count 10, 2440633959452544445475424000⟩, ⟨.count 11, 894899118465932963340988800⟩, ⟨.count 12, 488126791890508889095084800⟩, ⟨.count 13, 158641207364415388955902560⟩, ⟨.count 14, 246775211455757271709181760⟩, ⟨.path 9, 214863983838435041490663360⟩, ⟨.path 10, 75805747275932775295286400⟩, ⟨.privateRow 2 29, 11785455295102419245534001182400⟩, ⟨.privateRow 4 24, 347225942618864182577231728200⟩, ⟨.privateRow 4 25, 1811418186089349716228147397600⟩, ⟨.privateRow 5 22, 194896011287429785845291491712⟩, ⟨.privateRow 5 23, 604705028871514925946799247040⟩, ⟨.privateRow 5 24, 1471908375528682515485965263360⟩, ⟨.privateRow 6 20, 77234765585379269919457005600⟩, ⟨.privateRow 6 21, 209018604103026409137676950720⟩, ⟨.privateRow 6 22, 501306215271552629100652089600⟩, ⟨.privateRow 6 23, 899260621745325010359292104000⟩, ⟨.privateRow 7 17, 66100503068506412064959400⟩, ⟨.privateRow 7 18, 26194685073148112438313910800⟩, ⟨.privateRow 7 19, 72886821383539737036961898400⟩, ⟨.privateRow 7 20, 175853778363454458657617987760⟩, ⟨.privateRow 7 21, 321264970038708289238718923850⟩, ⟨.privateRow 7 22, 497957123116081637556027480000⟩, ⟨.privateRow 8 16, 8097311625892035477957526500⟩, ⟨.privateRow 8 17, 25193105069510077185024859320⟩, ⟨.privateRow 8 18, 63513770048425527806150655480⟩, ⟨.privateRow 8 19, 119371339161436186257523946856⟩, ⟨.privateRow 8 20, 188497702925408593512110304990⟩, ⟨.privateRow 8 21, 251299423665779488357183425600⟩, ⟨.privateRow 9 14, 2264064638435360365839794560⟩, ⟨.privateRow 9 15, 8568828547780714550687570220⟩, ⟨.privateRow 9 16, 23448681317102160348529597440⟩, ⟨.privateRow 9 17, 46393739753682367081326170880⟩, ⟨.privateRow 9 18, 75453283582679612662737388704⟩, ⟨.privateRow 9 19, 103420847100985132316835477240⟩, ⟨.privateRow 9 20, 113281573258738099965548198400⟩, ⟨.privateRow 10 12, 556464542755180133568396672⟩, ⟨.privateRow 10 13, 2820288130922940248104934400⟩, ⟨.privateRow 10 14, 8781706065355186482876259980⟩, ⟨.privateRow 10 15, 18822517757292230269855823520⟩, ⟨.privateRow 10 16, 32175691032116044272851006400⟩, ⟨.privateRow 10 17, 45969340626288674630529611040⟩, ⟨.privateRow 10 18, 53788521673884763897721500680⟩, ⟨.privateRow 10 19, 16885119276145853321947475040⟩, ⟨.privateRow 11 10, 99844116523058636405812800⟩, ⟨.privateRow 11 11, 882695948668670241113611680⟩, ⟨.privateRow 11 12, 3284686537096549399535674800⟩, ⟨.privateRow 11 13, 7919348733015287445474943500⟩, ⟨.privateRow 11 14, 14623465140386495469140248800⟩, ⟨.privateRow 11 15, 22219938339182540055682506000⟩, ⟨.privateRow 11 16, 17129182672091107766495017440⟩, ⟨.privateRow 12 9, 244063395945254444547542400⟩, ⟨.privateRow 12 10, 1209130740745448060695949640⟩, ⟨.privateRow 12 11, 3404458388810424265841413200⟩, ⟨.privateRow 12 12, 7035890086234288284222120750⟩, ⟨.privateRow 12 13, 11600275098945575831619798000⟩, ⟨.privateRow 13 7, 34575647758911046310901840⟩, ⟨.privateRow 13 8, 417126531251889414317617920⟩, ⟨.privateRow 13 9, 1466821009630979211730729824⟩, ⟨.privateRow 13 10, 3537563333450938032358545120⟩, ⟨.privateRow 13 11, 2655714827129299924732945740⟩, ⟨.privateRow 14 5, 1355907755251413580819680⟩, ⟨.privateRow 14 6, 105760804909610259303935040⟩, ⟨.privateRow 14 7, 613733155763344383536471520⟩, ⟨.privateRow 14 8, 1803221723708854921132092432⟩, ⟨.privateRow 15 4, 23728385716899737664344400⟩, ⟨.privateRow 15 5, 205646009546464393090984800⟩, ⟨.privateRow 15 6, 499158950444599935957208560⟩, ⟨.privateRow 16 2, 4721464504893315147497100⟩, ⟨.privateRow 16 3, 71185157150699212993033200⟩, ⟨.privateRow 16 4, 104659129858468485769519050⟩, ⟨.privateRow 17 1, 25181144026097680786651200⟩, ⟨.privateRow 17 2, 13559077552514135808196800⟩, ⟨.hall 8 22, 154695869511700362760999244160⟩, ⟨.hall 7 23, 636660766242458779972836660975⟩, ⟨.hall 6 24, 1636542695171309152469090808960⟩, ⟨.hall 5 25, 3510004508325453051328385124000⟩, ⟨.hall 4 26, 6711886210778050373954595672960⟩, ⟨.hall 3 27, 11631731965166300733635731601760⟩, ⟨.hall 2 28, 16644526068945245771054016662400⟩, ⟨.assumptionRow 18, 81456897999369309296508720⟩]
  caps := #[0, 0, 0, 13643445186671625009158816160, 0, 752476824625818682492909248, 1778325641406777731978119200, 1184552430023915851651740, 35290280482433835592129200, 101835876481163885378961632, 23611495304574449098016400, 180701887791718067539264200, 57489401008467058139875410, 60877023419590074574132320, 70695315376667674648025616, 99913301162027611004732040, 81456897999369309296508720, 81456897999369309296508720, 1194255436562291974575491280, 106309361213471773656000000, 0, 0, 0] }

theorem case_53_31_18_checked :
    (Witness.linear .conditional case_53_31_18).check 53 31 18 = true := by
  change case_53_31_18.check 53 31 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_31_19 : Certificate := {
  objectiveScale := 21370678694164800000
  eta := 227761787170860184508666400
  rows := #[⟨.count 2, 46818982705616424283780800⟩, ⟨.count 3, 10391968067133809836920240⟩, ⟨.count 4, 2259035483057643807316800⟩, ⟨.count 5, 478616836713128835321600⟩, ⟨.count 6, 98591681423768135803200⟩, ⟨.count 7, 20907072540245517525900⟩, ⟨.count 8, 4186045088899656222240⟩, ⟨.count 9, 785875721493803981040⟩, ⟨.count 10, 164869032481217618400⟩, ⟨.count 11, 33584432542470255600⟩, ⟨.count 12, 36637562773603915200⟩, ⟨.path 10, 27848606429576116800⟩, ⟨.path 11, 6404359677456443136⟩, ⟨.privateRow 2 29, 3051182334046196325175200⟩, ⟨.privateRow 4 24, 67001858861297500019880⟩, ⟨.privateRow 4 25, 412941970021289728219200⟩, ⟨.privateRow 5 22, 38325333165374602226880⟩, ⟨.privateRow 5 23, 134431054183946007928440⟩, ⟨.privateRow 5 24, 343098698548553070483360⟩, ⟨.privateRow 6 20, 15461729963845548583200⟩, ⟨.privateRow 6 21, 45136256084987570062560⟩, ⟨.privateRow 6 22, 114514264434168692893800⟩, ⟨.privateRow 6 23, 216481859801839785753600⟩, ⟨.privateRow 7 18, 5351155931888726602500⟩, ⟨.privateRow 7 19, 15294147037825545489600⟩, ⟨.privateRow 7 20, 39063580055262721118160⟩, ⟨.privateRow 7 21, 75920853713124592297125⟩, ⟨.privateRow 7 22, 125369668970964419601600⟩, ⟨.privateRow 8 15, 74603802592238219300⟩, ⟨.privateRow 8 16, 1599865683865963744230⟩, ⟨.privateRow 8 17, 5143913813413989694080⟩, ⟨.privateRow 8 18, 13631658260552106905130⟩, ⟨.privateRow 8 19, 27452861630586838361916⟩, ⟨.privateRow 8 20, 46670466747508197068475⟩, ⟨.privateRow 8 21, 67547826393962667993240⟩, ⟨.privateRow 9 13, 32810972883916395168⟩, ⟨.privateRow 9 14, 475994310923482471120⟩, ⟨.privateRow 9 15, 1659732479148109586220⟩, ⟨.privateRow 9 16, 4839996506977713407040⟩, ⟨.privateRow 9 17, 10292678711528558425080⟩, ⟨.privateRow 9 18, 18189979999451198947008⟩, ⟨.privateRow 9 19, 27316457948960556896520⟩, ⟨.privateRow 9 20, 33603022713210936105120⟩, ⟨.privateRow 10 11, 5329100039796933120⟩, ⟨.privateRow 10 12, 135375794448466466664⟩, ⟨.privateRow 10 13, 533687164402163698080⟩, ⟨.privateRow 10 14, 1709600272923292693020⟩, ⟨.privateRow 10 15, 3999513370492775971440⟩, ⟨.privateRow 10 16, 7473146866745858602920⟩, ⟨.privateRow 10 17, 11769084289764785679696⟩, ⟨.privateRow 10 18, 15455097886510141578180⟩, ⟨.privateRow 10 19, 15168561614318247624720⟩, ⟨.privateRow 11 10, 29421073136378901600⟩, ⟨.privateRow 11 11, 166548254108341131180⟩, ⟨.privateRow 11 12, 610286809534383735600⟩, ⟨.privateRow 11 13, 1584765410597815186125⟩, ⟨.privateRow 11 14, 3239589255963608097000⟩, ⟨.privateRow 11 15, 5439660361803136854000⟩, ⟨.privateRow 11 16, 7681065035486060821680⟩, ⟨.privateRow 11 17, 3536669731489452939150⟩, ⟨.privateRow 12 8, 2417061432980813850⟩, ⟨.privateRow 12 9, 43437716470219793400⟩, ⟨.privateRow 12 10, 215550994318036367760⟩, ⟨.privateRow 12 11, 645058570500072636600⟩, ⟨.privateRow 12 12, 1464548407746927339375⟩, ⟨.privateRow 12 13, 2697658639937383518000⟩, ⟨.privateRow 12 14, 3452835863892907869300⟩, ⟨.privateRow 13 0, 192829277755810080⟩, ⟨.privateRow 13 7, 4579695346700489400⟩, ⟨.privateRow 13 8, 67113353626192626480⟩, ⟨.privateRow 13 9, 264706391039288287320⟩, ⟨.privateRow 13 10, 691839310374887265360⟩, ⟨.privateRow 13 11, 1422453374685172007640⟩, ⟨.privateRow 13 12, 745312705565885360640⟩, ⟨.privateRow 14 6, 10584184801263353280⟩, ⟨.privateRow 14 7, 99106457684556853440⟩, ⟨.privateRow 14 8, 334724844339953547480⟩, ⟨.privateRow 14 9, 677681832414223036400⟩, ⟨.privateRow 15 5, 21995259040125406035⟩, ⟨.privateRow 15 6, 151125320486220493140⟩, ⟨.privateRow 15 7, 201893325084098463816⟩, ⟨.privateRow 16 3, 763282557783414900⟩, ⟨.privateRow 16 4, 43825140192731072175⟩, ⟨.privateRow 16 5, 68556651553637629200⟩, ⟨.privateRow 17 2, 4070840308178212800⟩, ⟨.privateRow 17 3, 26460462003158383200⟩, ⟨.privateRow 18 1, 6920428523902961760⟩, ⟨.hall 8 21, 86388702034026974400⟩, ⟨.hall 9 21, 2006905768112276282160⟩, ⟨.hall 8 22, 61378147844474066686080⟩, ⟨.hall 7 23, 194849053965195142988475⟩, ⟨.hall 6 24, 450213118380458500459392⟩, ⟨.hall 5 25, 907406588054156345971200⟩, ⟨.hall 4 26, 1664063174762626508270400⟩, ⟨.hall 3 27, 2798260196992306941917880⟩, ⟨.hall 2 28, 3934442592438589871640000⟩, ⟨.assumptionRow 19, 7627264611267852720⟩]
  caps := #[0, 50216350878680073993360, 6845804266532980301280, 0, 0, 17211090476398124160, 145548858174927595080, 24091763089742435925, 15170004382824990816, 80242395707613356624, 0, 4957244712309861726, 434449897716085320, 0, 56513725451478986600, 7627264611267852720, 58469558110266584925, 7627264611267852720, 7627264611267852720, 227450201024544947280, 21370678694164800000, 0, 0] }

theorem case_53_31_19_checked :
    (Witness.linear .conditional case_53_31_19).check 53 31 19 = true := by
  change case_53_31_19.check 53 31 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_31_20 : Certificate := {
  objectiveScale := 225523325527500000
  eta := 3544110839982499059873600
  rows := #[⟨.count 2, 672396955443343834704000⟩, ⟨.count 3, 136794930272976970874880⟩, ⟨.count 4, 27252115015319630916480⟩, ⟨.count 5, 5343551963788162924800⟩, ⟨.count 6, 1047755287017286848000⟩, ⟨.count 7, 209895713747870950800⟩, ⟨.count 8, 43748378650897240320⟩, ⟨.count 9, 9098927492518543680⟩, ⟨.count 10, 1908865907521372800⟩, ⟨.count 11, 291632291426876400⟩, ⟨.path 8, 2013819651945541440⟩, ⟨.path 11, 84083992325161920⟩, ⟨.path 12, 28324904194281240⟩, ⟨.privateRow 2 29, 43639007704269997219200⟩, ⟨.privateRow 4 26, 22502681658031599264240⟩, ⟨.privateRow 6 24, 14103567384300018424800⟩, ⟨.privateRow 7 18, 44042157153992626200⟩, ⟨.privateRow 7 22, 3299107971450868176600⟩, ⟨.privateRow 8 16, 15169187358502742565⟩, ⟨.privateRow 8 17, 51261886959113310480⟩, ⟨.privateRow 8 19, 381093413144985004464⟩, ⟨.privateRow 8 20, 301735140989276554560⟩, ⟨.privateRow 9 14, 4197148371969833280⟩, ⟨.privateRow 9 16, 84700117249981421760⟩, ⟨.privateRow 9 17, 41802985062429470880⟩, ⟨.privateRow 9 19, 825750647035685411040⟩, ⟨.privateRow 9 20, 38341103558541944160⟩, ⟨.privateRow 10 12, 1037150476419945888⟩, ⟨.privateRow 10 13, 4899422495971523520⟩, ⟨.privateRow 10 14, 7408785803567328180⟩, ⟨.privateRow 10 15, 62938035922276120320⟩, ⟨.privateRow 10 16, 60500444457830176800⟩, ⟨.privateRow 10 17, 65785882059544911264⟩, ⟨.privateRow 10 18, 336660317223186116160⟩, ⟨.privateRow 10 19, 338325272486968646880⟩, ⟨.privateRow 11 10, 224147133080161200⟩, ⟨.privateRow 11 11, 1346810945862301920⟩, ⟨.privateRow 11 12, 5738380845450052800⟩, ⟨.privateRow 11 13, 10104396097278933450⟩, ⟨.privateRow 11 14, 48070091464804094400⟩, ⟨.privateRow 11 15, 59444382069178306200⟩, ⟨.privateRow 11 16, 68607822159497340720⟩, ⟨.privateRow 11 17, 157136781026099674800⟩, ⟨.privateRow 11 18, 213333439849842312000⟩, ⟨.privateRow 12 8, 37558704198915900⟩, ⟨.privateRow 12 9, 327785054826902400⟩, ⟨.privateRow 12 10, 1778956977703946040⟩, ⟨.privateRow 12 11, 6233272006659297600⟩, ⟨.privateRow 12 12, 11254355246428093800⟩, ⟨.privateRow 12 13, 38518187062484844000⟩, ⟨.privateRow 12 14, 54345235640290194600⟩, ⟨.privateRow 12 15, 61810138566601785360⟩, ⟨.privateRow 12 16, 89928793865451340800⟩, ⟨.privateRow 12 17, 123121851035128545600⟩, ⟨.privateRow 13 6, 4894527968003520⟩, ⟨.privateRow 13 7, 60977660934710520⟩, ⟨.privateRow 13 8, 494569803312355680⟩, ⟨.privateRow 13 9, 2230191668620803888⟩, ⟨.privateRow 13 10, 6871917267076942080⟩, ⟨.privateRow 13 11, 12280370671720831680⟩, ⟨.privateRow 13 12, 33314255005075387200⟩, ⟨.privateRow 13 13, 50987929352015335680⟩, ⟨.privateRow 13 14, 58074063793158565152⟩, ⟨.privateRow 13 16, 119823754939355507040⟩, ⟨.privateRow 14 5, 3534936865780320⟩, ⟨.privateRow 14 6, 107226418262003040⟩, ⟨.privateRow 14 7, 731089215422748000⟩, ⟨.privateRow 14 8, 2881327039297538832⟩, ⟨.privateRow 14 9, 8067511469236419200⟩, ⟨.privateRow 14 10, 14257284113908475640⟩, ⟨.privateRow 14 11, 32423955905879572320⟩, ⟨.privateRow 14 12, 52502649799002202800⟩, ⟨.privateRow 14 14, 136277118581130006480⟩, ⟨.privateRow 15 4, 6186139515115560⟩, ⟨.privateRow 15 5, 187646231958505320⟩, ⟨.privateRow 15 6, 1133188283905259400⟩, ⟨.privateRow 15 7, 4037074647564414456⟩, ⟨.privateRow 15 8, 10552866663952132520⟩, ⟨.privateRow 15 9, 18687554207724717315⟩, ⟨.privateRow 15 10, 37280327920735699800⟩, ⟨.privateRow 15 11, 62472791939899521180⟩, ⟨.privateRow 15 13, 141458452292147510520⟩, ⟨.privateRow 16 3, 13256013246676200⟩, ⟨.privateRow 16 4, 359017025430813750⟩, ⟨.privateRow 16 5, 1926942289221385800⟩, ⟨.privateRow 16 6, 6410608006092610320⟩, ⟨.privateRow 16 7, 15949929716472952200⟩, ⟨.privateRow 16 8, 28347984328017053700⟩, ⟨.privateRow 16 10, 184276258813128081600⟩, ⟨.privateRow 16 12, 43943683912731603000⟩, ⟨.privateRow 17 2, 35349368657803200⟩, ⟨.privateRow 17 3, 765902987585736000⟩, ⟨.privateRow 17 4, 3801663920198289600⟩, ⟨.privateRow 17 5, 12039994964847769920⟩, ⟨.privateRow 17 6, 29308554324947497600⟩, ⟨.privateRow 17 7, 53766389728518667200⟩, ⟨.privateRow 17 8, 34006092648806678400⟩, ⟨.privateRow 17 9, 189024857336159644800⟩, ⟨.privateRow 18 1, 120187853436530880⟩, ⟨.privateRow 18 2, 1822849110454051680⟩, ⟨.privateRow 18 3, 8948531996774435520⟩, ⟨.privateRow 18 4, 27967713494680735776⟩, ⟨.privateRow 18 5, 67011405393834661760⟩, ⟨.privateRow 18 6, 126753114930501379320⟩, ⟨.privateRow 18 7, 133253990074416594240⟩, ⟨.privateRow 18 8, 287489345420181864960⟩, ⟨.privateRow 18 10, 499981470295968460800⟩, ⟨.privateRow 19 0, 540845340464388960⟩, ⟨.privateRow 19 1, 5859157855030880400⟩, ⟨.privateRow 19 2, 26845595990323306560⟩, ⟨.privateRow 19 3, 82965675227237266464⟩, ⟨.privateRow 19 4, 199992588118387384320⟩, ⟨.privateRow 19 5, 387583292110292738460⟩, ⟨.privateRow 19 6, 518284363405017306240⟩, ⟨.privateRow 19 7, 764034184296026804160⟩, ⟨.privateRow 19 10, 3606897575557009974240⟩, ⟨.privateRow 20 0, 25975599823970236440⟩, ⟨.privateRow 20 1, 109299926532030605280⟩, ⟨.privateRow 20 2, 338424957706583651904⟩, ⟨.privateRow 20 8, 27174188215847720207160⟩, ⟨.privateRow 21 0, 1012036356778061160000⟩, ⟨.privateRow 21 1, 1959302386722326405760⟩, ⟨.privateRow 21 2, 1533797322939194913600⟩, ⟨.privateRow 21 7, 54326111631846323068800⟩, ⟨.privateRow 21 8, 203797134618920769326400⟩, ⟨.privateRow 22 1, 97668255338128089014400⟩, ⟨.privateRow 22 6, 210402358574158915164000⟩, ⟨.hall 15 8, 77822170696648560⟩, ⟨.hall 19 10, 272237779973298452040⟩, ⟨.hall 20 10, 5424514872330407817600⟩, ⟨.hall 14 12, 50029753523926176⟩, ⟨.hall 16 14, 38233877140279941120⟩, ⟨.hall 10 15, 15254284445957700⟩, ⟨.hall 9 18, 468445218463861704⟩, ⟨.hall 6 19, 230749141650039792⟩, ⟨.hall 8 19, 1055620172241586224⟩, ⟨.hall 11 19, 16929254517330175020⟩, ⟨.hall 7 21, 7869142343178002250⟩, ⟨.hall 8 22, 226238418496455805440⟩, ⟨.hall 7 23, 5741120237409737455275⟩, ⟨.hall 6 24, 104113788520454608896⟩, ⟨.hall 3 25, 69118746784347803400⟩, ⟨.hall 5 25, 8889394109799415212000⟩, ⟨.hall 4 26, 40802654488403492805120⟩, ⟨.hall 2 28, 56414396307349743062400⟩]
  caps := #[0, 4569495351203882408400, 774429159413046337200, 0, 0, 6268905524243762400, 1108934678902056864, 0, 0, 737784504276568320, 0, 547509275299801620, 142645160193273540, 0, 68166306705362216, 68089157125063620, 1966331242500342900, 141397474631212800, 23312719908486461752, 0, 55890654735093851400, 4396961251105770984000, 0] }

theorem case_53_31_20_checked :
    (Witness.linear .conditional case_53_31_20).check 53 31 20 = true := by
  change case_53_31_20.check 53 31 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_32_1_checked :
    (Witness.rising).check 53 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_32_2_checked :
    (Witness.rising).check 53 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_32_3_checked :
    (Witness.rising).check 53 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_32_4_checked :
    (Witness.rising).check 53 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_32_5_checked :
    (Witness.rising).check 53 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_32_6_checked :
    (Witness.rising).check 53 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_32_7_checked :
    (Witness.rising).check 53 32 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_32_8_checked :
    (Witness.rising).check 53 32 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_32_9_checked :
    (Witness.rising).check 53 32 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_32_10_checked :
    (Witness.rising).check 53 32 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_32_11_checked :
    (Witness.linear .positive case_53_32_11).check 53 32 11 = true := by
  change case_53_32_11.check 53 32 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_32_12_checked :
    (Witness.linear .positive case_53_32_12).check 53 32 12 = true := by
  change case_53_32_12.check 53 32 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_32_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_32_13_checked :
    (Witness.linear .positive case_53_32_13).check 53 32 13 = true := by
  change case_53_32_13.check 53 32 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_32_14 : Certificate := {
  objectiveScale := 540078739200000
  eta := 10417884297317825328000
  rows := #[⟨.count 2, 2020320808587657576000⟩, ⟨.count 3, 421321988701935921600⟩, ⟨.count 4, 85111435442771337600⟩, ⟨.count 5, 17758748934854928000⟩, ⟨.count 6, 3796881805276560000⟩, ⟨.count 7, 799676597760440400⟩, ⟨.count 8, 186513492189024000⟩, ⟨.count 9, 43349014942833600⟩, ⟨.count 10, 10760393780136000⟩, ⟨.count 11, 3074398222896000⟩, ⟨.count 12, 922319466868800⟩, ⟨.path 12, 441884709002880⟩, ⟨.path 13, 49099158268160⟩, ⟨.privateRow 2 30, 62610580969010474400⟩, ⟨.privateRow 5 25, 20526253895145398400⟩, ⟨.privateRow 6 20, 327112310918250000⟩, ⟨.privateRow 6 21, 760764110253147000⟩, ⟨.privateRow 6 22, 1357218715482630000⟩, ⟨.privateRow 6 24, 11369551628022588000⟩, ⟨.privateRow 7 17, 31825714937016000⟩, ⟨.privateRow 7 18, 176063740729326450⟩, ⟨.privateRow 7 19, 357848973151441200⟩, ⟨.privateRow 7 20, 608722308138344400⟩, ⟨.privateRow 7 23, 8794444216519962000⟩, ⟨.privateRow 7 25, 1910764115515054800⟩, ⟨.privateRow 8 15, 30441666403708560⟩, ⟨.privateRow 8 16, 76011649396082400⟩, ⟨.privateRow 8 17, 150105891983822775⟩, ⟨.privateRow 8 18, 244894118443088400⟩, ⟨.privateRow 8 19, 436863447478458000⟩, ⟨.privateRow 8 20, 255090506549238360⟩, ⟨.privateRow 9 12, 2988998272260000⟩, ⟨.privateRow 9 13, 15371991114480000⟩, ⟨.privateRow 9 14, 35140371687701280⟩, ⟨.privateRow 9 15, 62740497067248000⟩, ⟨.privateRow 9 16, 101621671259308200⟩, ⟨.privateRow 9 17, 177363497478024000⟩, ⟨.privateRow 9 18, 262826888077353600⟩, ⟨.privateRow 9 19, 209919910659338880⟩, ⟨.privateRow 9 20, 132224743569718800⟩, ⟨.privateRow 10 9, 219599873064000⟩, ⟨.privateRow 10 10, 2678273836484400⟩, ⟨.privateRow 10 11, 7666780568346900⟩, ⟨.privateRow 10 12, 16580788597573200⟩, ⟨.privateRow 10 13, 29022319224138240⟩, ⟨.privateRow 10 14, 45168033891380400⟩, ⟨.privateRow 10 15, 79184969228465100⟩, ⟨.privateRow 10 16, 118386291568802400⟩, ⟨.privateRow 10 17, 165556344302949600⟩, ⟨.privateRow 10 18, 156763565385467040⟩, ⟨.privateRow 10 19, 131680318884414300⟩, ⟨.privateRow 10 21, 278809488838881000⟩, ⟨.privateRow 11 7, 414577942178400⟩, ⟨.privateRow 11 8, 1671953579010000⟩, ⟨.privateRow 11 9, 4213860501312000⟩, ⟨.privateRow 11 10, 8442949665150000⟩, ⟨.privateRow 11 11, 14825713744296000⟩, ⟨.privateRow 11 12, 23176770239422800⟩, ⟨.privateRow 11 13, 39516886248840000⟩, ⟨.privateRow 11 14, 60684428558754000⟩, ⟨.privateRow 11 15, 86212913802444000⟩, ⟨.privateRow 11 16, 116140051049022000⟩, ⟨.privateRow 11 17, 121396806192261600⟩, ⟨.privateRow 11 21, 696980051667900000⟩, ⟨.privateRow 12 4, 45211738572000⟩, ⟨.privateRow 12 5, 365084788968900⟩, ⟨.privateRow 12 6, 1086287372089920⟩, ⟨.privateRow 12 7, 2530888537062600⟩, ⟨.privateRow 12 8, 4954510982282400⟩, ⟨.privateRow 12 9, 8608315024108800⟩, ⟨.privateRow 12 10, 13771906584836400⟩, ⟨.privateRow 12 11, 23657494325184720⟩, ⟨.privateRow 12 12, 36098559133837200⟩, ⟨.privateRow 12 13, 53081406817188750⟩, ⟨.privateRow 12 14, 73126757730312000⟩, ⟨.privateRow 12 15, 96241474369240200⟩, ⟨.privateRow 12 19, 498052512109152000⟩, ⟨.privateRow 13 2, 85399950636000⟩, ⟨.privateRow 13 3, 289355126860800⟩, ⟨.privateRow 13 4, 787814544617100⟩, ⟨.privateRow 13 5, 1748990989025280⟩, ⟨.privateRow 13 6, 3411118028260800⟩, ⟨.privateRow 13 7, 5975368853731200⟩, ⟨.privateRow 13 8, 9624574436677200⟩, ⟨.privateRow 13 9, 16890557509425600⟩, ⟨.privateRow 13 10, 26347592770218720⟩, ⟨.privateRow 13 12, 132839623214298000⟩, ⟨.privateRow 13 15, 95736760660981440⟩, ⟨.privateRow 13 19, 1340232665301129600⟩, ⟨.privateRow 14 1, 499589711220600⟩, ⟨.privateRow 14 2, 509385587911200⟩, ⟨.privateRow 14 3, 1436320419759225⟩, ⟨.privateRow 14 4, 2819906370000720⟩, ⟨.privateRow 14 5, 5007792105330300⟩, ⟨.privateRow 14 6, 8211205253651400⟩, ⟨.privateRow 14 7, 14432591657484000⟩, ⟨.privateRow 14 8, 23223352030678800⟩, ⟨.privateRow 14 9, 35037891746938080⟩, ⟨.privateRow 14 11, 146005093104220350⟩, ⟨.privateRow 14 13, 119679490821290400⟩, ⟨.privateRow 14 17, 251293624743961800⟩, ⟨.privateRow 15 0, 1665299037402000⟩, ⟨.privateRow 15 1, 842445395391600⟩, ⟨.privateRow 15 2, 2872640839518450⟩, ⟨.privateRow 15 3, 155427910157520⟩, ⟨.privateRow 15 4, 18579979260156600⟩, ⟨.privateRow 15 5, 10273614061510800⟩, ⟨.privateRow 15 6, 24757445689376400⟩, ⟨.privateRow 15 7, 38544103174777200⟩, ⟨.privateRow 15 8, 56686779233164080⟩, ⟨.privateRow 15 9, 15024697981893600⟩, ⟨.privateRow 15 10, 166862963547680400⟩, ⟨.privateRow 15 11, 104057399851376400⟩, ⟨.privateRow 15 13, 186247044343039680⟩, ⟨.privateRow 16 0, 12195866479797000⟩, ⟨.privateRow 16 3, 18377764377043500⟩, ⟨.privateRow 16 4, 71159508867447000⟩, ⟨.privateRow 16 5, 26228459839081500⟩, ⟨.privateRow 16 6, 78571836401058000⟩, ⟨.privateRow 16 7, 113406864447076200⟩, ⟨.privateRow 16 11, 1212337699228656000⟩, ⟨.privateRow 17 0, 57952406501589600⟩, ⟨.privateRow 17 2, 32354381298096000⟩, ⟨.privateRow 17 4, 472056767135553600⟩, ⟨.privateRow 17 6, 290961047814877440⟩, ⟨.privateRow 17 7, 114572573773257600⟩, ⟨.privateRow 17 8, 666119614960800⟩, ⟨.privateRow 17 12, 4953931576463469600⟩, ⟨.privateRow 18 2, 1168988684285822400⟩, ⟨.privateRow 18 5, 1321514704120731120⟩, ⟨.privateRow 18 6, 1499805319729516800⟩, ⟨.privateRow 18 8, 470756247887296800⟩, ⟨.privateRow 18 11, 4422035063917270800⟩, ⟨.privateRow 18 14, 45409374151877736000⟩, ⟨.privateRow 19 1, 5064456192576580800⟩, ⟨.privateRow 19 2, 1557054599970870000⟩, ⟨.privateRow 19 4, 4402784207044903680⟩, ⟨.privateRow 19 5, 7549355636222400000⟩, ⟨.privateRow 19 6, 3821861290837590000⟩, ⟨.privateRow 20 0, 32918965251747775200⟩, ⟨.privateRow 20 2, 48703638429502056000⟩, ⟨.privateRow 20 5, 133773638204406400200⟩, ⟨.hall 15 2, 342855684171000⟩, ⟨.hall 18 6, 34820554418020800⟩, ⟨.hall 16 8, 39128704655040⟩, ⟨.hall 19 8, 397212250398163200⟩, ⟨.hall 14 11, 25860695835975⟩, ⟨.hall 20 11, 3376883396249551188000⟩, ⟨.hall 18 12, 172473740304465600⟩, ⟨.hall 8 14, 472777905600⟩, ⟨.hall 15 14, 1684890790783200⟩, ⟨.hall 10 20, 5862651156648000⟩, ⟨.hall 6 21, 447397852061160⟩, ⟨.hall 5 22, 1267186745784960⟩, ⟨.hall 4 23, 2291814764144048⟩, ⟨.hall 8 23, 3497294508447940200⟩, ⟨.hall 7 24, 9790186461747964272⟩, ⟨.hall 3 28, 110807619770215368000⟩, ⟨.hall 2 29, 111149917967666017440⟩]
  caps := #[0, 1922103417445411200, 549972576643089600, 105215948151394080, 20670854718228000, 3868545431836800, 5227781700391250, 1176032866986120, 0, 389197841440320, 1110963357015600, 103212923676720, 1614494248456870, 589177897468160, 8976111889805775, 0, 13230990213012000, 0, 0, 1083672669601304640, 5214539230369068600, 0] }

theorem case_53_32_14_checked :
    (Witness.linear .positive case_53_32_14).check 53 32 14 = true := by
  change case_53_32_14.check 53 32 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_32_15 : Certificate := {
  objectiveScale := 213188976000000
  eta := 4716233453060857728000
  rows := #[⟨.count 2, 1003490548589226297600⟩, ⟨.count 3, 222721089979833244800⟩, ⟨.count 4, 47107979170027776000⟩, ⟨.count 5, 10879953711026400000⟩, ⟨.count 6, 2428005996532116000⟩, ⟨.count 7, 559540476567072000⟩, ⟨.count 8, 133223922992160000⟩, ⟨.count 9, 31358861873539200⟩, ⟨.count 10, 8198395261056000⟩, ⟨.count 11, 2049598815264000⟩, ⟨.count 12, 614879644579200⟩, ⟨.path 12, 186541481984000⟩, ⟨.privateRow 2 30, 74444195928789086400⟩, ⟨.privateRow 3 28, 35330984377520832000⟩, ⟨.privateRow 3 29, 64365806154432182400⟩, ⟨.privateRow 6 21, 679997106939150000⟩, ⟨.privateRow 6 22, 817217747621074800⟩, ⟨.privateRow 6 25, 14743447477799040000⟩, ⟨.privateRow 7 18, 63059323549622400⟩, ⟨.privateRow 7 19, 195648846908486400⟩, ⟨.privateRow 7 20, 462175992846968400⟩, ⟨.privateRow 7 21, 748096735575309120⟩, ⟨.privateRow 7 23, 2103235677593450400⟩, ⟨.privateRow 7 24, 560761695861166800⟩, ⟨.privateRow 8 15, 3585943927205640⟩, ⟨.privateRow 8 16, 33429336232292000⟩, ⟨.privateRow 8 18, 314963557940631600⟩, ⟨.privateRow 9 13, 3757597827984000⟩, ⟨.privateRow 9 14, 14511159612069120⟩, ⟨.privateRow 9 15, 27965637168268800⟩, ⟨.privateRow 9 16, 25355245343828400⟩, ⟨.privateRow 9 17, 209644678818432000⟩, ⟨.privateRow 9 18, 60246818508676800⟩, ⟨.privateRow 9 19, 85864526367459840⟩, ⟨.privateRow 9 20, 110336736221712000⟩, ⟨.privateRow 9 21, 103664153412019200⟩, ⟨.privateRow 10 11, 2476598568444000⟩, ⟨.privateRow 10 12, 6698461582612800⟩, ⟨.privateRow 10 13, 14285703742390080⟩, ⟨.privateRow 10 14, 23735492946765600⟩, ⟨.privateRow 10 15, 28002643813544400⟩, ⟨.privateRow 10 16, 138230800098019200⟩, ⟨.privateRow 10 18, 215669035336154400⟩, ⟨.privateRow 10 20, 200860683895872000⟩, ⟨.privateRow 11 8, 136418102964000⟩, ⟨.privateRow 11 9, 1200376928520000⟩, ⟨.privateRow 11 10, 3481988896386000⟩, ⟨.privateRow 11 11, 6995738104992000⟩, ⟨.privateRow 11 12, 12502552773110400⟩, ⟨.privateRow 11 13, 22385138575800000⟩, ⟨.privateRow 11 15, 144450134684856000⟩, ⟨.privateRow 11 16, 6909632369640000⟩, ⟨.privateRow 11 17, 103253198498049600⟩, ⟨.privateRow 11 18, 74961747578718000⟩, ⟨.privateRow 12 6, 143471917068480⟩, ⟨.privateRow 12 7, 633179634001200⟩, ⟨.privateRow 12 9, 7553625633754200⟩, ⟨.privateRow 12 10, 647486898458400⟩, ⟨.privateRow 12 12, 48393305360400000⟩, ⟨.privateRow 12 14, 86910309762962400⟩, ⟨.privateRow 12 15, 38575157702281200⟩, ⟨.privateRow 12 16, 37333442420033760⟩, ⟨.privateRow 12 17, 53878828856252400⟩, ⟨.privateRow 13 4, 111019935826800⟩, ⟨.privateRow 13 5, 391701106917120⟩, ⟨.privateRow 13 6, 644159627654400⟩, ⟨.privateRow 13 7, 919691776080000⟩, ⟨.privateRow 13 8, 8443208452879200⟩, ⟨.privateRow 13 9, 801206809603200⟩, ⟨.privateRow 13 11, 48537536388140800⟩, ⟨.privateRow 13 13, 92758986382233600⟩, ⟨.privateRow 13 14, 58356632934600000⟩, ⟨.privateRow 13 16, 24014466118843200⟩, ⟨.privateRow 13 19, 1078430576631408000⟩, ⟨.privateRow 14 2, 84897597985200⟩, ⟨.privateRow 14 3, 284488585556175⟩, ⟨.privateRow 14 4, 414474427086720⟩, ⟨.privateRow 14 5, 1363959211586400⟩, ⟨.privateRow 14 7, 14802658110240000⟩, ⟨.privateRow 14 10, 54399768555132000⟩, ⟨.privateRow 14 12, 116285452783156800⟩, ⟨.privateRow 14 13, 82913388739981800⟩, ⟨.privateRow 14 14, 41832311819538240⟩, ⟨.privateRow 15 1, 378773898703200⟩, ⟨.privateRow 15 2, 444079743307200⟩, ⟨.privateRow 15 3, 843751512283680⟩, ⟨.privateRow 15 5, 4679917294852800⟩, ⟨.privateRow 15 6, 23036636684061000⟩, ⟨.privateRow 15 7, 2119471502148000⟩, ⟨.privateRow 15 9, 69942559570884000⟩, ⟨.privateRow 15 11, 178456616846164800⟩, ⟨.privateRow 15 14, 201001593814421400⟩, ⟨.privateRow 15 16, 492817495135165200⟩, ⟨.privateRow 16 0, 1273463969778000⟩, ⟨.privateRow 16 1, 797955788755125⟩, ⟨.privateRow 16 2, 1702305682677600⟩, ⟨.privateRow 16 3, 237899862486000⟩, ⟨.privateRow 16 4, 10034494199730000⟩, ⟨.privateRow 16 5, 46859664580228500⟩, ⟨.privateRow 16 7, 24923975593116600⟩, ⟨.privateRow 16 8, 94120234484276000⟩, ⟨.privateRow 16 9, 59811990426688500⟩, ⟨.privateRow 16 10, 210224178483462000⟩, ⟨.privateRow 16 11, 210012711939030000⟩, ⟨.privateRow 16 14, 576933599846604000⟩, ⟨.privateRow 16 16, 917579769608502000⟩, ⟨.privateRow 17 0, 10657913839372800⟩, ⟨.privateRow 17 3, 25415025309273600⟩, ⟨.privateRow 17 4, 66611961496080000⟩, ⟨.privateRow 17 5, 125795680013203200⟩, ⟨.privateRow 17 8, 595955015518262400⟩, ⟨.privateRow 17 9, 185752212629068800⟩, ⟨.privateRow 17 15, 10290215811914438400⟩, ⟨.privateRow 18 1, 131035244257288800⟩, ⟨.privateRow 18 3, 222076878298875600⟩, ⟨.privateRow 18 4, 415214559992232000⟩, ⟨.privateRow 18 6, 65427748847260800⟩, ⟨.privateRow 18 7, 1549505244334647600⟩, ⟨.privateRow 18 9, 1819394708329598400⟩, ⟨.privateRow 19 0, 611497806534014400⟩, ⟨.privateRow 19 1, 132404083466054400⟩, ⟨.privateRow 19 2, 887049287256132000⟩, ⟨.privateRow 19 3, 1894201959633984000⟩, ⟨.privateRow 19 4, 783623115039885120⟩, ⟨.privateRow 19 6, 3816199274110423200⟩, ⟨.privateRow 20 0, 10658528719017379200⟩, ⟨.privateRow 20 1, 1362658692338143200⟩, ⟨.privateRow 20 2, 13065875691127459200⟩, ⟨.privateRow 20 5, 54327050497165446000⟩, ⟨.privateRow 21 1, 560972028175951392000⟩, ⟨.privateRow 21 9, 4331820264064413120000⟩, ⟨.hall 16 2, 695724931181280⟩, ⟨.hall 18 5, 49368713281430400⟩, ⟨.hall 12 6, 2689789982880⟩, ⟨.hall 13 6, 6190961333700⟩, ⟨.hall 14 6, 12379404609000⟩, ⟨.hall 19 6, 325242606544455600⟩, ⟨.hall 15 8, 22103516635200⟩, ⟨.hall 11 9, 3115051307280⟩, ⟨.hall 17 12, 8981797474890240⟩, ⟨.hall 13 13, 11478988892800⟩, ⟨.hall 10 15, 9237554469000⟩, ⟨.hall 8 18, 32049916984800⟩, ⟨.hall 11 19, 3261058115000400⟩, ⟨.hall 6 20, 196287277843800⟩, ⟨.hall 7 22, 5297839157963352⟩, ⟨.hall 9 22, 500004086633251200⟩, ⟨.hall 7 24, 68263938141182784⟩, ⟨.hall 5 26, 11862850209546336000⟩, ⟨.hall 4 27, 55634437121452675200⟩, ⟨.hall 3 28, 77521990124894515200⟩]
  caps := #[0, 4440486887796960000, 156884367497457600, 60341017242105600, 10055751763200000, 3171998166480000, 0, 643593830880000, 263742576577480, 1262346825877280, 17697222972000, 1184755919832000, 44204797361120, 1687848239732160, 213188976000000, 317575305435960, 20025159625774875, 754122230759040, 203365261114810080, 35423899523812800, 55669898730045600, 0] }

theorem case_53_32_15_checked :
    (Witness.linear .positive case_53_32_15).check 53 32 15 = true := by
  change case_53_32_15.check 53 32 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_32_16 : Certificate := {
  objectiveScale := 38039601600000
  eta := 792637045669534665600
  rows := #[⟨.count 2, 157236469320112902720⟩, ⟨.count 3, 34203110645469205440⟩, ⟨.count 4, 7229262957246570240⟩, ⟨.count 5, 1654641123562627200⟩, ⟨.count 6, 365699668613479200⟩, ⟨.count 7, 90459043711676640⟩, ⟨.count 8, 22381619062682880⟩, ⟨.count 9, 5718380694586560⟩, ⟨.count 10, 1537199111448000⟩, ⟨.count 11, 461159733434400⟩, ⟨.count 12, 184463893373760⟩, ⟨.path 11, 4736040477168⟩, ⟨.path 12, 28065748906624⟩, ⟨.privateRow 2 30, 4131007404140897280⟩, ⟨.privateRow 3 28, 3071077872815272320⟩, ⟨.privateRow 4 25, 379355120720175600⟩, ⟨.privateRow 4 26, 1141462572196826880⟩, ⟨.privateRow 4 27, 2162890389777717600⟩, ⟨.privateRow 5 22, 12878312555908800⟩, ⟨.privateRow 5 23, 226480669086672000⟩, ⟨.privateRow 5 24, 424451418653021760⟩, ⟨.privateRow 5 25, 813198825944144640⟩, ⟨.privateRow 6 20, 24717795712295400⟩, ⟨.privateRow 6 21, 86595549944904000⟩, ⟨.privateRow 6 22, 165497418337010760⟩, ⟨.privateRow 6 23, 292759570775271600⟩, ⟨.privateRow 6 24, 398839119457779000⟩, ⟨.privateRow 7 18, 15845320340880030⟩, ⟨.privateRow 7 19, 34666767961459920⟩, ⟨.privateRow 7 20, 62160062069425320⟩, ⟨.privateRow 7 21, 110815659144878688⟩, ⟨.privateRow 7 22, 145913501657163240⟩, ⟨.privateRow 7 23, 163043877755238480⟩, ⟨.privateRow 8 15, 995848824366396⟩, ⟨.privateRow 8 16, 6742610769214320⟩, ⟨.privateRow 8 17, 14975201593837485⟩, ⟨.privateRow 8 18, 24594087783802680⟩, ⟨.privateRow 8 19, 42837042238770780⟩, ⟨.privateRow 8 20, 57359560044274488⟩, ⟨.privateRow 8 21, 62673529272624270⟩, ⟨.privateRow 8 22, 45373847772413160⟩, ⟨.privateRow 9 13, 838472242608000⟩, ⟨.privateRow 9 14, 2922727910566464⟩, ⟨.privateRow 9 15, 6378806979504960⟩, ⟨.privateRow 9 16, 10675847829006360⟩, ⟨.privateRow 9 17, 17808085706336640⟩, ⟨.privateRow 9 18, 24062290091199360⟩, ⟨.privateRow 9 19, 20614864883925312⟩, ⟨.privateRow 10 11, 495746713441980⟩, ⟨.privateRow 10 12, 1394658830204640⟩, ⟨.privateRow 10 13, 2860727546404728⟩, ⟨.privateRow 10 14, 4860965190201120⟩, ⟨.privateRow 10 15, 8341226678494710⟩, ⟨.privateRow 10 16, 8076883331293920⟩, ⟨.privateRow 11 8, 7985449929600⟩, ⟨.privateRow 11 9, 248316779541600⟩, ⟨.privateRow 11 10, 724346854030800⟩, ⟨.privateRow 11 11, 1434295699855200⟩, ⟨.privateRow 11 12, 2418992419924080⟩, ⟨.privateRow 11 13, 2759194768730400⟩, ⟨.privateRow 12 6, 8198395261056⟩, ⟨.privateRow 12 7, 125171927646480⟩, ⟨.privateRow 12 8, 392577003846720⟩, ⟨.privateRow 12 9, 818558526846060⟩, ⟨.privateRow 12 10, 672175247824080⟩, ⟨.privateRow 13 4, 5123997038160⟩, ⟨.privateRow 13 5, 68319960508800⟩, ⟨.privateRow 13 6, 228383867986560⟩, ⟨.privateRow 13 7, 179734049953920⟩, ⟨.privateRow 14 3, 41632475935050⟩, ⟨.privateRow 14 4, 57730366629936⟩, ⟨.privateRow 15 1, 19591753381200⟩, ⟨.privateRow 16 0, 9795876690600⟩, ⟨.hall 6 25, 248103936587707200⟩, ⟨.hall 5 26, 929705613710473600⟩, ⟨.hall 4 27, 2408460143830266240⟩, ⟨.hall 3 28, 2429122321128222720⟩, ⟨.hall 2 29, 4268707650945593856⟩, ⟨.assumptionRow 16, 53117403870960⟩]
  caps := #[0, 0, 35201748743132400, 0, 0, 0, 1076572973664760, 390872303048370, 68613127465168, 0, 54341300209482, 6609376272328, 111359366494420, 53117403870960, 223490342190258, 0, 0, 38039601600000, 0, 0, 0, 0] }

theorem case_53_32_16_checked :
    (Witness.linear .conditional case_53_32_16).check 53 32 16 = true := by
  change case_53_32_16.check 53 32 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_32_17 : Certificate := {
  objectiveScale := 12154471073791546500000
  eta := 202391679794868047853873504000
  rows := #[⟨.count 2, 42718243877651991128050771200⟩, ⟨.count 3, 8614382709804452380050451200⟩, ⟨.count 4, 1883431345154378477358700800⟩, ⟨.count 5, 407000812291184618803296000⟩, ⟨.count 6, 86683742982909502990560000⟩, ⟨.count 7, 20226206696012217364464000⟩, ⟨.count 8, 4870800796182533977564800⟩, ⟨.count 9, 1257390557554291691731200⟩, ⟨.count 10, 381027441683118694464000⟩, ⟨.count 11, 95256860420779673616000⟩, ⟨.count 12, 57154116252467804169600⟩, ⟨.path 10, 21465350011516739328000⟩, ⟨.path 11, 2567375285034364764960⟩, ⟨.privateRow 2 30, 4279824058903336189795348800⟩, ⟨.privateRow 3 27, 408404263368050772661238400⟩, ⟨.privateRow 3 28, 1332576797484413088116308800⟩, ⟨.privateRow 4 25, 244551350143927309746463200⟩, ⟨.privateRow 4 26, 487933157723799491277974400⟩, ⟨.privateRow 4 27, 915050102116732315378444800⟩, ⟨.privateRow 5 22, 15768185628319728639235200⟩, ⟨.privateRow 5 23, 89622734649758625187192320⟩, ⟨.privateRow 5 24, 176711001766588372525041600⟩, ⟨.privateRow 5 25, 339800272493005251722995200⟩, ⟨.privateRow 6 20, 10791241473382611596784000⟩, ⟨.privateRow 6 21, 32110823045454770254638000⟩, ⟨.privateRow 6 22, 63372007816434197364884400⟩, ⟨.privateRow 6 23, 121460435108195815499868000⟩, ⟨.privateRow 6 24, 176084952511711803892332000⟩, ⟨.privateRow 7 18, 5066871167215305472424400⟩, ⟨.privateRow 7 19, 12230073669833626476355200⟩, ⟨.privateRow 7 20, 23181021585786791295769200⟩, ⟨.privateRow 7 21, 44613233055204090872474880⟩, ⟨.privateRow 7 22, 65141800902335266384275000⟩, ⟨.privateRow 7 23, 80746594554794352111127200⟩, ⟨.privateRow 8 15, 122801969225788462569960⟩, ⟨.privateRow 8 16, 1922865568549460800465200⟩, ⟨.privateRow 8 17, 4887569972652442065940950⟩, ⟨.privateRow 8 18, 8977959094658484238308000⟩, ⟨.privateRow 8 19, 17097680337164749389467400⟩, ⟨.privateRow 8 20, 25443742464126389353991040⟩, ⟨.privateRow 8 21, 31724702007763040424848700⟩, ⟨.privateRow 8 22, 31622367033408216706040400⟩, ⟨.privateRow 8 23, 4829522823333529452331200⟩, ⟨.privateRow 9 13, 83133260003589533337600⟩, ⟨.privateRow 9 14, 730302596559310831056000⟩, ⟨.privateRow 9 15, 1955235260933188708073600⟩, ⟨.privateRow 9 16, 3727718471133177894172800⟩, ⟨.privateRow 9 17, 7035399548220441608496000⟩, ⟨.privateRow 9 18, 9062102654696839616668800⟩, ⟨.privateRow 9 19, 16785528897613655553454080⟩, ⟨.privateRow 9 20, 8976371480318137910414400⟩, ⟨.privateRow 10 11, 36118226242878959579400⟩, ⟨.privateRow 10 12, 290100438554192642376000⟩, ⟨.privateRow 10 13, 809207029274523327367920⟩, ⟨.privateRow 10 14, 1619895831933369894103200⟩, ⟨.privateRow 10 15, 3169672030501443639572400⟩, ⟨.privateRow 10 16, 4894161407190487087999200⟩, ⟨.privateRow 10 17, 5712236396566087761172800⟩, ⟨.privateRow 11 9, 11324242147924856304000⟩, ⟨.privateRow 11 10, 118710254084986790226000⟩, ⟨.privateRow 11 11, 355835544712333987392000⟩, ⟨.privateRow 11 12, 749498297219861886496800⟩, ⟨.privateRow 11 13, 1541910291154539666360000⟩, ⟨.privateRow 11 14, 2529177890603996675043000⟩, ⟨.privateRow 11 15, 116906146880047781256000⟩, ⟨.privateRow 12 7, 1701015364656779886000⟩, ⟨.privateRow 12 8, 48727547830629602272800⟩, ⟨.privateRow 12 9, 166302602151277846854600⟩, ⟨.privateRow 12 10, 376697584391265072936000⟩, ⟨.privateRow 12 11, 819208999618705193097600⟩, ⟨.privateRow 12 12, 271482052199222069805600⟩, ⟨.privateRow 13 6, 17690559792430510814400⟩, ⟨.privateRow 13 7, 81578952257795925609600⟩, ⟨.privateRow 13 8, 205860659464907183536800⟩, ⟨.privateRow 13 9, 173194291674144861120000⟩, ⟨.privateRow 14 4, 5503729713200603364480⟩, ⟨.privateRow 14 5, 38329546216932773431200⟩, ⟨.privateRow 14 6, 76205488336623738892800⟩, ⟨.privateRow 15 2, 1289936651531391413550⟩, ⟨.privateRow 15 3, 17887121567901960934560⟩, ⟨.privateRow 15 4, 7371066580179379506000⟩, ⟨.privateRow 16 1, 3224841628828478533875⟩, ⟨.hall 7 24, 17013129289445705120280576⟩, ⟨.hall 6 25, 153613594536059821165002000⟩, ⟨.hall 5 26, 460295261680677128049344000⟩, ⟨.hall 4 27, 1084566942901065613505630400⟩, ⟨.hall 3 28, 1081480041887170353911683200⟩, ⟨.hall 2 29, 1959919428843583862616561600⟩, ⟨.assumptionRow 17, 13420657573144201860480⟩]
  caps := #[0, 62742523726031339000210400, 136475183472998015235189600, 3735978579931015971352800, 0, 1033502370190042299655680, 0, 186073243105561218401280, 113877417510028492320, 3117688860069243139680, 0, 62487994035371204507760, 50622482739533653408680, 28107501645641059081440, 144453072963797166940800, 10840784270081419033380, 285568295529494481428925, 156741937459937449139520, 12154471073791546500000, 0, 0, 0] }

theorem case_53_32_17_checked :
    (Witness.linear .conditional case_53_32_17).check 53 32 17 = true := by
  change case_53_32_17.check 53 32 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_32_18 : Certificate := {
  objectiveScale := 140752071807690184842000000
  eta := 2619002280575510782064007817521600
  rows := #[⟨.count 2, 507021332869075207112670037096800⟩, ⟨.count 3, 92611545238940507349925038203520⟩, ⟨.count 4, 18199781278299253931950442831040⟩, ⟨.count 5, 3508355289024345301683174633600⟩, ⟨.count 6, 686049089511466664411758129800⟩, ⟨.count 7, 146244209204501947393123749480⟩, ⟨.count 8, 36890431150685175918986171040⟩, ⟨.count 9, 11466727422034010725210772160⟩, ⟨.count 10, 3909111621147958201776399600⟩, ⟨.count 11, 1737382942732425867456177600⟩, ⟨.count 12, 1042429765639455520473706560⟩, ⟨.path 8, 551221330548628641156615360⟩, ⟨.path 9, 536488036846679358412171200⟩, ⟨.privateRow 2 30, 52161187482214211954756701658160⟩, ⟨.privateRow 3 27, 4825117821321250866628211636640⟩, ⟨.privateRow 3 28, 15742426844098510785020425233600⟩, ⟨.privateRow 4 25, 2703729813671390571817532382600⟩, ⟨.privateRow 4 26, 5629304124874792677732913576080⟩, ⟨.privateRow 4 27, 11141286640477848486471772492560⟩, ⟨.privateRow 5 22, 150322233056193335887569499680⟩, ⟨.privateRow 5 23, 928735425867045571707374297856⟩, ⟨.privateRow 5 24, 1976273097358134424231402020000⟩, ⟨.privateRow 5 25, 4092077349272601894795840169920⟩, ⟨.privateRow 6 20, 89402830594772747762849139000⟩, ⟨.privateRow 6 21, 314792071936331411859716178900⟩, ⟨.privateRow 6 22, 683508166957720491580603470060⟩, ⟨.privateRow 6 23, 1437856313631456968296453981575⟩, ⟨.privateRow 6 24, 2297966440428097416620180237700⟩, ⟨.privateRow 7 18, 35972875784054613507735877245⟩, ⟨.privateRow 7 19, 111773704295479793218094397240⟩, ⟨.privateRow 7 20, 240854362563742160464265154120⟩, ⟨.privateRow 7 21, 517331831942720788423088723064⟩, ⟨.privateRow 7 22, 846880076339326270650399370380⟩, ⟨.privateRow 7 23, 1181372140420751466929438096400⟩, ⟨.privateRow 8 16, 12045855069611486014362831360⟩, ⟨.privateRow 8 17, 40631233799255930364852753435⟩, ⟨.privateRow 8 18, 88757516930329275297793987320⟩, ⟨.privateRow 8 19, 193204222327440474902241349860⟩, ⟨.privateRow 8 20, 326837927005942897874079010260⟩, ⟨.privateRow 8 21, 465271152063743647304764361280⟩, ⟨.privateRow 8 22, 548274622152785293122483246120⟩, ⟨.privateRow 8 23, 218942826714461892284493180930⟩, ⟨.privateRow 9 14, 3526887373746824510936040528⟩, ⟨.privateRow 9 15, 14684103241908873442722212160⟩, ⟨.privateRow 9 16, 34233683067423508030001099460⟩, ⟨.privateRow 9 17, 76304204194386494169277742880⟩, ⟨.privateRow 9 18, 133469618511688804973244576960⟩, ⟨.privateRow 9 19, 196660166564359058690256263136⟩, ⟨.privateRow 9 20, 241148752451260710402917450880⟩, ⟨.privateRow 9 21, 178853921826843618466460949600⟩, ⟨.privateRow 10 12, 880537264157570382824380920⟩, ⟨.privateRow 10 13, 5168714254628966955682128360⟩, ⟨.privateRow 10 14, 13599847590611044706920856880⟩, ⟨.privateRow 10 15, 32087291223589490239581280050⟩, ⟨.privateRow 10 16, 58630469378138185791405079080⟩, ⟨.privateRow 10 17, 90199131110191776285433220400⟩, ⟨.privateRow 10 18, 116969306619460571526487156920⟩, ⟨.privateRow 10 19, 6536903322030752326303868220⟩, ⟨.privateRow 11 10, 151362907889567405119288200⟩, ⟨.privateRow 11 11, 1730203674374027413458424800⟩, ⟨.privateRow 11 12, 5449064684024426584294375200⟩, ⟨.privateRow 11 13, 14236888002946267524988122000⟩, ⟨.privateRow 11 14, 27956070987603579867249403200⟩, ⟨.privateRow 11 15, 45516048587363455599038626800⟩, ⟨.privateRow 11 16, 24033797374465224499810456800⟩, ⟨.privateRow 12 9, 503117143832931657450851430⟩, ⟨.privateRow 12 10, 2148037092832817436127637760⟩, ⟨.privateRow 12 11, 6536903322030752326303868220⟩, ⟨.privateRow 12 12, 14376843851110824053199869640⟩, ⟨.privateRow 12 13, 17835321771487559295604823175⟩, ⟨.privateRow 13 7, 89096561165765429100316800⟩, ⟨.privateRow 13 8, 776996260499779346279012760⟩, ⟨.privateRow 13 9, 3027258157791348102385764000⟩, ⟨.privateRow 13 10, 7818223242295916403552799200⟩, ⟨.privateRow 13 11, 1872512727167170101591658080⟩, ⟨.privateRow 14 5, 6722017337952838177657830⟩, ⟨.privateRow 14 6, 209933772246834792317621460⟩, ⟨.privateRow 14 7, 1325357751799701260694868815⟩, ⟨.privateRow 14 8, 2592254322508721777238592260⟩, ⟨.privateRow 15 4, 40332104027717029065946980⟩, ⟨.privateRow 15 5, 463302118061980231321647360⟩, ⟨.privateRow 15 6, 627388284875598229914730800⟩, ⟨.privateRow 16 3, 134440346759056763553156600⟩, ⟨.privateRow 16 4, 108586433920776616716011100⟩, ⟨.hall 7 24, 517256545348535716635498955368⟩, ⟨.hall 6 25, 2741047351462164135762268197300⟩, ⟨.hall 5 26, 6847176321513417837238279788800⟩, ⟨.hall 4 27, 14559459344896218511163489678880⟩, ⟨.hall 3 28, 14029163569391742664262104775040⟩, ⟨.hall 2 29, 24341887491699965578886460773808⟩, ⟨.assumptionRow 18, 118450469038048905814524468⟩]
  caps := #[0, 625614508104105477312483628500, 64981562742443259533536936020, 0, 0, 3123041989166065377188537760, 2353278141370459466026919055, 0, 81472461305270715925833588, 545772464212603962254132784, 147855132142038287387193630, 0, 0, 333049804344505438416097872, 625966178038599386977610193, 118450469038048905814524468, 556848596073844516969583628, 11009379896159431954376657448, 1711326464461923497131475532, 140752071807690184842000000, 0, 0] }

theorem case_53_32_18_checked :
    (Witness.linear .conditional case_53_32_18).check 53 32 18 = true := by
  change case_53_32_18.check 53 32 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_32_19 : Certificate := {
  objectiveScale := 177382530416520000000
  eta := 3511824208347058238194560000
  rows := #[⟨.count 2, 685838610100719608870937600⟩, ⟨.count 3, 126066878315121177312278400⟩, ⟨.count 4, 24173237842801732145260800⟩, ⟨.count 5, 4450271981378306363280000⟩, ⟨.count 6, 771469304556299216868000⟩, ⟨.count 7, 147365293754622959215200⟩, ⟨.count 8, 12258234200203718126400⟩, ⟨.count 9, 5165677288380162153600⟩, ⟨.count 10, 1537403954875048260000⟩, ⟨.count 11, 614961581950019304000⟩, ⟨.count 12, 368976949170011582400⟩, ⟨.count 13, 532966704356683396800⟩, ⟨.path 9, 1065052429033511318400⟩, ⟨.privateRow 2 30, 73593374954331735138636000⟩, ⟨.privateRow 3 27, 6224518140181705391227200⟩, ⟨.privateRow 3 28, 21812994792558159722532000⟩, ⟨.privateRow 4 25, 3466748549326091739910200⟩, ⟨.privateRow 4 26, 7675697648360894833480800⟩, ⟨.privateRow 4 27, 15785541091312338017271600⟩, ⟨.privateRow 5 22, 178543845959488937928000⟩, ⟨.privateRow 5 23, 1188089377351918628146560⟩, ⟨.privateRow 5 24, 2629924202648054221509600⟩, ⟨.privateRow 5 25, 5731523938651773249187200⟩, ⟨.privateRow 6 20, 109448519644676054700000⟩, ⟨.privateRow 6 21, 389953972020973351992000⟩, ⟨.privateRow 6 22, 887855908620189953644200⟩, ⟨.privateRow 6 23, 1972976118690397349529000⟩, ⟨.privateRow 6 24, 3363908182331266706136000⟩, ⟨.privateRow 7 18, 44086339576004404729050⟩, ⟨.privateRow 7 19, 133355883240104424213600⟩, ⟨.privateRow 7 20, 301947844964076006095400⟩, ⟨.privateRow 7 21, 692483638970638737462240⟩, ⟨.privateRow 7 22, 1219794234177336831713700⟩, ⟨.privateRow 7 23, 1843043277557440909750800⟩, ⟨.privateRow 8 0, 85274672697069343488⟩, ⟨.privateRow 8 16, 14382698702292164444200⟩, ⟨.privateRow 8 17, 46576293397920784973475⟩, ⟨.privateRow 8 18, 106574306346181083524400⟩, ⟨.privateRow 8 19, 249961384343284513099200⟩, ⟨.privateRow 8 20, 460043535033080191032840⟩, ⟨.privateRow 8 21, 716357216283915924367650⟩, ⟨.privateRow 8 22, 938909677508357250696000⟩, ⟨.privateRow 8 23, 508516856794320545971800⟩, ⟨.privateRow 9 14, 4087444648027794973920⟩, ⟨.privateRow 9 15, 15993556401677909454400⟩, ⟨.privateRow 9 16, 39126930651569978217000⟩, ⟨.privateRow 9 17, 94528380311174395872000⟩, ⟨.privateRow 9 18, 181707481653298481680800⟩, ⟨.privateRow 9 19, 295443942944307940823040⟩, ⟨.privateRow 9 20, 404972700433486045660800⟩, ⟨.privateRow 9 21, 437251350579395947795200⟩, ⟨.privateRow 9 22, 175223053416958833686400⟩, ⟨.privateRow 10 12, 939214052432756755200⟩, ⟨.privateRow 10 13, 5260996333582415145720⟩, ⟨.privateRow 10 14, 14636085650410459435200⟩, ⟨.privateRow 10 15, 37731736562520871921050⟩, ⟨.privateRow 10 16, 76277199075443465814000⟩, ⟨.privateRow 10 17, 130361606013704925459600⟩, ⟨.privateRow 10 18, 189069938370533435014800⟩, ⟨.privateRow 10 19, 187040565150098371311600⟩, ⟨.privateRow 11 10, 135105196034473938000⟩, ⟨.privateRow 11 11, 1565356754054594592000⟩, ⟨.privateRow 11 12, 5431228880585852307600⟩, ⟨.privateRow 11 13, 15706367272329533436000⟩, ⟨.privateRow 11 14, 34360978391457328611000⟩, ⟨.privateRow 11 15, 62322762399311371932000⟩, ⟨.privateRow 11 16, 96423180769845072234000⟩, ⟨.privateRow 11 17, 34901865055581550135200⟩, ⟨.privateRow 12 9, 348478229771677605600⟩, ⟨.privateRow 12 10, 1889609224537332043200⟩, ⟨.privateRow 12 11, 6656959124608958965800⟩, ⟨.privateRow 12 12, 16477553943027461684400⟩, ⟨.privateRow 12 13, 32562215764253522146800⟩, ⟨.privateRow 12 14, 37033864981575805371600⟩, ⟨.privateRow 13 7, 18921894829231363200⟩, ⟨.privateRow 13 8, 526133797890572071200⟩, ⟨.privateRow 13 9, 2724466160033115825600⟩, ⟨.privateRow 13 10, 8224086222611591492160⟩, ⟨.privateRow 13 11, 18457958000455394220800⟩, ⟨.privateRow 13 12, 4525092307182225378600⟩, ⟨.privateRow 14 0, 3506359897083443400⟩, ⟨.privateRow 14 6, 40997438796667953600⟩, ⟨.privateRow 14 7, 932691732624195944400⟩, ⟨.privateRow 14 8, 4057814680897475862000⟩, ⟨.privateRow 14 9, 6875270486201215818720⟩, ⟨.privateRow 15 5, 112742956690836872400⟩, ⟨.privateRow 15 6, 1721038316151790135500⟩, ⟨.privateRow 15 7, 1986512261693092660800⟩, ⟨.privateRow 16 4, 307480790975009652000⟩, ⟨.privateRow 16 5, 805001793038740547250⟩, ⟨.privateRow 17 3, 245984632780007721600⟩, ⟨.hall 8 23, 31822553639296971150600⟩, ⟨.hall 7 24, 1122886230740921981382048⟩, ⟨.hall 6 25, 4848357112093952192736000⟩, ⟨.hall 5 26, 10972007887022922195456000⟩, ⟨.hall 4 27, 21966374996261950965796800⟩, ⟨.hall 3 28, 20762765523461095893158400⟩, ⟨.hall 2 29, 34963308662514094518495840⟩, ⟨.assumptionRow 19, 88064535499866125200⟩]
  caps := #[0, 0, 458988276248359735878000, 0, 1804664469516750172760, 0, 905156914095022231500, 2152122795721329456740, 0, 0, 80301997551926990580, 160472988250556358000, 78610254669904986600, 291711832997334570720, 0, 1644409113280191239800, 88064535499866125200, 3731227730892465804000, 12513615880573780372400, 2040525829498373874800, 177382530416520000000, 0] }

theorem case_53_32_19_checked :
    (Witness.linear .conditional case_53_32_19).check 53 32 19 = true := by
  change case_53_32_19.check 53 32 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_32_20 : Certificate := {
  objectiveScale := 24041810915192070000000
  eta := 536377949812091012197716144000
  rows := #[⟨.count 2, 115915234791606245589036643200⟩, ⟨.count 3, 24289527787322524819409116800⟩, ⟨.count 4, 4884009747494215425639552000⟩, ⟨.count 5, 1040204915794914035886720000⟩, ⟨.count 6, 212684755104495816266124000⟩, ⟨.count 7, 41174777916882013920516000⟩, ⟨.count 8, 7430035112820814542048000⟩, ⟨.count 9, 1200236441301823887561600⟩, ⟨.count 10, 142885290631169510424000⟩, ⟨.path 10, 53666850635982832248000⟩, ⟨.path 11, 11969231592002315510880⟩, ⟨.privateRow 2 30, 14039422847430570117926798400⟩, ⟨.privateRow 5 23, 169404800572314571558694400⟩, ⟨.privateRow 6 23, 776554763588412944871235500⟩, ⟨.privateRow 6 24, 180694326146517309210084000⟩, ⟨.privateRow 7 18, 3467349719316380119622400⟩, ⟨.privateRow 7 19, 14824689106056768062467200⟩, ⟨.privateRow 7 20, 35891197392209434690615200⟩, ⟨.privateRow 7 22, 502123320848412484421300100⟩, ⟨.privateRow 7 23, 243736110180159470373099600⟩, ⟨.privateRow 8 16, 1719915535375188551400000⟩, ⟨.privateRow 8 17, 6261352506533373921371700⟩, ⟨.privateRow 8 18, 15737964255340993183260600⟩, ⟨.privateRow 8 19, 37952516161356598169468100⟩, ⟨.privateRow 8 20, 43044670086941918913598080⟩, ⟨.privateRow 8 21, 215246569294437159613434300⟩, ⟨.privateRow 8 22, 223468625511298248483402000⟩, ⟨.privateRow 8 23, 146402650202206799872270800⟩, ⟨.privateRow 9 14, 627742710172938049129440⟩, ⟨.privateRow 9 15, 2304157612622637216244800⟩, ⟨.privateRow 9 16, 5901162503067300780511200⟩, ⟨.privateRow 9 18, 60950102140235874163197600⟩, ⟨.privateRow 9 19, 26336616769137164161351680⟩, ⟨.privateRow 9 21, 336548838323975972196902400⟩, ⟨.privateRow 10 11, 4762843021038983680800⟩, ⟨.privateRow 10 12, 191596185164522752614000⟩, ⟨.privateRow 10 14, 3830119596085516043310000⟩, ⟨.privateRow 10 15, 5125116768326761377020850⟩, ⟨.privateRow 10 16, 4009973620641892903256400⟩, ⟨.privateRow 10 17, 37350214970987710024833600⟩, ⟨.privateRow 10 18, 30871795893770484422209440⟩, ⟨.privateRow 10 19, 13895594513881234888734000⟩, ⟨.privateRow 10 20, 88991340426602890583907600⟩, ⟨.privateRow 10 22, 90517831614845884853604000⟩, ⟨.privateRow 11 9, 2497994591454012420000⟩, ⟨.privateRow 11 10, 54664448309651971791000⟩, ⟨.privateRow 11 11, 198386188644929568192000⟩, ⟨.privateRow 11 12, 240307079697875994804000⟩, ⟨.privateRow 11 13, 3734501914223748567900000⟩, ⟨.privateRow 11 14, 4977441573066478797781500⟩, ⟨.privateRow 11 15, 5205107015849746451160000⟩, ⟨.privateRow 11 16, 24227716476566939259924000⟩, ⟨.privateRow 11 17, 27344347755243176035778400⟩, ⟨.privateRow 11 18, 16279180953046653539898000⟩, ⟨.privateRow 12 7, 510304609397033965800⟩, ⟨.privateRow 12 8, 14838087873236833774800⟩, ⟨.privateRow 12 9, 80372975980032849613500⟩, ⟨.privateRow 12 10, 241606036885432081262400⟩, ⟨.privateRow 12 11, 412224063470924037573240⟩, ⟨.privateRow 12 12, 3726924663963004730226000⟩, ⟨.privateRow 12 13, 4975980246230478200515800⟩, ⟨.privateRow 12 14, 5428620434765647328180400⟩, ⟨.privateRow 12 15, 16565168027173585241822400⟩, ⟨.privateRow 13 6, 4082436875176271726400⟩, ⟨.privateRow 13 7, 26378822885754371155200⟩, ⟨.privateRow 13 8, 105576353633030804924400⟩, ⟨.privateRow 13 9, 348986497723401895156800⟩, ⟨.privateRow 13 10, 588687397400418382946880⟩, ⟨.privateRow 13 11, 4024073147997825767644800⟩, ⟨.privateRow 13 12, 5645159690686455407668200⟩, ⟨.privateRow 13 13, 6357715026941180501913600⟩, ⟨.privateRow 13 14, 8334975286818221441400000⟩, ⟨.privateRow 14 4, 1031949321225113130840⟩, ⟨.privateRow 14 5, 7739619909188348481300⟩, ⟨.privateRow 14 6, 39293454923571615366600⟩, ⟨.privateRow 14 7, 172851511305206449415700⟩, ⟨.privateRow 14 8, 522072542965250415738600⟩, ⟨.privateRow 14 9, 863741581865419690513080⟩, ⟨.privateRow 14 10, 4800284259232151246957400⟩, ⟨.privateRow 14 11, 7281047429568938833782975⟩, ⟨.privateRow 14 12, 8385325341612062126025600⟩, ⟨.privateRow 15 3, 4127797284900452523360⟩, ⟨.privateRow 15 4, 13267919844322883110800⟩, ⟨.privateRow 15 5, 76205488336623738892800⟩, ⟨.privateRow 15 6, 309584796367533939252000⟩, ⟨.privateRow 15 7, 875280651548209591885200⟩, ⟨.privateRow 15 9, 9452655782422036278494400⟩, ⟨.privateRow 15 10, 9631956976984899684977850⟩, ⟨.privateRow 15 12, 17058122279851120052785200⟩, ⟨.privateRow 16 2, 5159746606125565654200⟩, ⟨.privateRow 16 3, 33169799610807207777000⟩, ⟨.privateRow 16 4, 148838844407468240025000⟩, ⟨.privateRow 16 5, 554672760158498307826500⟩, ⟨.privateRow 16 6, 1498671855142834751379000⟩, ⟨.privateRow 16 9, 43216102667930440832458875⟩, ⟨.privateRow 16 11, 11028958370593396585852500⟩, ⟨.privateRow 17 1, 16511189139601810093440⟩, ⟨.privateRow 17 2, 88452798962152554072000⟩, ⟨.privateRow 17 3, 400078813767274629187200⟩, ⟨.privateRow 17 4, 1465368036139660645792800⟩, ⟨.privateRow 17 5, 3940170135586795590480000⟩, ⟨.privateRow 17 6, 1931809129333411780932480⟩, ⟨.privateRow 17 7, 1430969725432156874764800⟩, ⟨.privateRow 17 8, 71637921879447353542912800⟩, ⟨.privateRow 18 0, 140345107686615385794240⟩, ⟨.privateRow 18 1, 300739516471318683844800⟩, ⟨.privateRow 18 2, 1376461633080266283751200⟩, ⟨.privateRow 18 3, 4736647384423269270555600⟩, ⟨.privateRow 18 4, 12343990153345489614175200⟩, ⟨.privateRow 18 5, 9789071261141423159148240⟩, ⟨.privateRow 18 6, 6081621333086666717750400⟩, ⟨.privateRow 18 7, 145783480609471731993766800⟩, ⟨.privateRow 18 8, 129317992082667034053264000⟩, ⟨.privateRow 19 0, 2706655648241868154603200⟩, ⟨.privateRow 19 1, 5343909869605739689857600⟩, ⟨.privateRow 19 2, 20525471999167500172407600⟩, ⟨.privateRow 19 3, 52820795074780699744377600⟩, ⟨.privateRow 19 4, 56839768613079231246667200⟩, ⟨.privateRow 19 5, 41401806767551538809300800⟩, ⟨.privateRow 19 6, 404983351368189522632503800⟩, ⟨.privateRow 19 8, 1317840561177318472607913600⟩, ⟨.privateRow 20 0, 78458313085575178173818400⟩, ⟨.privateRow 20 1, 119995067072056154854075200⟩, ⟨.privateRow 20 2, 354530879985620457523404000⟩, ⟨.privateRow 20 3, 467980761581019003930893280⟩, ⟨.privateRow 20 4, 413316342137082311164036800⟩, ⟨.privateRow 20 5, 1807425697772845832489507700⟩, ⟨.privateRow 20 6, 2005631835347224302560971200⟩, ⟨.privateRow 20 9, 6914715740027235923466083400⟩, ⟨.privateRow 21 0, 3999835569068538495135840000⟩, ⟨.privateRow 21 5, 110395461706291662465749184000⟩, ⟨.hall 15 5, 22913677559200152582000⟩, ⟨.hall 19 7, 20838304188503924327805600⟩, ⟨.hall 20 7, 880266843041220024876486000⟩, ⟨.hall 11 10, 187946196340203150300⟩, ⟨.hall 17 14, 24700738952844307899786240⟩, ⟨.hall 13 15, 6821089166611815895800⟩, ⟨.hall 15 16, 2212620750509139624654000⟩, ⟨.hall 7 22, 395321838016623881935572⟩, ⟨.hall 6 23, 1188329333749226428359600⟩, ⟨.hall 5 26, 3034527241787429336700752000⟩, ⟨.hall 4 27, 7819678537528992757990567200⟩, ⟨.hall 3 28, 11935044747399211453035820800⟩, ⟨.hall 2 29, 13691437152921607268849980320⟩]
  caps := #[0, 82384142377207218827479200, 27556991045285940398160000, 7625838848291979634519200, 810345662382716805945600, 0, 547590586018387529552220, 84263134028075568165600, 0, 67330093062682435402560, 19621476452521592510400, 11969231592002315510880, 63455894612280384930540, 90720819448361593920, 22766163113281274406720, 249371929879865811558540, 5159746606125565654200, 11249053772236214665336320, 0, 167285438568361821030008400, 596469886989038408304721620, 0] }

theorem case_53_32_20_checked :
    (Witness.linear .conditional case_53_32_20).check 53 32 20 = true := by
  change case_53_32_20.check 53 32 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_33_1_checked :
    (Witness.rising).check 53 33 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_33_2_checked :
    (Witness.rising).check 53 33 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_33_3_checked :
    (Witness.rising).check 53 33 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_33_4_checked :
    (Witness.rising).check 53 33 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_33_5_checked :
    (Witness.rising).check 53 33 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_33_6_checked :
    (Witness.rising).check 53 33 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_33_7_checked :
    (Witness.rising).check 53 33 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_33_8_checked :
    (Witness.rising).check 53 33 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_33_9_checked :
    (Witness.rising).check 53 33 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_33_10_checked :
    (Witness.rising).check 53 33 10 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_33_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_33_11_checked :
    (Witness.linear .positive case_53_33_11).check 53 33 11 = true := by
  change case_53_33_11.check 53 33 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_33_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_33_12_checked :
    (Witness.linear .positive case_53_33_12).check 53 33 12 = true := by
  change case_53_33_12.check 53 33 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_33_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_33_13_checked :
    (Witness.linear .positive case_53_33_13).check 53 33 13 = true := by
  change case_53_33_13.check 53 33 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_33_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_33_14_checked :
    (Witness.linear .positive case_53_33_14).check 53 33 14 = true := by
  change case_53_33_14.check 53 33 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_33_15 : Certificate := {
  objectiveScale := 571218366610892000000
  eta := 27883741641059643503917072320
  rows := #[⟨.count 2, 5534155612243354194677779200⟩, ⟨.count 3, 1061920435543031053586076480⟩, ⟨.count 4, 207594750098934567573684480⟩, ⟨.count 5, 41437991476029118835264400⟩, ⟨.count 6, 8024838109325262088063200⟩, ⟨.count 7, 1675983888319258276799040⟩, ⟨.count 8, 336507847198390840452480⟩, ⟨.count 9, 72108824399655180096960⟩, ⟨.count 10, 14898517437945285144000⟩, ⟨.count 11, 3277673836347962731680⟩, ⟨.path 10, 1306984427341530537600⟩, ⟨.path 11, 793455875225863641792⟩, ⟨.privateRow 2 31, 573697806923656612851413760⟩, ⟨.privateRow 5 24, 17107818588818191478003760⟩, ⟨.privateRow 5 27, 135158158315644591203556480⟩, ⟨.privateRow 6 20, 356856738932384442411660⟩, ⟨.privateRow 6 21, 1489312559353917161223360⟩, ⟨.privateRow 6 22, 4028989516835279077841760⟩, ⟨.privateRow 6 23, 8583025963655320141268304⟩, ⟨.privateRow 6 25, 31599871363239800475975120⟩, ⟨.privateRow 6 27, 145900552221284130836485920⟩, ⟨.privateRow 7 18, 313711538955642708120240⟩, ⟨.privateRow 7 20, 2973407597090790626669760⟩, ⟨.privateRow 7 21, 1906110408900625358591160⟩, ⟨.privateRow 7 22, 1464964125141046580930880⟩, ⟨.privateRow 7 23, 11876963305419828478502640⟩, ⟨.privateRow 7 24, 8495574504107426640384480⟩, ⟨.privateRow 8 15, 24483230323023418586640⟩, ⟨.privateRow 8 16, 152466461287452733068648⟩, ⟨.privateRow 8 17, 223428099844386126209520⟩, ⟨.privateRow 8 18, 490626802378335671398350⟩, ⟨.privateRow 8 20, 4691990096732108650399920⟩, ⟨.privateRow 8 22, 5242366161752204059094520⟩, ⟨.privateRow 9 12, 616314738458591282880⟩, ⟨.privateRow 9 13, 21395926431715867831800⟩, ⟨.privateRow 9 14, 70486541389745582381280⟩, ⟨.privateRow 9 15, 134675976075719624241696⟩, ⟨.privateRow 9 16, 210823218362628220148800⟩, ⟨.privateRow 9 17, 365415109505070789544380⟩, ⟨.privateRow 9 18, 180011928154983350025600⟩, ⟨.privateRow 9 19, 2606903955505715765980080⟩, ⟨.privateRow 9 20, 758672237320008440292864⟩, ⟨.privateRow 9 24, 17978405178350392023568320⟩, ⟨.privateRow 10 10, 1617553321834059529920⟩, ⟨.privateRow 10 11, 12560596239990794244480⟩, ⟨.privateRow 10 12, 35508133227102929593200⟩, ⟨.privateRow 10 13, 70700237296431262228800⟩, ⟨.privateRow 10 14, 114599396132675133327648⟩, ⟨.privateRow 10 15, 166168131157883080306080⟩, ⟨.privateRow 10 16, 309218729424554393163720⟩, ⟨.privateRow 10 18, 1828445383434231694772640⟩, ⟨.privateRow 10 21, 580446239382348309210240⟩, ⟨.privateRow 11 8, 1529581123629049274784⟩, ⟨.privateRow 11 9, 7257706351913346048720⟩, ⟨.privateRow 11 10, 19666043018087776390080⟩, ⟨.privateRow 11 11, 39729379834520760384000⟩, ⟨.privateRow 11 12, 67232945965418541322560⟩, ⟨.privateRow 11 14, 362696130072645775005600⟩, ⟨.privateRow 11 17, 1733442503904933926504400⟩, ⟨.privateRow 11 20, 1261209162846861538390080⟩, ⟨.privateRow 12 6, 1160842817039903467470⟩, ⟨.privateRow 12 7, 4661580567250435885056⟩, ⟨.privateRow 12 8, 12278270244097130232960⟩, ⟨.privateRow 12 9, 25352947195682959591200⟩, ⟨.privateRow 12 10, 44369992117969643645520⟩, ⟨.privateRow 12 11, 69129120912066123068160⟩, ⟨.privateRow 12 12, 2039441498172065699712⟩, ⟨.privateRow 12 13, 364631098016438175002080⟩, ⟨.privateRow 12 14, 41653771670255359715100⟩, ⟨.privateRow 12 16, 1153255609085394294480000⟩, ⟨.privateRow 12 19, 2479256768879053439596320⟩, ⟨.privateRow 13 4, 867619544915637193680⟩, ⟨.privateRow 13 5, 3414243579529127845500⟩, ⟨.privateRow 13 6, 8958975152684431466592⟩, ⟨.privateRow 13 7, 18963684338870355804720⟩, ⟨.privateRow 13 8, 34499618200534325675760⟩, ⟨.privateRow 13 9, 56039117952004751704140⟩, ⟨.privateRow 13 11, 195349360646338578808128⟩, ⟨.privateRow 13 13, 620846052501576607425720⟩, ⟨.privateRow 13 15, 725276382787440864460080⟩, ⟨.privateRow 13 17, 499981829786245481695020⟩, ⟨.privateRow 13 18, 382213187916354098544240⟩, ⟨.privateRow 13 20, 8846441684303151412804320⟩, ⟨.privateRow 14 2, 732707511035457277320⟩, ⟨.privateRow 14 3, 2924199206937888319440⟩, ⟨.privateRow 14 4, 7799107833810107749935⟩, ⟨.privateRow 14 5, 17043903949009406204736⟩, ⟨.privateRow 14 6, 32102251060421628183240⟩, ⟨.privateRow 14 7, 54315737859480525267840⟩, ⟨.privateRow 14 8, 80654188330133797218840⟩, ⟨.privateRow 14 9, 30988916270926193099520⟩, ⟨.privateRow 14 10, 263673252163544325750648⟩, ⟨.privateRow 14 11, 55911219303628739930880⟩, ⟨.privateRow 14 13, 1728159104489695234568640⟩, ⟨.privateRow 14 16, 1355142541660078234403340⟩, ⟨.privateRow 15 2, 16013471847517007463600⟩, ⟨.privateRow 15 3, 14499154401067029583890⟩, ⟨.privateRow 15 4, 36612830705279465180544⟩, ⟨.privateRow 15 5, 63576467111384292985920⟩, ⟨.privateRow 15 6, 114172305299454035153520⟩, ⟨.privateRow 15 7, 150909566215187450771100⟩, ⟨.privateRow 15 8, 46052972791515314745120⟩, ⟨.privateRow 15 10, 676232670569493570252720⟩, ⟨.privateRow 15 12, 1532936837318643617580720⟩, ⟨.privateRow 15 13, 1142572820285445378910080⟩, ⟨.privateRow 16 0, 9863370340861924887000⟩, ⟨.privateRow 16 1, 40938788897130436472160⟩, ⟨.privateRow 16 2, 42165908207184728891925⟩, ⟨.privateRow 16 3, 95161797048635851309776⟩, ⟨.privateRow 16 4, 178047925181616118388760⟩, ⟨.privateRow 16 5, 298814598080389269038160⟩, ⟨.privateRow 16 6, 395323883261745949470960⟩, ⟨.privateRow 16 7, 193035124270977744515760⟩, ⟨.privateRow 16 8, 100132935700430261452824⟩, ⟨.privateRow 16 9, 1362723246293483542387920⟩, ⟨.privateRow 16 10, 938302420526194914500310⟩, ⟨.privateRow 16 11, 2582963062748687392693920⟩, ⟨.privateRow 16 14, 6270736327906377366159120⟩, ⟨.privateRow 16 17, 37404267541430226033476880⟩, ⟨.privateRow 17 0, 265684385087499567309120⟩, ⟨.privateRow 17 1, 83444113083691884544020⟩, ⟨.privateRow 17 4, 3330116617729530135386880⟩, ⟨.privateRow 17 7, 2099240836386325197549984⟩, ⟨.privateRow 17 8, 2364052603297786156916160⟩, ⟨.privateRow 17 9, 3909445468304032548211320⟩, ⟨.privateRow 17 10, 6111456987430515653412480⟩, ⟨.privateRow 17 12, 9533223608812594537182336⟩, ⟨.privateRow 18 0, 2334067957461565905259680⟩, ⟨.privateRow 18 3, 13744378953752457054844800⟩, ⟨.privateRow 18 7, 35824813170846869794905280⟩, ⟨.privateRow 18 11, 106369110778662258634179072⟩, ⟨.privateRow 19 3, 196786074344604435805514400⟩, ⟨.privateRow 19 14, 6359932758572859925297238400⟩, ⟨.privateRow 20 8, 7473283174282026862106105760⟩, ⟨.hall 17 3, 69274677062590810734924⟩, ⟨.hall 14 6, 692573496380026180920⟩, ⟨.hall 11 8, 1627487781892276304⟩, ⟨.hall 16 9, 1369495093119362681472⟩, ⟨.hall 19 12, 31155694531845820605789120⟩, ⟨.hall 9 13, 2744248868502171030⟩, ⟨.hall 13 13, 39719587330184797035⟩, ⟨.hall 16 13, 15384868480583420586768⟩, ⟨.hall 17 13, 157808289242167448520636⟩, ⟨.hall 10 17, 31696879832216071200⟩, ⟨.hall 14 17, 25084108151076221607360⟩, ⟨.hall 11 20, 7569865764898866308880⟩, ⟨.hall 4 26, 254492446485482540375040⟩, ⟨.hall 3 29, 453501355624584112061248032⟩, ⟨.hall 2 30, 548461833012058814632143360⟩]
  caps := #[0, 0, 0, 170892372224477409425920, 42394015193101732224064, 0, 0, 2601984810332998683450, 0, 2419192767554726641632, 757614493549213267968, 8924867721920626973952, 1142436733221784000000, 10223806881505710175760, 571218366610892000000, 24876958744329642946996, 15145196753923253396379, 0, 2508383554402550520760064, 0, 0] }

theorem case_53_33_15_checked :
    (Witness.linear .positive case_53_33_15).check 53 33 15 = true := by
  change case_53_33_15.check 53 33 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_33_16 : Certificate := {
  objectiveScale := 147422717405964000000
  eta := 9448339604104000862492630400
  rows := #[⟨.count 2, 1806449462438788564472275200⟩, ⟨.count 3, 329077508190836327131809600⟩, ⟨.count 4, 62527711436401728970252800⟩, ⟨.count 5, 11483497216153164067866000⟩, ⟨.count 6, 2233132551300061748937600⟩, ⟨.count 7, 433913131873898136860400⟩, ⟨.count 8, 88440893120794524710400⟩, ⟨.count 9, 21685026678656349808800⟩, ⟨.count 10, 5798135475576564120000⟩, ⟨.count 11, 2551179609253688212800⟩, ⟨.path 9, 1858375568590097356800⟩, ⟨.privateRow 2 31, 200152796243998108735224000⟩, ⟨.privateRow 3 30, 322625008030231693266480000⟩, ⟨.privateRow 6 21, 436808518255828909990800⟩, ⟨.privateRow 6 22, 838960138909759171905600⟩, ⟨.privateRow 6 26, 30494604199910620442072400⟩, ⟨.privateRow 7 18, 30884121407261580057600⟩, ⟨.privateRow 7 19, 185567945387381368812000⟩, ⟨.privateRow 7 20, 415074319181075833765200⟩, ⟨.privateRow 7 24, 10114505891387532154119600⟩, ⟨.privateRow 8 16, 21047231776342927755600⟩, ⟨.privateRow 8 17, 74456649336737270803200⟩, ⟨.privateRow 8 18, 169095373475846021854650⟩, ⟨.privateRow 8 19, 309937951338498669186000⟩, ⟨.privateRow 8 20, 263515593805828878313800⟩, ⟨.privateRow 8 21, 434848564397291155871760⟩, ⟨.privateRow 8 22, 657672843435523707191400⟩, ⟨.privateRow 8 23, 3141139893893603612010000⟩, ⟨.privateRow 8 24, 2805021980374430189973600⟩, ⟨.privateRow 9 14, 10385104874032690401600⟩, ⟨.privateRow 9 15, 31719666475054190112480⟩, ⟨.privateRow 9 16, 69700746608375456974400⟩, ⟨.privateRow 9 17, 129259766868853536115200⟩, ⟨.privateRow 9 18, 256818747331537946755200⟩, ⟨.privateRow 9 19, 254669142290407524279600⟩, ⟨.privateRow 9 20, 395404492994218854226080⟩, ⟨.privateRow 10 12, 4599854143957407535200⟩, ⟨.privateRow 10 13, 14463712495438265404800⟩, ⟨.privateRow 10 14, 31309931568113446248000⟩, ⟨.privateRow 10 15, 57775198827745141142400⟩, ⟨.privateRow 10 16, 115962709511531282400000⟩, ⟨.privateRow 10 17, 197567324804931724843200⟩, ⟨.privateRow 10 18, 213294077028209872094400⟩, ⟨.privateRow 10 19, 299647641377796833721600⟩, ⟨.privateRow 10 20, 208066091541065003446200⟩, ⟨.privateRow 10 21, 109314180832870155542400⟩, ⟨.privateRow 11 10, 1998126686967923635200⟩, ⟨.privateRow 11 11, 6957762570691876944000⟩, ⟨.privateRow 11 12, 15570629268048336736800⟩, ⟨.privateRow 11 13, 28608000436494767368080⟩, ⟨.privateRow 11 14, 56705764951138797093600⟩, ⟨.privateRow 11 16, 347341447189753771154400⟩, ⟨.privateRow 11 18, 309458086602472380212640⟩, ⟨.privateRow 12 8, 890888117517160963200⟩, ⟨.privateRow 12 9, 3554207489814967339200⟩, ⟨.privateRow 12 10, 8704719314907260244600⟩, ⟨.privateRow 12 11, 16827477624673317201600⟩, ⟨.privateRow 12 12, 33732263722354321924800⟩, ⟨.privateRow 12 13, 59842484661506266720000⟩, ⟨.privateRow 12 14, 11675190017348475918300⟩, ⟨.privateRow 12 15, 280143818044714524700800⟩, ⟨.privateRow 12 16, 135283385390702522173200⟩, ⟨.privateRow 12 17, 210529010643634915071840⟩, ⟨.privateRow 12 19, 589086269403411820840800⟩, ⟨.privateRow 13 6, 425196601542281368800⟩, ⟨.privateRow 13 7, 1943755892764714828800⟩, ⟨.privateRow 13 8, 5347664950166384907600⟩, ⟨.privateRow 13 9, 11249993415806194549500⟩, ⟨.privateRow 13 10, 23637065622100459729200⟩, ⟨.privateRow 13 11, 42817297775307733838160⟩, ⟨.privateRow 13 12, 72354288362444879590800⟩, ⟨.privateRow 13 13, 27637779100248288972000⟩, ⟨.privateRow 13 14, 250683767794999315576800⟩, ⟨.privateRow 13 15, 242964424731285278821800⟩, ⟨.privateRow 13 19, 1997361035744866729938000⟩, ⟨.privateRow 14 4, 222089296341280893525⟩, ⟨.privateRow 14 5, 1158154552772309252160⟩, ⟨.privateRow 14 6, 3638034187685744160600⟩, ⟨.privateRow 14 8, 36422644599970066538100⟩, ⟨.privateRow 14 10, 122237948706241003796160⟩, ⟨.privateRow 14 11, 76683869630530173211200⟩, ⟨.privateRow 14 13, 392287252331075203674000⟩, ⟨.privateRow 14 14, 324743904427917395421000⟩, ⟨.privateRow 14 19, 5040341257053852243093600⟩, ⟨.privateRow 15 2, 162575171177931111600⟩, ⟨.privateRow 15 3, 806101890423908428350⟩, ⟨.privateRow 15 4, 2763777910024828897200⟩, ⟨.privateRow 15 5, 7304270190779904942600⟩, ⟨.privateRow 15 8, 151840283359848933049200⟩, ⟨.privateRow 15 9, 130910947004842728764040⟩, ⟨.privateRow 15 11, 403396417450707317787150⟩, ⟨.privateRow 15 12, 281510521406814714814800⟩, ⟨.privateRow 15 14, 1228222903215033961915680⟩, ⟨.privateRow 16 1, 812875855889655558000⟩, ⟨.privateRow 16 2, 2418305671271725285050⟩, ⟨.privateRow 16 3, 7185822566064555132720⟩, ⟨.privateRow 16 4, 20333508909468384029400⟩, ⟨.privateRow 16 7, 334165874575729312116000⟩, ⟨.privateRow 16 8, 352658061319168167282720⟩, ⟨.privateRow 16 9, 104409387712049091672000⟩, ⟨.privateRow 16 10, 644996669752044443884050⟩, ⟨.privateRow 16 11, 789650831435665399200⟩, ⟨.privateRow 16 13, 4636513821857652957942720⟩, ⟨.privateRow 17 0, 3901804108270346678400⟩, ⟨.privateRow 17 1, 7600389252568279467300⟩, ⟨.privateRow 17 2, 27269275378911645119040⟩, ⟨.privateRow 17 3, 71858225660645551327200⟩, ⟨.privateRow 17 4, 5102359218507376425600⟩, ⟨.privateRow 17 6, 918579276277343131651200⟩, ⟨.privateRow 17 7, 1216062280410924714768000⟩, ⟨.privateRow 17 8, 675590155783847063760000⟩, ⟨.privateRow 17 9, 1445455846942985513235600⟩, ⟨.privateRow 17 10, 1129200688953001520856000⟩, ⟨.privateRow 17 12, 5795089521740061231648960⟩, ⟨.privateRow 17 13, 11591284554644132394856800⟩, ⟨.privateRow 18 0, 86137744862440500629400⟩, ⟨.privateRow 18 1, 112762138729013019005760⟩, ⟨.privateRow 18 2, 344550979449762002517600⟩, ⟨.privateRow 18 4, 146173142796868728340800⟩, ⟨.privateRow 18 6, 12178310982733406052622080⟩, ⟨.privateRow 19 0, 2292830154156598053117120⟩, ⟨.privateRow 19 1, 1812248658144852091164000⟩, ⟨.privateRow 19 2, 520440640287752395411200⟩, ⟨.privateRow 19 3, 892700264938019733795600⟩, ⟨.privateRow 19 4, 358788623228677787745600⟩, ⟨.privateRow 19 5, 60891554913667030263110400⟩, ⟨.privateRow 19 6, 42599030186516029402176000⟩, ⟨.privateRow 20 6, 2303166683540090913192648000⟩, ⟨.hall 16 6, 32157726167063296800⟩, ⟨.hall 15 7, 4950205532661363975⟩, ⟨.hall 10 11, 2251193495684918400⟩, ⟨.hall 14 15, 347254861244089698900⟩, ⟨.hall 15 16, 13954368859439087079000⟩, ⟨.hall 16 16, 273126287578924267488000⟩, ⟨.hall 15 17, 42992100822608449512000⟩, ⟨.hall 11 18, 206117176906210489920⟩, ⟨.hall 6 19, 12740959210904636712⟩, ⟨.hall 7 20, 140933906499340494540⟩, ⟨.hall 9 20, 529364967151630509900⟩, ⟨.hall 8 22, 3696129298624063260960⟩, ⟨.hall 5 24, 8341108729064555343900⟩, ⟨.hall 6 24, 26794944947857811236512⟩, ⟨.hall 8 24, 555612903167329910238336⟩, ⟨.hall 4 28, 102955873493498715757267200⟩, ⟨.hall 3 29, 148420032820432024793581440⟩]
  caps := #[0, 1451820850967847826065600, 0, 99165206300629943073600, 4768071086456988710400, 0, 3064395267027433739400, 0, 971528326649544824160, 0, 636285726676984356000, 0, 2255684743170956529740, 294845434811928000000, 9611696477129031484485, 147422717405964000000, 106402010240354357228700, 29934030230128097793720, 173716985966819581125840, 0, 0] }

theorem case_53_33_16_checked :
    (Witness.linear .positive case_53_33_16).check 53 33 16 = true := by
  change case_53_33_16.check 53 33 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_33_17 : Certificate := {
  objectiveScale := 49811423336151838320960000
  eta := 2116324658676102249719650996609920
  rows := #[⟨.count 2, 391075991876849870861711533572480⟩, ⟨.count 3, 72212484489179932239835065693120⟩, ⟨.count 4, 13104177453102800307861616078080⟩, ⟨.count 5, 2567677942582092387783090154800⟩, ⟨.count 6, 485874420985089145041858745920⟩, ⟨.count 7, 96212756630710721790467078400⟩, ⟨.count 8, 20722747581999232385639063040⟩, ⟨.count 9, 4995662363517672092966559840⟩, ⟨.count 10, 1513837079853840028171684800⟩, ⟨.count 11, 555073595946408010329617760⟩, ⟨.path 9, 338230399595501847706272000⟩, ⟨.path 10, 60027732124414274950329600⟩, ⟨.privateRow 2 31, 35083981705388664700893820138560⟩, ⟨.privateRow 3 28, 4906850588166246811313820998400⟩, ⟨.privateRow 3 29, 11135824807032843457898310432480⟩, ⟨.privateRow 4 25, 494533569081853110003000782976⟩, ⟨.privateRow 4 26, 2360820515826064335933585936240⟩, ⟨.privateRow 4 27, 4111491800019038177845959816960⟩, ⟨.privateRow 4 28, 7124554628504128948584087155520⟩, ⟨.privateRow 5 23, 395875404886778490700359333000⟩, ⟨.privateRow 5 24, 854850342663864763108299991584⟩, ⟨.privateRow 5 25, 1485885760215538709651525942040⟩, ⟨.privateRow 5 26, 2630617120878015651621020701920⟩, ⟨.privateRow 5 27, 3250788514660138512495406411440⟩, ⟨.privateRow 6 20, 30016375636351938725255093730⟩, ⟨.privateRow 6 21, 164077111754158463053385821200⟩, ⟨.privateRow 6 22, 324918496871629333379889862680⟩, ⟨.privateRow 6 23, 535985231730250979307727015920⟩, ⟨.privateRow 6 24, 944789225789281223248680362580⟩, ⟨.privateRow 6 25, 1239941901078284427074644472880⟩, ⟨.privateRow 6 26, 1273215479413071885027181004160⟩, ⟨.privateRow 7 18, 21743319405234030182409127440⟩, ⟨.privateRow 7 19, 63891283700081338688982044250⟩, ⟨.privateRow 7 20, 126107434583824410346790777760⟩, ⟨.privateRow 7 21, 204108490852293459798348016320⟩, ⟨.privateRow 7 22, 352069965870807876951830601888⟩, ⟨.privateRow 7 23, 466631869658947000683765330240⟩, ⟨.privateRow 7 24, 510156688134744708160405199040⟩, ⟨.privateRow 7 25, 367326560136534862835747524320⟩, ⟨.privateRow 8 15, 470971535954528008764524160⟩, ⟨.privateRow 8 16, 10398378697396043393508172704⟩, ⟨.privateRow 8 17, 26540741198770842271686538080⟩, ⟨.privateRow 8 18, 50742977896100798944299223560⟩, ⟨.privateRow 8 19, 82507725226033933535423897040⟩, ⟨.privateRow 8 20, 141096624347377213959064781160⟩, ⟨.privateRow 8 21, 188558500542994801108971153072⟩, ⟨.privateRow 8 22, 209470898270275722898139502180⟩, ⟨.privateRow 8 23, 81996705090083272192580756880⟩, ⟨.privateRow 9 13, 385467774962783340506679000⟩, ⟨.privateRow 9 14, 4496656807565850750347004480⟩, ⟨.privateRow 9 15, 11718220358868613551403041600⟩, ⟨.privateRow 9 16, 22134416233418492263761300800⟩, ⟨.privateRow 9 17, 35863921782537362000741414160⟩, ⟨.privateRow 9 18, 61807004374032574483528072800⟩, ⟨.privateRow 9 19, 84504815412507782461477548240⟩, ⟨.privateRow 9 20, 51856208830193317231682512512⟩, ⟨.privateRow 10 11, 194081676904338465150216000⟩, ⟨.privateRow 10 12, 1963783100810398036544935560⟩, ⟨.privateRow 10 13, 5463575642745222647128716960⟩, ⟨.privateRow 10 14, 10647320794972008198140849760⟩, ⟨.privateRow 10 15, 17369878790322949656577331520⟩, ⟨.privateRow 10 16, 30068588998596897559560089340⟩, ⟨.privateRow 10 17, 24985520565587664464966950080⟩, ⟨.privateRow 11 9, 75691853992692001408584240⟩, ⟨.privateRow 11 10, 892775713759956939690993600⟩, ⟨.privateRow 11 11, 2720701640737318050630777960⟩, ⟨.privateRow 11 12, 5647071046363869923270739360⟩, ⟨.privateRow 11 13, 9567450344676268978045047936⟩, ⟨.privateRow 11 14, 9694164115064034847069788960⟩, ⟨.privateRow 12 7, 20558281331348444827022880⟩, ⟨.privateRow 12 8, 427318561958742674618832720⟩, ⟨.privateRow 12 9, 1465963599550769873434631520⟩, ⟨.privateRow 12 10, 3315022864679936728357439400⟩, ⟨.privateRow 12 11, 3212698691689816059786575520⟩, ⟨.privateRow 13 6, 209694469579754137235633376⟩, ⟨.privateRow 13 7, 859042469917060015986313200⟩, ⟨.privateRow 13 8, 1224008442343361253547362240⟩, ⟨.privateRow 14 4, 96642277865669251798460235⟩, ⟨.privateRow 14 5, 458155983955765341859367040⟩, ⟨.privateRow 15 2, 47163115995446432250228960⟩, ⟨.privateRow 15 3, 75166216117742751398802405⟩, ⟨.hall 6 26, 164452545129899992986298358080⟩, ⟨.hall 5 27, 1022045778583822154019716129700⟩, ⟨.hall 4 28, 2985249600562534740243526798080⟩, ⟨.hall 3 29, 6896851104478113573679981736640⟩, ⟨.hall 2 30, 13834152948571934558349288879360⟩, ⟨.assumptionRow 17, 57461258796689631105766544⟩]
  caps := #[0, 914428002425782540684123895760, 0, 124436345313867471065153372400, 7345516371500460174867509664, 2576550441371646266003400066, 465450295403070210737790, 60382129781397625103590688, 1080878688584782212795521852, 826638159251162088052441648, 0, 32428886065258593867225024, 194323547239107500610517264, 395677667714751874178656512, 326068228331924124666986223, 0, 5008179236255034662501975296, 689710091245587943708633456, 49811423336151838320960000, 0, 0] }

theorem case_53_33_17_checked :
    (Witness.linear .conditional case_53_33_17).check 53 33 17 = true := by
  change case_53_33_17.check 53 33 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_33_18 : Certificate := {
  objectiveScale := 18901601882163000000
  eta := 904246724751714451099792800
  rows := #[⟨.count 2, 153575220034431694108209600⟩, ⟨.count 3, 25744827542144466018463200⟩, ⟨.count 4, 4182493963395640744051200⟩, ⟨.count 5, 710103941934752203839000⟩, ⟨.count 6, 120480360328261299366000⟩, ⟨.count 7, 23000796062668066242600⟩, ⟨.count 8, 5616800015303557080000⟩, ⟨.count 9, 1853544005050173836400⟩, ⟨.count 10, 612741819851297136000⟩, ⟨.count 11, 168504000459106712400⟩, ⟨.count 12, 224672000612142283200⟩, ⟨.path 8, 537057992399056128000⟩, ⟨.privateRow 2 31, 14374402263164557207994400⟩, ⟨.privateRow 3 28, 1892312406933580165934400⟩, ⟨.privateRow 3 29, 4423211289384833521976400⟩, ⟨.privateRow 4 25, 172907571671104701150720⟩, ⟨.privateRow 4 26, 864537858355523505753600⟩, ⟨.privateRow 4 27, 1604457647038178758425600⟩, ⟨.privateRow 4 28, 2945562264025491403893600⟩, ⟨.privateRow 5 23, 125469951008522625905400⟩, ⟨.privateRow 5 24, 302077121623040603319480⟩, ⟨.privateRow 5 25, 567444242546060983453350⟩, ⟨.privateRow 5 26, 1086757189627649902362000⟩, ⟨.privateRow 5 27, 1459090181975443281564300⟩, ⟨.privateRow 6 20, 6267412683742885775100⟩, ⟨.privateRow 6 21, 49722053468806250532000⟩, ⟨.privateRow 6 22, 110196935633576370278700⟩, ⟨.privateRow 6 23, 200897958414034093932720⟩, ⟨.privateRow 6 24, 388214494391064186846000⟩, ⟨.privateRow 6 25, 565689772652391858471000⟩, ⟨.privateRow 6 26, 649985459104286464559400⟩, ⟨.privateRow 7 18, 3940675566292336872000⟩, ⟨.privateRow 7 19, 18117690549363536306175⟩, ⟨.privateRow 7 20, 41165985826446733395000⟩, ⟨.privateRow 7 21, 74687392203493584715200⟩, ⟨.privateRow 7 22, 143689780391497783443000⟩, ⟨.privateRow 7 23, 214243809583729589814150⟩, ⟨.privateRow 7 24, 268325235397746738010800⟩, ⟨.privateRow 7 25, 240699940655812076439000⟩, ⟨.privateRow 8 16, 1634488804453335110280⟩, ⟨.privateRow 8 17, 6802568907423196908000⟩, ⟨.privateRow 8 18, 15811292043079513180200⟩, ⟨.privateRow 8 19, 29311672079862705733200⟩, ⟨.privateRow 8 20, 56622024820939274997300⟩, ⟨.privateRow 8 21, 86217880234909601178000⟩, ⟨.privateRow 8 22, 110763296301786145617600⟩, ⟨.privateRow 8 23, 112176857638970874149400⟩, ⟨.privateRow 8 24, 36270486098822719844100⟩, ⟨.privateRow 9 14, 554871759087563517600⟩, ⟨.privateRow 9 15, 2641768273864439679960⟩, ⟨.privateRow 9 16, 6403152017446055071200⟩, ⟨.privateRow 9 17, 12200157699907267940850⟩, ⟨.privateRow 9 18, 24045253398847132452000⟩, ⟨.privateRow 9 19, 37701209880498653689200⟩, ⟨.privateRow 9 20, 50176746803378443248000⟩, ⟨.privateRow 9 21, 33780371425371476205300⟩, ⟨.privateRow 10 12, 160844727710965498200⟩, ⟨.privateRow 10 13, 1037483308611855378000⟩, ⟨.privateRow 10 14, 2760401898430093597680⟩, ⟨.privateRow 10 15, 5480635166447713272000⟩, ⟨.privateRow 10 16, 11102115848430689982900⟩, ⟨.privateRow 10 17, 18191866958656546755600⟩, ⟨.privateRow 10 18, 22045940060066461539000⟩, ⟨.privateRow 11 10, 35350489606805604000⟩, ⟨.privateRow 11 11, 402111819277413745500⟩, ⟨.privateRow 11 12, 1251942945559809375600⟩, ⟨.privateRow 11 13, 2683809170948681455680⟩, ⟨.privateRow 11 14, 5667861833624498508000⟩, ⟨.privateRow 11 15, 9786635753937436444050⟩, ⟨.privateRow 11 16, 1615012368036633165600⟩, ⟨.privateRow 12 9, 149781333741428188800⟩, ⟨.privateRow 12 10, 585083334927453862500⟩, ⟨.privateRow 12 11, 1419518549322171698400⟩, ⟨.privateRow 12 12, 3233404542143081025720⟩, ⟨.privateRow 12 13, 1838981930936423873600⟩, ⟨.privateRow 13 7, 42126000114776678100⟩, ⟨.privateRow 13 8, 274359077670596826600⟩, ⟨.privateRow 13 9, 793373002161627437550⟩, ⟨.privateRow 13 10, 1161656366801417487000⟩, ⟨.privateRow 14 5, 10431200028420891720⟩, ⟨.privateRow 14 6, 111762857447366697000⟩, ⟨.privateRow 14 7, 457368001246146790800⟩, ⟨.privateRow 14 8, 73887666867981316350⟩, ⟨.privateRow 15 4, 40565777888303467800⟩, ⟨.privateRow 15 5, 121697333664910403400⟩, ⟨.privateRow 16 3, 24339466732982080680⟩, ⟨.hall 6 26, 158206533764383524420000⟩, ⟨.hall 5 27, 576584581570964789823000⟩, ⟨.hall 4 28, 1441030717305548732563200⟩, ⟨.hall 3 29, 3050319328844246279140320⟩, ⟨.hall 2 30, 5785318510730445220934400⟩, ⟨.assumptionRow 18, 17143148055861611784⟩]
  caps := #[0, 490951177297393184452080, 0, 17662272862188990355320, 851613258508508976480, 541740701185386262560, 67243315417912473840, 62071050213831666150, 40228782075141443784, 0, 72788290446253168332, 47518780699762902180, 89764785429758699260, 63434831233947609744, 17143148055861611784, 462690934756708666008, 2766056790328172044704, 1708619374907027823240, 247479278294420388216, 18901601882163000000, 0] }

theorem case_53_33_18_checked :
    (Witness.linear .conditional case_53_33_18).check 53 33 18 = true := by
  change case_53_33_18.check 53 33 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_33_19 : Certificate := {
  objectiveScale := 6048512602292160000
  eta := 565189580384717921391638880
  rows := #[⟨.count 2, 53982211193480160955203840⟩, ⟨.count 3, 7363467549662534832281760⟩, ⟨.count 4, 1162452931167224173276800⟩, ⟨.count 5, 187657288511291842042800⟩, ⟨.count 6, 28331139277191141911520⟩, ⟨.count 7, 4308085611737828280360⟩, ⟨.count 8, 853753602326140676160⟩, ⟨.count 9, 235905600642749397360⟩, ⟨.count 10, 61274181985129713600⟩, ⟨.count 11, 33700800091821342480⟩, ⟨.path 2, 10107832827539844076680000⟩, ⟨.path 8, 163523160910924214400⟩, ⟨.privateRow 2 31, 5079451991439496381270560⟩, ⟨.privateRow 3 28, 685204667466911535303360⟩, ⟨.privateRow 3 29, 1514401620126145059909600⟩, ⟨.privateRow 4 25, 58297890718838679644736⟩, ⟨.privateRow 4 26, 280974803965545139369920⟩, ⟨.privateRow 4 27, 542478034544704614195840⟩, ⟨.privateRow 4 28, 1035108841220261927159040⟩, ⟨.privateRow 5 23, 37920889169986081699440⟩, ⟨.privateRow 5 24, 94573431937675172690208⟩, ⟨.privateRow 5 25, 186890595309202906501380⟩, ⟨.privateRow 5 26, 379476625833923619881880⟩, ⟨.privateRow 5 27, 541577474275584277210680⟩, ⟨.privateRow 6 20, 1725059704700104968195⟩, ⟨.privateRow 6 21, 14120367771805747091640⟩, ⟨.privateRow 6 22, 33243654979464691862100⟩, ⟨.privateRow 6 23, 64489851055709320969728⟩, ⟨.privateRow 6 24, 133465465830307239408780⟩, ⟨.privateRow 6 25, 210309218884120498462320⟩, ⟨.privateRow 6 26, 262014359380552098520200⟩, ⟨.privateRow 7 18, 1008349336080686199600⟩, ⟨.privateRow 7 19, 4858331413237030318590⟩, ⟨.privateRow 7 20, 11878156489506132557160⟩, ⟨.privateRow 7 21, 23233759529969466157680⟩, ⟨.privateRow 7 22, 48417458051918411007552⟩, ⟨.privateRow 7 23, 78898989214968519747150⟩, ⟨.privateRow 7 24, 109016471497026739365720⟩, ⟨.privateRow 7 25, 111420863103577754907180⟩, ⟨.privateRow 8 16, 380257361036050814316⟩, ⟨.privateRow 8 17, 1706883115761692068200⟩, ⟨.privateRow 8 18, 4329148611795216619410⟩, ⟨.privateRow 8 19, 8750974423842941930640⟩, ⟨.privateRow 8 20, 18537312317173506216360⟩, ⟨.privateRow 8 21, 31169870004925559659752⟩, ⟨.privateRow 8 22, 44566499721426073651260⟩, ⟨.privateRow 8 23, 51992845474993260037200⟩, ⟨.privateRow 8 24, 36964160900712709143480⟩, ⟨.privateRow 9 14, 110633939695373094000⟩, ⟨.privateRow 9 15, 609984481661966298888⟩, ⟨.privateRow 9 16, 1644266197072567228160⟩, ⟨.privateRow 9 17, 3458076542755223308920⟩, ⟨.privateRow 9 18, 7555398420585470495040⟩, ⟨.privateRow 9 19, 13203848658197484126840⟩, ⟨.privateRow 9 20, 19659548960231156920944⟩, ⟨.privateRow 9 21, 24402187666486303734060⟩, ⟨.privateRow 9 22, 9167865802756583722800⟩, ⟨.privateRow 10 12, 23233127336028349740⟩, ⟨.privateRow 10 13, 213345560911860730080⟩, ⟨.privateRow 10 14, 653795521781334044112⟩, ⟨.privateRow 10 15, 1453900173658272259920⟩, ⟨.privateRow 10 16, 3301146554448863320200⟩, ⟨.privateRow 10 17, 6070520743812493768800⟩, ⟨.privateRow 10 18, 9508221189542503307880⟩, ⟨.privateRow 10 19, 9794677990322984718960⟩, ⟨.privateRow 11 10, 707009792136112080⟩, ⟨.privateRow 11 11, 68933454733270927800⟩, ⟨.privateRow 11 12, 266264172626290937280⟩, ⟨.privateRow 11 13, 654408263601185341248⟩, ⟨.privateRow 11 14, 1567938234575041449120⟩, ⟨.privateRow 11 15, 3057581681057972708640⟩, ⟨.privateRow 11 16, 5103264013904374718400⟩, ⟨.privateRow 11 17, 1114679493946151373240⟩, ⟨.privateRow 12 9, 14690092347716995440⟩, ⟨.privateRow 12 10, 106095111400178300400⟩, ⟨.privateRow 12 11, 309775031147044663200⟩, ⟨.privateRow 12 12, 815933815556430058488⟩, ⟨.privateRow 12 13, 1710419619475031344880⟩, ⟨.privateRow 12 14, 1420114270535916015060⟩, ⟨.privateRow 13 7, 1604800004372444880⟩, ⟨.privateRow 13 8, 34132861631460077640⟩, ⟨.privateRow 13 9, 147441000401718373350⟩, ⟨.privateRow 13 10, 457513892155635194880⟩, ⟨.privateRow 13 11, 885207682411840595808⟩, ⟨.privateRow 14 6, 7450857163157779800⟩, ⟨.privateRow 14 7, 58575200159594238120⟩, ⟨.privateRow 14 8, 265126334055697664550⟩, ⟨.privateRow 14 9, 178278691394829785760⟩, ⟨.privateRow 15 5, 17385333380701486200⟩, ⟨.privateRow 15 6, 131058667023749665200⟩, ⟨.privateRow 15 7, 4056577788830346780⟩, ⟨.privateRow 16 4, 41724800113683566880⟩, ⟨.hall 7 25, 8574045223360879882620⟩, ⟨.hall 6 26, 85799324618954387961520⟩, ⟨.hall 5 27, 249722928680396147776800⟩, ⟨.hall 4 28, 566381069460405636877440⟩, ⟨.hall 3 29, 1129594651077698364358800⟩, ⟨.hall 2 30, 2063302133312004300555840⟩, ⟨.assumptionRow 19, 3663130444763189400⟩]
  caps := #[0, 161519580377509510316160, 11279043447307463908080, 0, 629231715946063758528, 77841887276510557200, 13829156722312106175, 77902471064112728748, 4411698255186228006, 1596807327005130240, 17910239920663500396, 42582328752337562160, 15930270066286976400, 57179624309029912536, 3663130444763189400, 213342716472451686120, 3663130444763189400, 2280379978753178702400, 493082307979609748400, 74967533385034890600, 6048512602292160000] }

theorem case_53_33_19_checked :
    (Witness.linear .conditional case_53_33_19).check 53 33 19 = true := by
  change case_53_33_19.check 53 33 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_33_20 : Certificate := {
  objectiveScale := 12329714524652156632000000
  eta := 1725166550043074626668396472576320
  rows := #[⟨.count 2, 171001585197415859942442541714560⟩, ⟨.count 3, 24391799843662788228055964920320⟩, ⟨.count 4, 4016364952681244938755524544000⟩, ⟨.count 5, 676030393975011270941393247600⟩, ⟨.count 6, 101794077248990173447769328960⟩, ⟨.count 7, 14368891856575143530892609360⟩, ⟨.count 8, 1598023190721980744862940800⟩, ⟨.count 9, 79901159536099037243147040⟩, ⟨.path 2, 30725191888011523781479762761600⟩, ⟨.path 8, 199742314021818290558035200⟩, ⟨.path 9, 119636026610179005964477440⟩, ⟨.privateRow 2 31, 16351452694424523575661069147840⟩, ⟨.privateRow 3 28, 2125518808770486425921865240000⟩, ⟨.privateRow 3 29, 4875613144425838863153078573600⟩, ⟨.privateRow 4 25, 174781123113232107334809378432⟩, ⟨.privateRow 4 26, 897969181446449030057108009040⟩, ⟨.privateRow 4 27, 1740424812828539473460727302400⟩, ⟨.privateRow 4 28, 3350202351908941898913659955840⟩, ⟨.privateRow 5 23, 122424112745880188758187432760⟩, ⟨.privateRow 5 24, 302543077211454467886601495392⟩, ⟨.privateRow 5 25, 597477566506083904951724313900⟩, ⟨.privateRow 5 26, 1221355807808887200125871795600⟩, ⟨.privateRow 5 27, 1766421542874270807439310115720⟩, ⟨.privateRow 6 20, 7494617790653400666966576870⟩, ⟨.privateRow 6 21, 46404183741056501970966436080⟩, ⟨.privateRow 6 22, 106227851777692409838493219800⟩, ⟨.privateRow 6 23, 204396043999956459383219366880⟩, ⟨.privateRow 6 24, 425685634550163413821333558620⟩, ⟨.privateRow 6 25, 681416323988185354192597974000⟩, ⟨.privateRow 6 26, 868365801838324336758522030720⟩, ⟨.privateRow 7 17, 91505851754437230747508872⟩, ⟨.privateRow 7 18, 4800622312762818081558498480⟩, ⟨.privateRow 7 19, 16335031103731294840197191880⟩, ⟨.privateRow 7 20, 37835373221554760775099324720⟩, ⟨.privateRow 7 21, 72833711734275039067949629200⟩, ⟨.privateRow 7 22, 152453695285149423032417213664⟩, ⟨.privateRow 7 23, 252846743749845307528336170300⟩, ⟨.privateRow 7 24, 359411903134230124876566828960⟩, ⟨.privateRow 7 25, 382407900744050183900907009000⟩, ⟨.privateRow 8 15, 207016640616256596493608240⟩, ⟨.privateRow 8 16, 1976222012526182854480503456⟩, ⟨.privateRow 8 17, 6028098591667916254232982240⟩, ⟨.privateRow 8 18, 13796266879899767097316722240⟩, ⟨.privateRow 8 19, 27118834028264089902406215600⟩, ⟨.privateRow 8 20, 57502201146145940469318153120⟩, ⟨.privateRow 8 21, 98451545408396697056431011120⟩, ⟨.privateRow 8 22, 145270295681570062087696712100⟩, ⟨.privateRow 8 23, 177584766022287671330518915680⟩, ⟨.privateRow 8 24, 138182396987721943325585876760⟩, ⟨.privateRow 9 12, 1365831786941863884498240⟩, ⟨.privateRow 9 13, 124290692611709613489339840⟩, ⟨.privateRow 9 14, 759464556802719131775771360⟩, ⟨.privateRow 9 15, 2318021417208384291576188016⟩, ⟨.privateRow 9 16, 5344499782303513380041613120⟩, ⟨.privateRow 9 17, 10637951601570074597400104520⟩, ⟨.privateRow 9 18, 23086362016438266268841358240⟩, ⟨.privateRow 9 19, 41012969259659131746399067680⟩, ⟨.privateRow 9 20, 63070424175150531153640577952⟩, ⟨.privateRow 9 21, 82089563516726638652084345040⟩, ⟨.privateRow 9 22, 53557451306826680593573152960⟩, ⟨.privateRow 10 10, 1556516094859072154087280⟩, ⟨.privateRow 10 11, 55874936738530795274928000⟩, ⟨.privateRow 10 12, 301445283704373640508236560⟩, ⟨.privateRow 10 13, 939003709589527528593017280⟩, ⟨.privateRow 10 14, 2230695099412364939760950544⟩, ⟨.privateRow 10 15, 4522889879194939441521171840⟩, ⟨.privateRow 10 16, 9981289167958371777430856940⟩, ⟨.privateRow 10 17, 18538106689771549355179504800⟩, ⟨.privateRow 10 18, 29919352375381084945865696160⟩, ⟨.privateRow 10 19, 41574752429165131778625127104⟩, ⟨.privateRow 10 20, 3686348951324569218263374800⟩, ⟨.privateRow 11 8, 968498903467867118098752⟩, ⟨.privateRow 11 9, 24385418819458797080700720⟩, ⟨.privateRow 11 10, 127953605131235521179585120⟩, ⟨.privateRow 11 11, 412217345788510942140781320⟩, ⟨.privateRow 11 12, 1016263508479805110059531360⟩, ⟨.privateRow 11 13, 2123918095305032589990563136⟩, ⟨.privateRow 11 14, 4776313758935698004090345280⟩, ⟨.privateRow 11 15, 9218596281477426421928089740⟩, ⟨.privateRow 11 16, 15737415396421792192591792320⟩, ⟨.privateRow 11 17, 11022728145093662637861421200⟩, ⟨.privateRow 12 6, 554869163445132203077410⟩, ⟨.privateRow 12 7, 11245348379154679315702176⟩, ⟨.privateRow 12 8, 60242937745471496334118800⟩, ⟨.privateRow 12 9, 200777272680453991021241280⟩, ⟨.privateRow 12 10, 516398234779603036997376240⟩, ⟨.privateRow 12 11, 1118616233505386521404058560⟩, ⟨.privateRow 12 12, 2586134196985072172103192528⟩, ⟨.privateRow 12 13, 5182724595094621502166599360⟩, ⟨.privateRow 12 14, 7226615984709401812880187840⟩, ⟨.privateRow 13 5, 5826126216173888132312805⟩, ⟨.privateRow 13 6, 32848254475951826422182672⟩, ⟨.privateRow 13 7, 112242105062615314222516080⟩, ⟨.privateRow 13 8, 300141535180474588618488240⟩, ⟨.privateRow 13 9, 675830641076171023348285380⟩, ⟨.privateRow 13 10, 1612550674273998751634422080⟩, ⟨.privateRow 13 11, 3370497246431111054373419304⟩, ⟨.privateRow 13 12, 47348835280651281329272320⟩, ⟨.privateRow 14 3, 4364349050291123883029040⟩, ⟨.privateRow 14 4, 20094190419048716211446205⟩, ⟨.privateRow 14 5, 74193933854949106011493680⟩, ⟨.privateRow 14 6, 204916579218430864222220640⟩, ⟨.privateRow 14 7, 479406957216594223458882240⟩, ⟨.privateRow 14 8, 1182981056465021856961038120⟩, ⟨.privateRow 14 9, 177615781046696344694181840⟩, ⟨.privateRow 15 1, 3205910722127430506669480⟩, ⟨.privateRow 15 2, 16972468528909926211779600⟩, ⟨.privateRow 15 3, 57706392998293749120050640⟩, ⟨.privateRow 15 4, 138495343195904997888121536⟩, ⟨.privateRow 15 5, 478138684843005349851848160⟩, ⟨.privateRow 16 0, 19235464332764583040016880⟩, ⟨.privateRow 16 1, 50917405586729778635338800⟩, ⟨.privateRow 16 2, 129839384246160935520113940⟩, ⟨.privateRow 17 0, 40733924469383822908271040⟩, ⟨.hall 7 25, 46549083859739030780570079720⟩, ⟨.hall 6 26, 307498132823574624477709843680⟩, ⟨.hall 5 27, 847572951875474849798800926900⟩, ⟨.hall 4 28, 1877710311647100933436262949120⟩, ⟨.hall 3 29, 3698402727260646381104045517600⟩, ⟨.hall 2 30, 6698707018965804962369336486400⟩]
  caps := #[0, 352744116631880986219470943680, 0, 3292354100955223609649023680, 24158094095563767201438576, 259207820954601707999336526, 16010851488064916160117440, 128853057023471739280427248, 52767063221870718724895892, 39734867074079968721330400, 70780467496603547222376172, 151327953666854237202930, 2723646130586960454245986, 79036772208165542061792732, 221858945129628488505906225, 0, 93113171834442672864291340, 4415078920919933702362006080, 4315400083628254821200000000, 949388018398216060664000000, 147956574295825879584000000] }

theorem case_53_33_20_checked :
    (Witness.linear .conditional case_53_33_20).check 53 33 20 = true := by
  change case_53_33_20.check 53 33 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_33_21 : Certificate := {
  objectiveScale := 256996531034933289600000
  eta := 15952720133771797089805751499840
  rows := #[⟨.count 2, 2873152908474789135220317452160⟩, ⟨.count 3, 479998053966710741067734768640⟩, ⟨.count 4, 81756928402743918108149164800⟩, ⟨.count 5, 12565101701241380856785220000⟩, ⟨.count 6, 1887557500008705213152624160⟩, ⟨.count 7, 240133054734835278596339760⟩, ⟨.count 8, 24056263086137344546323840⟩, ⟨.count 9, 2577456759229001201391840⟩, ⟨.path 8, 5602184265993078815251200⟩, ⟨.path 9, 1468916872431542637143040⟩, ⟨.privateRow 2 31, 342910002161344777835573177280⟩, ⟨.privateRow 3 30, 540883883069555642558657876160⟩, ⟨.privateRow 5 23, 883280112183560772821420280⟩, ⟨.privateRow 5 24, 3686880063626470951844267664⟩, ⟨.privateRow 6 21, 490105448367997141144024560⟩, ⟨.privateRow 6 22, 1397673658372652364439936200⟩, ⟨.privateRow 6 23, 3263203449226094909917702320⟩, ⟨.privateRow 6 27, 128817422641126636543762075440⟩, ⟨.privateRow 7 18, 17905823941098828451997280⟩, ⟨.privateRow 7 19, 168731365702384257219687240⟩, ⟨.privateRow 7 20, 485736629938238233211960160⟩, ⟨.privateRow 7 21, 1094559970419249176857734720⟩, ⟨.privateRow 7 22, 2667471368144170224301400736⟩, ⟨.privateRow 7 23, 2728621529756878277804422140⟩, ⟨.privateRow 7 24, 3560776968880890786716488800⟩, ⟨.privateRow 7 25, 547279985209624588428867360⟩, ⟨.privateRow 8 16, 10610530325492721612396408⟩, ⟨.privateRow 8 17, 54890282835432432992604000⟩, ⟨.privateRow 8 18, 164473959448300639163816790⟩, ⟨.privateRow 8 19, 384286529197428702931326240⟩, ⟨.privateRow 8 20, 964255212036005227231813920⟩, ⟨.privateRow 8 21, 1977596656131104988454579104⟩, ⟨.privateRow 8 22, 2790204335897028342223391460⟩, ⟨.privateRow 8 23, 3958830390133566456382233360⟩, ⟨.privateRow 8 24, 3947804602885753506798501600⟩, ⟨.privateRow 9 13, 143192042179388955632880⟩, ⟨.privateRow 9 14, 4035412097782779658744800⟩, ⟨.privateRow 9 15, 18529050258012930858894672⟩, ⟨.privateRow 9 16, 56067639626685186627807680⟩, ⟨.privateRow 9 17, 136569410228592216434859300⟩, ⟨.privateRow 9 18, 354748056496423324083629280⟩, ⟨.privateRow 9 19, 754622062285379796185277600⟩, ⟨.privateRow 9 20, 1391712096349917137587087296⟩, ⟨.privateRow 9 22, 6321164971328398983428276640⟩, ⟨.privateRow 10 11, 72096692565846187451520⟩, ⟨.privateRow 10 12, 1386359317464083979536520⟩, ⟨.privateRow 10 14, 32991446518131215377815552⟩, ⟨.privateRow 10 15, 44077114074491909433902880⟩, ⟨.privateRow 10 16, 137601043805202814137941640⟩, ⟨.privateRow 10 17, 311068904720975430708238560⟩, ⟨.privateRow 10 18, 611482089939510618354445920⟩, ⟨.privateRow 10 19, 1062661990405033295322933888⟩, ⟨.privateRow 10 20, 835506039929164639442086680⟩, ⟨.privateRow 10 21, 2345563755648670759969646880⟩, ⟨.privateRow 10 22, 3529358403262439145087690000⟩, ⟨.privateRow 11 9, 33473464405571444173920⟩, ⟨.privateRow 11 10, 468628501678000218434880⟩, ⟨.privateRow 11 11, 1054414128775500491478480⟩, ⟨.privateRow 11 12, 4430669470410183883384320⟩, ⟨.privateRow 11 13, 30367126908734414154580224⟩, ⟨.privateRow 11 14, 50689982931503690294039520⟩, ⟨.privateRow 11 15, 135814397642555438305158660⟩, ⟨.privateRow 11 16, 282951194620295417602145760⟩, ⟨.privateRow 11 17, 517287761102232574449035040⟩, ⟨.privateRow 11 18, 839735412156808591413461472⟩, ⟨.privateRow 11 19, 884829189730774162432357800⟩, ⟨.privateRow 11 20, 1132909402806565528066322400⟩, ⟨.privateRow 11 22, 5355955145677864496492243520⟩, ⟨.privateRow 12 7, 19092272290585194084384⟩, ⟨.privateRow 12 8, 184104054230642942956560⟩, ⟨.privateRow 12 9, 638856803569581494362080⟩, ⟨.privateRow 12 10, 1670573825426204482383600⟩, ⟨.privateRow 12 11, 5363192852537113610976960⟩, ⟨.privateRow 12 12, 36571247572615939268637552⟩, ⟨.privateRow 12 13, 57372278233208508223573920⟩, ⟨.privateRow 12 14, 138824684892917592486077160⟩, ⟨.privateRow 12 15, 268055502959816124944751360⟩, ⟨.privateRow 12 16, 453059621455586655622432320⟩, ⟨.privateRow 12 17, 675637331819228848258180992⟩, ⟨.privateRow 12 18, 728847494693089784171359200⟩, ⟨.privateRow 13 6, 85915225307633373379728⟩, ⟨.privateRow 13 7, 337524099422845395420360⟩, ⟨.privateRow 13 8, 958285205354372241543120⟩, ⟨.privateRow 13 9, 2291072674870223290126080⟩, ⟨.privateRow 13 10, 8279103529644670525682880⟩, ⟨.privateRow 13 11, 48198441397582322466027408⟩, ⟨.privateRow 13 12, 74841707379093960810785280⟩, ⟨.privateRow 13 13, 164473959448300639163816790⟩, ⟨.privateRow 13 14, 306165042185559214136759280⟩, ⟨.privateRow 13 15, 503749604387090345916471840⟩, ⟨.privateRow 13 16, 745915986120872947682798496⟩, ⟨.privateRow 13 17, 272243870193563251897013100⟩, ⟨.privateRow 13 19, 2285559781246316815334214120⟩, ⟨.privateRow 14 4, 49861514687465797050735⟩, ⟨.privateRow 14 5, 212742462666520734083136⟩, ⟨.privateRow 14 6, 626830470356712877209240⟩, ⟨.privateRow 14 7, 1534200451922024524638000⟩, ⟨.privateRow 14 8, 4188367233747126952261740⟩, ⟨.privateRow 14 9, 13707383674081506389220240⟩, ⟨.privateRow 14 10, 71800581149950747753058400⟩, ⟨.privateRow 14 11, 113196718677144573926735280⟩, ⟨.privateRow 14 12, 224077647005471291946003090⟩, ⟨.privateRow 14 13, 401513408557581721165118640⟩, ⟨.privateRow 14 14, 638892208195395079543417800⟩, ⟨.privateRow 14 15, 916494529167371322430149888⟩, ⟨.privateRow 14 16, 767867326186973274581319000⟩, ⟨.privateRow 14 19, 1991269450558634071018152960⟩, ⟨.privateRow 15 3, 116343534270753526451715⟩, ⟨.privateRow 15 4, 496399079555215046193984⟩, ⟨.privateRow 15 5, 1196676352499179129217640⟩, ⟨.privateRow 15 6, 3436609012305334935189120⟩, ⟨.privateRow 15 8, 43491328447394409160859280⟩, ⟨.privateRow 15 9, 116901983235253143378683232⟩, ⟨.privateRow 15 10, 207453448664116954721902480⟩, ⟨.privateRow 15 11, 376254989831616904544846310⟩, ⟨.privateRow 15 12, 657108281561215917399286320⟩, ⟨.privateRow 15 13, 1043058565915395615815108880⟩, ⟨.privateRow 15 14, 1517864285509958807499654576⟩, ⟨.privateRow 15 18, 12367783067118182875923111360⟩, ⟨.privateRow 16 2, 698061205624521158710290⟩, ⟨.privateRow 16 3, 1116897928999233853936464⟩, ⟨.privateRow 16 4, 3590029057497537387652920⟩, ⟨.privateRow 16 5, 9021098657301504204871440⟩, ⟨.privateRow 16 6, 930748274166028211613720⟩, ⟨.privateRow 16 7, 96459366595388378294512800⟩, ⟨.privateRow 16 8, 260795666421321104894164344⟩, ⟨.privateRow 16 9, 467856132480790181037829920⟩, ⟨.privateRow 16 10, 809750998524444544103936400⟩, ⟨.privateRow 16 11, 1369795531494060376577791920⟩, ⟨.privateRow 16 13, 7494385103584859159913673440⟩, ⟨.privateRow 17 1, 2792244822498084634841160⟩, ⟨.privateRow 17 2, 4467591715996935415745856⟩, ⟨.privateRow 17 3, 12764547759991244044988160⟩, ⟨.privateRow 17 4, 29211176604595346949107520⟩, ⟨.privateRow 17 5, 7445986193328225692909760⟩, ⟨.privateRow 17 6, 266024779452544790664866880⟩, ⟨.privateRow 17 7, 748321612429486682137430880⟩, ⟨.privateRow 17 8, 1377507445765721753188305600⟩, ⟨.privateRow 17 10, 8450130617114203557782161920⟩, ⟨.privateRow 17 12, 10186109112473012747900551680⟩, ⟨.privateRow 17 13, 18328295014877427543097374240⟩, ⟨.privateRow 18 0, 15822720660822479597433240⟩, ⟨.privateRow 18 1, 16877568704877311570595456⟩, ⟨.privateRow 18 2, 54249327979962787191199680⟩, ⟨.privateRow 18 3, 136318824154778285762501760⟩, ⟨.privateRow 18 4, 63290882643289918389732960⟩, ⟨.privateRow 18 5, 978131822669026011477691200⟩, ⟨.privateRow 18 7, 6610381076076947031816553600⟩, ⟨.privateRow 18 8, 10047427619622274544370107400⟩, ⟨.privateRow 18 11, 106860326254930698209225129664⟩, ⟨.privateRow 19 0, 379745295859739510338397760⟩, ⟨.privateRow 19 1, 325495967879776723147198080⟩, ⟨.privateRow 19 2, 963968827951646449320548160⟩, ⟨.privateRow 19 4, 6835415325475311186091159680⟩, ⟨.privateRow 19 5, 2278471775158437062030386560⟩, ⟨.privateRow 19 6, 29746714842346261643174491200⟩, ⟨.privateRow 19 10, 669187160364032965118324532672⟩, ⟨.privateRow 19 11, 350884653374399307552679530240⟩, ⟨.privateRow 20 0, 17007164321718333784441099680⟩, ⟨.privateRow 20 2, 21645481864005152089288672320⟩, ⟨.privateRow 20 3, 66904216670561379185074078080⟩, ⟨.privateRow 20 4, 71430090151217001894652618656⟩, ⟨.privateRow 20 5, 286201371312957010958372445120⟩, ⟨.privateRow 20 6, 267862838067063757104947319960⟩, ⟨.hall 17 9, 24420101047856791938136476⟩, ⟨.hall 18 9, 219652873429359816669263040⟩, ⟨.hall 19 9, 4173404595157836516715997760⟩, ⟨.hall 11 11, 5385595299197580731880⟩, ⟨.hall 13 11, 16182727367487113174742⟩, ⟨.hall 15 13, 490793732806035884695470⟩, ⟨.hall 19 13, 5133071413464078924031313721600⟩, ⟨.hall 16 15, 64057381222014882799297200⟩, ⟨.hall 8 17, 21358163978078194547280⟩, ⟨.hall 6 20, 144845052767318409666160⟩, ⟨.hall 7 20, 237892030549015897634580⟩, ⟨.hall 9 20, 604038367651987600392060⟩, ⟨.hall 5 26, 1117932093748307218616034800⟩, ⟨.hall 4 28, 167084849080550214248608293120⟩, ⟨.hall 3 29, 251315436799975607941951637568⟩]
  caps := #[0, 5090169617209056052364852160, 393188416437715854232717440, 0, 0, 0, 1982174296516532216138040, 5645333909386458154020296, 629565087258190909425600, 0, 1424338825155020810426160, 1639162295058614945775912, 0, 12707536931319862228143624, 0, 92419395822074666271084158, 4427702504246962778105268, 2792244822498084634841160, 498309892767162345588302584, 7675322128193120770529039880, 0] }

theorem case_53_33_21_checked :
    (Witness.linear .conditional case_53_33_21).check 53 33 21 = true := by
  change case_53_33_21.check 53 33 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_34_1_checked :
    (Witness.rising).check 53 34 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_34_2_checked :
    (Witness.rising).check 53 34 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_34_3_checked :
    (Witness.rising).check 53 34 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_34_4_checked :
    (Witness.rising).check 53 34 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_34_5_checked :
    (Witness.rising).check 53 34 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_34_6_checked :
    (Witness.rising).check 53 34 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_34_7_checked :
    (Witness.rising).check 53 34 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_34_8_checked :
    (Witness.rising).check 53 34 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_34_9_checked :
    (Witness.rising).check 53 34 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_34_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_34_10_checked :
    (Witness.linear .positive case_53_34_10).check 53 34 10 = true := by
  change case_53_34_10.check 53 34 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_34_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_34_11_checked :
    (Witness.linear .positive case_53_34_11).check 53 34 11 = true := by
  change case_53_34_11.check 53 34 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_34_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_34_12_checked :
    (Witness.linear .positive case_53_34_12).check 53 34 12 = true := by
  change case_53_34_12.check 53 34 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_34_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_34_13_checked :
    (Witness.linear .positive case_53_34_13).check 53 34 13 = true := by
  change case_53_34_13.check 53 34 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_34_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_53_34_14_checked :
    (Witness.linear .positive case_53_34_14).check 53 34 14 = true := by
  change case_53_34_14.check 53 34 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_34_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_53_34_15_checked :
    (Witness.linear .positive case_53_34_15).check 53 34 15 = true := by
  change case_53_34_15.check 53 34 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_34_16 : Certificate := {
  objectiveScale := 992572332132381000000
  eta := 228037606387910625032289763200
  rows := #[⟨.count 2, 31472788257133700285791382400⟩, ⟨.count 3, 4358544798606309891278899200⟩, ⟨.count 4, 600340963502302238209593600⟩, ⟨.count 5, 81115433652406444035544800⟩, ⟨.count 6, 10906276793600866424947200⟩, ⟨.count 7, 1768456595465874756842400⟩, ⟨.count 8, 422650003947819124276800⟩, ⟨.count 9, 127401675831160788657600⟩, ⟨.count 10, 36400478808903082473600⟩, ⟨.count 11, 22244737049885217067200⟩, ⟨.path 3, 29341496150356845184329600⟩, ⟨.path 7, 338909626557721870358400⟩, ⟨.privateRow 2 32, 2998813001695026112829232000⟩, ⟨.privateRow 4 29, 1724462066765464268787745200⟩, ⟨.privateRow 5 23, 8047510300732760528711040⟩, ⟨.privateRow 5 24, 21110255460341070996772800⟩, ⟨.privateRow 5 25, 42717903241117575447168192⟩, ⟨.privateRow 5 28, 986615261189296561277254800⟩, ⟨.privateRow 6 20, 706888310696352453468800⟩, ⟨.privateRow 6 21, 4677253885323856422535950⟩, ⟨.privateRow 6 22, 9978239983106420404750800⟩, ⟨.privateRow 7 18, 562474065404240488699200⟩, ⟨.privateRow 7 19, 2044926898800162454677600⟩, ⟨.privateRow 7 20, 4178634132076206088185900⟩, ⟨.privateRow 7 21, 6001993235439437853988800⟩, ⟨.privateRow 7 22, 6658326471967428722864400⟩, ⟨.privateRow 7 23, 11393436534993352678718880⟩, ⟨.privateRow 7 24, 18717754545136452025420200⟩, ⟨.privateRow 7 25, 29728502157382315094808000⟩, ⟨.privateRow 7 26, 45877386800704343927842800⟩, ⟨.privateRow 8 16, 305865134435921734674000⟩, ⟨.privateRow 8 17, 888955304356037987047980⟩, ⟨.privateRow 8 18, 1792555060603250408665200⟩, ⟨.privateRow 8 19, 2989831689111134956438350⟩, ⟨.privateRow 8 20, 4424319308243241923115600⟩, ⟨.privateRow 8 21, 6535318372447527730867800⟩, ⟨.privateRow 8 22, 9877219368575283508263480⟩, ⟨.privateRow 8 23, 15123640601790711953562600⟩, ⟨.privateRow 9 14, 149983454351498812044000⟩, ⟨.privateRow 9 15, 416215575875538276364800⟩, ⟨.privateRow 9 17, 3074716987784134447955200⟩, ⟨.privateRow 9 18, 1359456771071394288493200⟩, ⟨.privateRow 9 19, 3717182228842507636411200⟩, ⟨.privateRow 9 20, 4959902279183497793347200⟩, ⟨.privateRow 9 21, 7142987291600414884069440⟩, ⟨.privateRow 9 22, 10082932630066153845187200⟩, ⟨.privateRow 10 12, 73080961300951573273920⟩, ⟨.privateRow 10 13, 214307818987416898063320⟩, ⟨.privateRow 10 14, 264896211695699250182880⟩, ⟨.privateRow 10 15, 406775350689491946642480⟩, ⟨.privateRow 10 16, 2314868227363964361529440⟩, ⟨.privateRow 10 17, 1340447632137856012090320⟩, ⟨.privateRow 10 18, 2980159200768908080802880⟩, ⟨.privateRow 10 19, 3894547895229222298987920⟩, ⟨.privateRow 10 20, 5334854174232835767330816⟩, ⟨.privateRow 10 21, 7251885390703716605802960⟩, ⟨.privateRow 10 23, 13731170618688465286103760⟩, ⟨.privateRow 11 10, 37122710531301953157600⟩, ⟨.privateRow 11 11, 121957159770000071193600⟩, ⟨.privateRow 11 12, 219919559470456123278000⟩, ⟨.privateRow 11 13, 281460267961770804379200⟩, ⟨.privateRow 11 14, 408898711953344626453440⟩, ⟨.privateRow 11 15, 2385130139237692718872000⟩, ⟨.privateRow 11 17, 5183601518001174673204800⟩, ⟨.privateRow 11 18, 2128416885909471905748000⟩, ⟨.privateRow 11 19, 4390706643882798481482240⟩, ⟨.privateRow 11 21, 11121020359060797308323200⟩, ⟨.privateRow 12 8, 20205636153645738836040⟩, ⟨.privateRow 12 9, 77062124779959501982800⟩, ⟨.privateRow 12 10, 167691094683750097891200⟩, ⟨.privateRow 12 13, 1984230544849761362394240⟩, ⟨.privateRow 12 14, 1849711676634205480296200⟩, ⟨.privateRow 12 16, 5244196759510439923592400⟩, ⟨.privateRow 12 17, 259058500226788257095100⟩, ⟨.privateRow 12 18, 9938392395462467855198280⟩, ⟨.privateRow 12 22, 46419205038847976714979600⟩, ⟨.privateRow 13 6, 12214744005070900443150⟩, ⟨.privateRow 13 7, 54658496751146533365120⟩, ⟨.privateRow 13 8, 137894670998012952738000⟩, ⟨.privateRow 13 9, 218536207940630594044800⟩, ⟨.privateRow 13 10, 3972274473193788762000⟩, ⟨.privateRow 13 11, 4766729367832546514400⟩, ⟨.privateRow 13 12, 10010131672448347680240⟩, ⟨.privateRow 13 13, 7174986971780834181175200⟩, ⟨.privateRow 13 15, 4059210537378544253191200⟩, ⟨.privateRow 13 16, 3101551908669710265369600⟩, ⟨.privateRow 13 18, 12647324695201704039331800⟩, ⟨.privateRow 14 4, 8505340636720818290400⟩, ⟨.privateRow 14 5, 43893632928791365820100⟩, ⟨.privateRow 14 6, 128754656591121339738960⟩, ⟨.privateRow 14 7, 267050338154999570199600⟩, ⟨.privateRow 14 8, 396432992424740118447600⟩, ⟨.privateRow 14 9, 17213189383839751302000⟩, ⟨.privateRow 14 12, 10714636618460783860451600⟩, ⟨.privateRow 14 13, 3458560076948002030354350⟩, ⟨.privateRow 14 14, 4441002861030655835916000⟩, ⟨.privateRow 14 16, 13496517532081072200872160⟩, ⟨.privateRow 15 2, 6426257369966840486080⟩, ⟨.privateRow 15 3, 42526703183604091452000⟩, ⟨.privateRow 15 4, 139168636168344389276670⟩, ⟨.privateRow 15 5, 335450634712269073373376⟩, ⟨.privateRow 15 6, 640330645078838748434400⟩, ⟨.privateRow 15 7, 1029931325409685550211360⟩, ⟨.privateRow 15 8, 38557544219801042916480⟩, ⟨.privateRow 15 11, 19307690268065372240427360⟩, ⟨.privateRow 16 1, 66270779127783042512700⟩, ⟨.privateRow 16 2, 178612153371137184098400⟩, ⟨.privateRow 16 3, 501549305671630753562025⟩, ⟨.privateRow 16 4, 1091660470723117027572840⟩, ⟨.privateRow 16 6, 6456534928729184253754800⟩, ⟨.privateRow 16 11, 5245934629592462206175775⟩, ⟨.privateRow 16 13, 93622537058704407331578000⟩, ⟨.privateRow 17 0, 514100589597347238886400⟩, ⟨.privateRow 17 1, 884555426218965102201600⟩, ⟨.privateRow 17 2, 2349600350894126052723000⟩, ⟨.privateRow 17 3, 5475171279211748094140160⟩, ⟨.privateRow 17 5, 27983879208755603070537600⟩, ⟨.privateRow 17 9, 16901056883012790478390400⟩, ⟨.privateRow 17 11, 8510200831370373043708800⟩, ⟨.privateRow 17 12, 177075521829436289593934400⟩, ⟨.privateRow 18 13, 4760001129329850874994924400⟩, ⟨.hall 14 7, 126834027038819220120⟩, ⟨.hall 13 9, 156501640898762805360⟩, ⟨.hall 16 9, 30916615824947422009440⟩, ⟨.hall 12 12, 43322108997429622800⟩, ⟨.hall 13 12, 193044457812708318960⟩, ⟨.hall 10 16, 43813452693010946400⟩, ⟨.hall 17 16, 67090126942453814674675200⟩, ⟨.hall 8 20, 375930870889668586800⟩, ⟨.hall 9 20, 491163245964664404768⟩, ⟨.hall 4 28, 6209426582500890368299680⟩, ⟨.hall 5 28, 735423663357526762658239200⟩, ⟨.hall 3 29, 12279955938132119248851840⟩, ⟨.hall 2 30, 89143720707446671267801800⟩]
  caps := #[0, 71499619818040910354812800, 5653848450138288230476800, 113629040843070863510400, 0, 3059367894209101926528, 20477810617446214280050, 10452882236965089903960, 18621520488732422731470, 32670007508628096175520, 5427246968437276354680, 0, 29984804388590119466860, 2173067800041307969800, 992572332132381000000, 505255400835322243670564, 2487719167245283209338100, 0, 0, 0] }

theorem case_53_34_16_checked :
    (Witness.linear .positive case_53_34_16).check 53 34 16 = true := by
  change case_53_34_16.check 53 34 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_34_17 : Certificate := {
  objectiveScale := 942740417131907230636800000
  eta := 104193778788858158618334725280672000
  rows := #[⟨.count 2, 16288224635329528457098697580806400⟩, ⟨.count 3, 2569711692673187727003245633126400⟩, ⟨.count 4, 413917255644279548857829776843200⟩, ⟨.count 5, 66132286208501154739054115558400⟩, ⟨.count 6, 10206641111261020055389729569600⟩, ⟨.count 7, 1725979997199892774783005763200⟩, ⟨.count 8, 333083859108751237238825673600⟩, ⟨.count 9, 74324497487076722359076803200⟩, ⟨.count 10, 24774832495692240786358934400⟩, ⟨.path 8, 42232856005086993453182976000⟩, ⟨.path 9, 3362787167929564583688480000⟩, ⟨.privateRow 2 32, 1311623676468606235657906625241600⟩, ⟨.privateRow 3 28, 7282424374150424777812506772800⟩, ⟨.privateRow 3 29, 247733643574702738387567797964800⟩, ⟨.privateRow 3 30, 415295011606956656248226737584000⟩, ⟨.privateRow 4 26, 43842162955189381601560429287600⟩, ⟨.privateRow 4 27, 98054399808028776864769411293900⟩, ⟨.privateRow 4 28, 153324556417923808159890345297600⟩, ⟨.privateRow 4 29, 244969930720999255110402466002600⟩, ⟨.privateRow 5 23, 6101490691855761300329397566400⟩, ⟨.privateRow 5 24, 20403909732980018972069275732800⟩, ⟨.privateRow 5 25, 35435883360055202081009830253376⟩, ⟨.privateRow 5 26, 54529612779956086072782567605520⟩, ⟨.privateRow 5 27, 89580380544729639564190961689920⟩, ⟨.privateRow 5 28, 99670802785669597499574417020160⟩, ⟨.privateRow 6 20, 624832636134742580678893760000⟩, ⟨.privateRow 6 21, 3686903073592565440118397492600⟩, ⟨.privateRow 6 22, 7979335917953568020476858634400⟩, ⟨.privateRow 6 23, 13405003167475733640239817003600⟩, ⟨.privateRow 6 24, 19828438875099921055264014579840⟩, ⟨.privateRow 6 25, 32169898791794805980365769542200⟩, ⟨.privateRow 6 26, 37902347707933484943981695481600⟩, ⟨.privateRow 6 27, 33178612978754831034049258656000⟩, ⟨.privateRow 7 18, 537259938978011735909898034560⟩, ⟨.privateRow 7 19, 1666140256277757812248757860800⟩, ⟨.privateRow 7 20, 3245945464658820904455633958800⟩, ⟨.privateRow 7 21, 5294735630507941745198995123200⟩, ⟨.privateRow 7 22, 7710675050147390654262425496000⟩, ⟨.privateRow 7 23, 12231098852337586016789345352000⟩, ⟨.privateRow 7 24, 14584855408669394678640981970800⟩, ⟨.privateRow 7 25, 13505036469318459255319659129600⟩, ⟨.privateRow 7 26, 1784377816654024485207994680000⟩, ⟨.privateRow 8 15, 14824755092908435748318945700⟩, ⟨.privateRow 8 16, 291104281824383829239717479200⟩, ⟨.privateRow 8 17, 752845222462847966895482119080⟩, ⟨.privateRow 8 18, 1414765280355857527867941371200⟩, ⟨.privateRow 8 19, 2264402485361482132705993854900⟩, ⟨.privateRow 8 20, 3257841316769847734357020590000⟩, ⟨.privateRow 8 21, 5116748449301290312962339088200⟩, ⟨.privateRow 8 22, 6199901832046983256786323333600⟩, ⟨.privateRow 8 23, 1470489537088066541673679252200⟩, ⟨.privateRow 9 13, 11434538074934880362934892800⟩, ⟨.privateRow 9 14, 145437442613600746838440411200⟩, ⟨.privateRow 9 15, 365616467436427917059297001600⟩, ⟨.privateRow 9 16, 677729306715492186844618849920⟩, ⟨.privateRow 9 17, 1078775731016130040166518044800⟩, ⟨.privateRow 9 18, 1544641987127256512360628562800⟩, ⟨.privateRow 9 19, 2411810280890166868932370550400⟩, ⟨.privateRow 9 20, 704706346544134849034209689600⟩, ⟨.privateRow 10 11, 6370671213178004773635154560⟩, ⟨.privateRow 10 12, 73943346217912226346978973440⟩, ⟨.privateRow 10 13, 195101805903576396192576608400⟩, ⟨.privateRow 10 14, 366892746686206002190715492160⟩, ⟨.privateRow 10 15, 587163530147906106636706745280⟩, ⟨.privateRow 10 16, 846473443602818226867263592000⟩, ⟨.privateRow 10 17, 131925983039561182187361325680⟩, ⟨.privateRow 11 9, 3303310999425632104847857920⟩, ⟨.privateRow 11 10, 40111633564454104130295417600⟩, ⟨.privateRow 11 11, 115827635684988510343062710400⟩, ⟨.privateRow 11 12, 228249614196423885022473516000⟩, ⟨.privateRow 11 13, 283283943284076935052104179200⟩, ⟨.privateRow 12 7, 1655956685909984844227116275⟩, ⟨.privateRow 12 8, 23719608148653497197310313120⟩, ⟨.privateRow 12 9, 77052678446423784588527043000⟩, ⟨.privateRow 12 10, 89676423606202256179683835200⟩, ⟨.privateRow 13 5, 1145055283414347263235076800⟩, ⟨.privateRow 13 6, 15816076102160671573434498300⟩, ⟨.privateRow 13 7, 33740962351276099356660263040⟩, ⟨.privateRow 14 3, 781040795168428225848617200⟩, ⟨.privateRow 14 4, 10750796827612482638151554400⟩, ⟨.privateRow 15 2, 2186914226471599032376128160⟩, ⟨.hall 5 28, 16594154328795702312909206952000⟩, ⟨.hall 4 29, 70796974253565075475112396923680⟩, ⟨.hall 3 30, 191616013611037331991614171232000⟩, ⟨.hall 2 31, 435395486991013740854553825534600⟩, ⟨.assumptionRow 17, 1129530963066349906855615680⟩]
  caps := #[0, 87892547494215782381076797097600, 6699305070508769516153551852800, 876714515614229619757911624000, 759051945507213872600013427500, 59105395031885470059505084800, 0, 0, 9149802510704703024387427360, 11789392757389922057286615360, 33167473196763421190211272640, 10156990980137455312157819520, 73784484944723672822625332025, 1406820826005975528846366240, 11023074685064851348441387600, 20768104508447431917824007680, 108067929940679527719422533440, 13954315711044165783333184320, 942740417131907230636800000, 0] }

theorem case_53_34_17_checked :
    (Witness.linear .conditional case_53_34_17).check 53 34 17 = true := by
  change case_53_34_17.check 53 34 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_34_18 : Certificate := {
  objectiveScale := 1386449933184581496000000
  eta := 163949952847987274901317437852800
  rows := #[⟨.count 2, 24129086627725222719394671652800⟩, ⟨.count 3, 3581294119658476765130257070400⟩, ⟨.count 4, 525601127360200767585827317200⟩, ⟨.count 5, 73892259832556789481763105200⟩, ⟨.count 6, 10966342448648004092699824800⟩, ⟨.count 7, 1928148122839209510804364800⟩, ⟨.count 8, 482037030709802377701091200⟩, ⟨.count 9, 164330805923796265125372000⟩, ⟨.count 10, 65732322369518506050148800⟩, ⟨.path 7, 179278260946449000411398400⟩, ⟨.path 8, 25211647095848914359859200⟩, ⟨.privateRow 2 32, 2086216099159465540492180956000⟩, ⟨.privateRow 3 29, 364152196866216262887746563200⟩, ⟨.privateRow 3 30, 648580824820039099196818209600⟩, ⟨.privateRow 4 26, 52442616209784562429018090740⟩, ⟨.privateRow 4 27, 141632270999726231429377647975⟩, ⟨.privateRow 4 28, 238322120714368231800280121100⟩, ⟨.privateRow 4 29, 406635894546742508901628324950⟩, ⟨.privateRow 5 23, 5624913065497003459792971360⟩, ⟨.privateRow 5 24, 25518504809076149206187211360⟩, ⟨.privateRow 5 25, 50006521565834898662711201088⟩, ⟨.privateRow 5 26, 84480002363334802956976864620⟩, ⟨.privateRow 5 27, 150761098329746608645830448560⟩, ⟨.privateRow 5 28, 184913421955536107105952760080⟩, ⟨.privateRow 6 20, 178213426036229847311448400⟩, ⟨.privateRow 6 21, 3706735649096583016027364250⟩, ⟨.privateRow 6 22, 9818020389520868581535193000⟩, ⟨.privateRow 6 23, 18616050148796172480492984900⟩, ⟨.privateRow 6 24, 30578937208849094405426246160⟩, ⟨.privateRow 6 25, 54696497986857880957254100650⟩, ⟨.privateRow 6 26, 72493491663086380796469760200⟩, ⟨.privateRow 6 27, 73771033257869354062371015300⟩, ⟨.privateRow 7 18, 190232471047975581199894920⟩, ⟨.privateRow 7 19, 1638352050805340224210256400⟩, ⟨.privateRow 7 20, 3870283927373123108461663050⟩, ⟨.privateRow 7 21, 7219488283921555508885475600⟩, ⟨.privateRow 7 22, 11788387742090613504672221400⟩, ⟨.privateRow 7 23, 20877368112206333694218332080⟩, ⟨.privateRow 7 24, 28349802868620252338545426200⟩, ⟨.privateRow 7 25, 31303714315737761551898244000⟩, ⟨.privateRow 7 26, 21898253680816736586992428800⟩, ⟨.privateRow 8 16, 98598483554277759075223200⟩, ⟨.privateRow 8 17, 677864574435659593642159500⟩, ⟨.privateRow 8 18, 1616274627275807278009330100⟩, ⟨.privateRow 8 19, 2996412479959110092636730975⟩, ⟨.privateRow 8 20, 4884211520986673199057633900⟩, ⟨.privateRow 8 21, 8644028628822133262629463550⟩, ⟨.privateRow 8 22, 12010756015185909244385522400⟩, ⟨.privateRow 8 23, 13794544089765672730617945825⟩, ⟨.privateRow 8 24, 2816903898210407644690751700⟩, ⟨.privateRow 9 14, 39865436251883908761895800⟩, ⟨.privateRow 9 15, 285504026453464218197616000⟩, ⟨.privateRow 9 16, 720864468652386283016631840⟩, ⟨.privateRow 9 17, 1361714036247556211754934400⟩, ⟨.privateRow 9 18, 2227138894728338826518583300⟩, ⟨.privateRow 9 19, 3949677878250988962743464800⟩, ⟨.privateRow 9 20, 5668195539141905989305886800⟩, ⟨.privateRow 9 21, 3145656804950180061755454240⟩, ⟨.privateRow 10 12, 14410547596394441710994160⟩, ⟨.privateRow 10 13, 125165297178624821937158340⟩, ⟨.privateRow 10 14, 346588608857461213718966400⟩, ⟨.privateRow 10 15, 685588122314078018103051984⟩, ⟨.privateRow 10 16, 1144837947935780647040091600⟩, ⟨.privateRow 10 17, 2043453571662406556834000820⟩, ⟨.privateRow 10 18, 1783224002567366328417608160⟩, ⟨.privateRow 11 10, 4434323334451645249414800⟩, ⟨.privateRow 11 11, 57305101552913569377052800⟩, ⟨.privateRow 11 12, 180763886516175891637909200⟩, ⟨.privateRow 11 13, 385762417138285373890267200⟩, ⟨.privateRow 11 14, 673391124718845139758191040⟩, ⟨.privateRow 11 15, 777020971219925549913796000⟩, ⟨.privateRow 12 8, 1004243813978754953543940⟩, ⟨.privateRow 12 9, 27258046379423348739049800⟩, ⟨.privateRow 12 10, 102741867122441852939495400⟩, ⟨.privateRow 12 11, 243110689967356928337095475⟩, ⟨.privateRow 12 12, 293513078358336106876706100⟩, ⟨.privateRow 13 7, 13198632983720779389434640⟩, ⟨.privateRow 13 8, 63328844595803118498995400⟩, ⟨.privateRow 13 9, 124482090348135778856875200⟩, ⟨.privateRow 14 5, 6993840847352043426466725⟩, ⟨.privateRow 14 6, 42273882455105684711087760⟩, ⟨.privateRow 14 7, 6660800807001946120444500⟩, ⟨.privateRow 15 3, 3071804607464426916722640⟩, ⟨.privateRow 15 4, 9791377186292860797053415⟩, ⟨.hall 6 27, 3057307570413893269284025500⟩, ⟨.hall 5 28, 45603057883745599942138434000⟩, ⟨.hall 4 29, 143841858451432987015912701960⟩, ⟨.hall 3 30, 343544681870548994572227691200⟩, ⟨.hall 2 31, 720743274683017483271101878150⟩, ⟨.assumptionRow 18, 1340542538664285119200752⟩]
  caps := #[0, 124157976117794921595458088000, 1271484338161387424008114950, 923524815267251993000101710, 979544203126304352079693095, 122374024586518206958513200, 211685534060960949468535100, 2944704083735883567456864, 5725908509997899264119078, 62860894394607314723127040, 0, 17435053466960539956853824, 7823305613725131329010057, 76520266710011198071276752, 1340542538664285119200752, 7500855412365456685571874, 738243062981699040755898480, 143538861430336636116787968, 19456206459104437320799248, 1386449933184581496000000] }

theorem case_53_34_18_checked :
    (Witness.linear .conditional case_53_34_18).check 53 34 18 = true := by
  change case_53_34_18.check 53 34 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_34_19 : Certificate := {
  objectiveScale := 30085584017415696000000
  eta := 3895173767063263475297418912000
  rows := #[⟨.count 2, 543243819145321612281835872000⟩, ⟨.count 3, 74880165976476537629502950400⟩, ⟨.count 4, 9903944470859638905597091200⟩, ⟨.count 5, 1201164890058491675049532800⟩, ⟨.count 6, 142456213376209255261939200⟩, ⟨.count 7, 20920143223079680842662400⟩, ⟨.count 8, 5230035805769920210665600⟩, ⟨.count 9, 2377289002622691004848000⟩, ⟨.count 10, 950915601049076401939200⟩, ⟨.count 11, 581115089529991134518400⟩, ⟨.path 6, 4341291272882147243088000⟩, ⟨.path 7, 5273350378943239077408000⟩, ⟨.privateRow 2 32, 48802045218728655476855232000⟩, ⟨.privateRow 3 29, 8017838595275131013328537600⟩, ⟨.privateRow 3 30, 14897466435190852724513702400⟩, ⟨.privateRow 4 26, 1066883720745348973640693520⟩, ⟨.privateRow 4 27, 3046822734098839142725878600⟩, ⟨.privateRow 4 28, 5407130629304185008910082400⟩, ⟨.privateRow 4 29, 9714137754741905551285018800⟩, ⟨.privateRow 5 23, 103712440192831132050548160⟩, ⟨.privateRow 5 24, 499100379894325052400036480⟩, ⟨.privateRow 5 25, 1047959707854804812345101824⟩, ⟨.privateRow 5 26, 1887113141739693210235052160⟩, ⟨.privateRow 5 27, 3598961972477141094299354880⟩, ⟨.privateRow 5 28, 4754799885552293460856452480⟩, ⟨.privateRow 6 20, 2997815938051541566960000⟩, ⟨.privateRow 6 21, 63167729084668545242805900⟩, ⟨.privateRow 6 22, 184776809233102589211508800⟩, ⟨.privateRow 6 23, 378534218497768153660039200⟩, ⟨.privateRow 6 24, 671216984161616259925477920⟩, ⟨.privateRow 6 25, 1296945109279238428113904800⟩, ⟨.privateRow 6 26, 1881968889589996764906148800⟩, ⟨.privateRow 6 27, 2122948323770269933766228400⟩, ⟨.privateRow 7 18, 2291253781575393616101120⟩, ⟨.privateRow 7 19, 26274703690891742010724800⟩, ⟨.privateRow 7 20, 69391367922983048509366800⟩, ⟨.privateRow 7 21, 141886957778302325170982400⟩, ⟨.privateRow 7 22, 252515260511121504774477600⟩, ⟨.privateRow 7 23, 488883823177445398739836800⟩, ⟨.privateRow 7 24, 734104013903931479093485200⟩, ⟨.privateRow 7 25, 914218560492718195554840000⟩, ⟨.privateRow 7 26, 788739209374920824151331200⟩, ⟨.privateRow 8 16, 799033248103737809962800⟩, ⟨.privateRow 8 17, 10089610741964471073075720⟩, ⟨.privateRow 8 18, 27376977551190693448422400⟩, ⟨.privateRow 8 19, 56395403454230858382715350⟩, ⟨.privateRow 8 20, 101228173185090419950482000⟩, ⟨.privateRow 8 21, 197675982955118650925342400⟩, ⟨.privateRow 8 22, 306276707936781827447922720⟩, ⟨.privateRow 8 23, 398445193105547983827131700⟩, ⟨.privateRow 8 24, 370896705892516841606368800⟩, ⟨.privateRow 9 14, 127669224214922294704800⟩, ⟨.privateRow 9 15, 3798859800150603201686400⟩, ⟨.privateRow 9 16, 11400421483688371529915520⟩, ⟨.privateRow 9 17, 24236608127973064590166400⟩, ⟨.privateRow 9 18, 44059089515273873289849600⟩, ⟨.privateRow 9 19, 86971042749917114729740800⟩, ⟨.privateRow 9 20, 139793398128298018829524800⟩, ⟨.privateRow 9 21, 191186864455367083256553600⟩, ⟨.privateRow 9 22, 73603508953423649833432800⟩, ⟨.privateRow 10 13, 1335243989806411447722960⟩, ⟨.privateRow 10 14, 5000951592789915441107520⟩, ⟨.privateRow 10 15, 11377705166552199149202528⟩, ⟨.privateRow 10 16, 21268812276797675523373440⟩, ⟨.privateRow 10 17, 42541586701933055531754960⟩, ⟨.privateRow 10 18, 71060564415538837979199360⟩, ⟨.privateRow 10 19, 66659183633540255775937920⟩, ⟨.privateRow 11 11, 430756639791461959852800⟩, ⟨.privateRow 11 12, 2245217391365874837912000⟩, ⟨.privateRow 11 13, 5839966519574125781606400⟩, ⟨.privateRow 11 14, 11548341688296005636883840⟩, ⟨.privateRow 11 15, 23702451833556608092780800⟩, ⟨.privateRow 11 16, 36762132993334780066635600⟩, ⟨.privateRow 12 9, 134901717212319370513200⟩, ⟨.privateRow 12 10, 1005776116494215425128000⟩, ⟨.privateRow 12 11, 3202186274597555314169100⟩, ⟨.privateRow 12 12, 7065831202239664931076000⟩, ⟨.privateRow 12 13, 15276062916019641948652440⟩, ⟨.privateRow 12 14, 1920908212613026250213600⟩, ⟨.privateRow 13 7, 41508220680713652465600⟩, ⟨.privateRow 13 8, 462520173299380698902400⟩, ⟨.privateRow 13 9, 1829554650003763297137600⟩, ⟨.privateRow 13 10, 4763068323111891620427600⟩, ⟨.privateRow 13 11, 2637658750528985733950400⟩, ⟨.privateRow 14 5, 16862714651539921314150⟩, ⟨.privateRow 14 6, 215842747539710992821120⟩, ⟨.privateRow 14 7, 1098485411586029159893200⟩, ⟨.privateRow 14 8, 1743345268589973403555200⟩, ⟨.privateRow 15 4, 94431202048623559359240⟩, ⟨.privateRow 15 5, 705086308629722576548992⟩, ⟨.privateRow 15 6, 53960686884927748205280⟩, ⟨.privateRow 16 3, 177058503841169173798575⟩, ⟨.hall 6 27, 295030055543342463312368400⟩, ⟨.hall 5 28, 1476252750371171616245001600⟩, ⟨.hall 4 29, 3963088687576633539188584320⟩, ⟨.hall 3 30, 8715939025731794126561491200⟩, ⟨.hall 2 31, 17337568696127285498356464000⟩, ⟨.assumptionRow 19, 20939365905561208311360⟩]
  caps := #[0, 0, 34034841398475843657547200, 12455325429214341998860800, 2405147587514832927433920, 4525177939642958312463936, 407342691029209581694620, 0, 195924566643618538756030, 0, 494517629562178548342912, 0, 896915177695666517213980, 62383022820641568266760, 0, 2993497448068643238724848, 10958151513971969828111745, 13874773162712354834948160, 2814810249227814259329600, 400258810338258535688640] }

theorem case_53_34_19_checked :
    (Witness.linear .conditional case_53_34_19).check 53 34 19 = true := by
  change case_53_34_19.check 53 34 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_34_20 : Certificate := {
  objectiveScale := 5386437671452741904000000
  eta := 953019024157306147671985574419200
  rows := #[⟨.count 2, 134831702612910479272320188764800⟩, ⟨.count 3, 18667848088298516681230158902400⟩, ⟨.count 4, 2453327467797539201309703662400⟩, ⟨.count 5, 292435798630613442471995328000⟩, ⟨.count 6, 29094377924984500654101576000⟩, ⟨.count 7, 2048657380516660105229637600⟩, ⟨.count 8, 80339505118300396283515200⟩, ⟨.path 7, 1463049977582416842579945600⟩, ⟨.path 8, 36817008457430160652492800⟩, ⟨.privateRow 2 32, 12233216104858483041694575988800⟩, ⟨.privateRow 3 29, 1982296949288943977899454044800⟩, ⟨.privateRow 3 30, 3709756988342639098787597875200⟩, ⟨.privateRow 4 26, 271808630691489815726202800400⟩, ⟨.privateRow 4 27, 747082079314145278815175564500⟩, ⟨.privateRow 4 28, 1335021641427077260142242957200⟩, ⟨.privateRow 4 29, 2432569748162598336419950422600⟩, ⟨.privateRow 5 23, 31227965639483364035402358240⟩, ⟨.privateRow 5 24, 122962290567062699858462797440⟩, ⟨.privateRow 5 25, 254210262095326113920298795840⟩, ⟨.privateRow 5 26, 460142507077437562203926220120⟩, ⟨.privateRow 5 27, 894122454313100600358125715360⟩, ⟨.privateRow 5 28, 1211937502610585138016083495040⟩, ⟨.privateRow 6 20, 2826547826900203624800181600⟩, ⟨.privateRow 6 21, 17036996304149577786872942100⟩, ⟨.privateRow 6 22, 44957741126940335534552197200⟩, ⟨.privateRow 6 23, 90323123263269190171675597800⟩, ⟨.privateRow 6 24, 161130633026087238366138446160⟩, ⟨.privateRow 6 25, 318154482706609356832255631400⟩, ⟨.privateRow 6 26, 477259699423303443422089314000⟩, ⟨.privateRow 6 27, 561129838864749148192278280200⟩, ⟨.privateRow 7 17, 170591027101845646653957600⟩, ⟨.privateRow 7 18, 1838626959993103354945590720⟩, ⟨.privateRow 7 19, 6987624099932174943420976800⟩, ⟨.privateRow 7 20, 16699139992446725227502088000⟩, ⟨.privateRow 7 21, 33275311354610337603549816000⟩, ⟨.privateRow 7 22, 59497142076181322047677542400⟩, ⟨.privateRow 7 23, 118033653212590966499793624480⟩, ⟨.privateRow 7 24, 184077891102305782984604202000⟩, ⟨.privateRow 7 25, 241196409973377425442316240800⟩, ⟨.privateRow 7 26, 224930529454961534494771681200⟩, ⟨.privateRow 8 14, 2317485724566357585101400⟩, ⟨.privateRow 8 15, 125530476747344369192992500⟩, ⟨.privateRow 8 16, 861823782178131523768617600⟩, ⟨.privateRow 8 17, 2809874191512556360015944120⟩, ⟨.privateRow 8 18, 6556596278821293452249101600⟩, ⟨.privateRow 8 19, 13023786962536978303772971875⟩, ⟨.privateRow 8 20, 23388838427565202868038362600⟩, ⟨.privateRow 8 21, 46811151648929697567861523200⟩, ⟨.privateRow 8 22, 75569347001901310254181485000⟩, ⟨.privateRow 8 23, 103828767927263474646907956600⟩, ⟨.privateRow 8 24, 113077853454007807769047644000⟩, ⟨.privateRow 8 25, 24257509326656825902853870700⟩, ⟨.privateRow 9 12, 521685098170781794048800⟩, ⟨.privateRow 9 13, 65732322369518506050148800⟩, ⟨.privateRow 9 14, 388307608071785248703656800⟩, ⟨.privateRow 9 15, 1197125022547897640489073600⟩, ⟨.privateRow 9 16, 2784129031917828278479635840⟩, ⟨.privateRow 9 17, 5549106424231698078653302400⟩, ⟨.privateRow 9 18, 10003181336150198205437227800⟩, ⟨.privateRow 9 19, 20164172414497057903574217600⟩, ⟨.privateRow 9 20, 33758416597664013486829197600⟩, ⟨.privateRow 9 21, 48776304634732487867257082880⟩, ⟨.privateRow 9 22, 41057138911138697973434608800⟩, ⟨.privateRow 10 11, 33335677773112956639718320⟩, ⟨.privateRow 10 12, 184556135883648113140802400⟩, ⟨.privateRow 10 13, 562559125612462547612523480⟩, ⟨.privateRow 10 14, 1313451314256378875438427840⟩, ⟨.privateRow 10 15, 2636523450241387277671468368⟩, ⟨.privateRow 10 16, 4780200554538873578869154400⟩, ⟨.privateRow 10 17, 9669224620556172239976888480⟩, ⟨.privateRow 10 18, 16733571208925996825909308800⟩, ⟨.privateRow 10 19, 25510714311610132198062749280⟩, ⟨.privateRow 10 20, 2972415617549626843587728736⟩, ⟨.privateRow 11 9, 18015525390164331287818560⟩, ⟨.privateRow 11 10, 98076798456106977281174400⟩, ⟨.privateRow 11 11, 300570875792242741340424000⟩, ⟨.privateRow 11 12, 709056995930454255077994000⟩, ⟨.privateRow 11 13, 1437479575050581470692648000⟩, ⟨.privateRow 11 14, 2625641099093544769447610400⟩, ⟨.privateRow 11 15, 5318637540862028254971299200⟩, ⟨.privateRow 11 16, 9450847238461882980988060800⟩, ⟨.privateRow 11 17, 5002960091457797404927992000⟩, ⟨.privateRow 12 7, 11297742907260993227369325⟩, ⟨.privateRow 12 8, 59585132962739460576940440⟩, ⟨.privateRow 12 9, 187219739606039316339263100⟩, ⟨.privateRow 12 10, 450364725807395490704705400⟩, ⟨.privateRow 12 11, 924741178705436853055044750⟩, ⟨.privateRow 12 12, 1707214483763883421024698000⟩, ⟨.privateRow 12 13, 3460624182970789569912417240⟩, ⟨.privateRow 12 14, 2428038376908634198790681600⟩, ⟨.privateRow 13 5, 8101462701005081978169600⟩, ⟨.privateRow 13 6, 43039020599089498009026000⟩, ⟨.privateRow 13 7, 140020280349037833522697920⟩, ⟨.privateRow 13 8, 345541851095547112586751600⟩, ⟨.privateRow 13 9, 721731268507808505074436000⟩, ⟨.privateRow 13 10, 1351425246811410237483416400⟩, ⟨.privateRow 13 11, 636977504866524570533584800⟩, ⟨.privateRow 14 3, 6216747419868483045748200⟩, ⟨.privateRow 14 4, 37300484519210898274489200⟩, ⟨.privateRow 14 5, 128220415534787462818556625⟩, ⟨.privateRow 14 6, 325757564801108511597205680⟩, ⟨.privateRow 14 7, 583486150693370480150938200⟩, ⟨.privateRow 15 1, 5496913508094237640451040⟩, ⟨.privateRow 15 2, 40616083143140755898888240⟩, ⟨.privateRow 15 3, 147446621158292492002686720⟩, ⟨.privateRow 15 4, 150134450189823865554819030⟩, ⟨.privateRow 16 0, 82453702621413564606765600⟩, ⟨.privateRow 16 1, 21758615969539690660118700⟩, ⟨.hall 6 27, 99816096573408363782533099200⟩, ⟨.hall 5 28, 408455740168608664753218597600⟩, ⟨.hall 4 29, 1039452602096850102215190536400⟩, ⟨.hall 3 30, 2227835209705984389044143209600⟩, ⟨.hall 2 31, 4371066603504858917020585524300⟩, ⟨.assumptionRow 20, 1274965494057209297906640⟩]
  caps := #[0, 138408121828556523780189091200, 0, 702411542169231560978558400, 0, 328845746542667722768310680, 66774569613404573140744480, 0, 0, 13695184745953103738242240, 140603869479028933622276856, 1579281801323498677768440, 134409666675825250886079365, 0, 14358986397412950068901125, 108496609919856541172237140, 0, 8463362812702539378738787840, 2237436164057256670777709440, 466929873513945841189307040] }

theorem case_53_34_20_checked :
    (Witness.linear .conditional case_53_34_20).check 53 34 20 = true := by
  change case_53_34_20.check 53 34 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_34_21 : Certificate := {
  objectiveScale := 106629480434880809120000000
  eta := 30658211388383859601026353391744000
  rows := #[⟨.count 2, 3275815396294850642322589596096000⟩, ⟨.count 3, 382525472309736536849297829600000⟩, ⟨.count 4, 48313491160216039311651040944000⟩, ⟨.count 5, 5973685457987666465865746928000⟩, ⟨.count 6, 636294816953573495737579560000⟩, ⟨.count 7, 52400749631470758472506552000⟩, ⟨.count 8, 2687217929819013255000336000⟩, ⟨.path 3, 30614282633490057008342900064000⟩, ⟨.path 7, 20203919478258309764286624000⟩, ⟨.path 8, 2223665203932109398517056000⟩, ⟨.privateRow 2 32, 327819089694481065004000989312000⟩, ⟨.privateRow 3 31, 559081064734705345729329905472000⟩, ⟨.privateRow 4 26, 5051432264473781116749631612800⟩, ⟨.privateRow 5 23, 421701270843740865802552728000⟩, ⟨.privateRow 5 24, 2347553583489889979568293529600⟩, ⟨.privateRow 6 20, 22180211484220426866669440000⟩, ⟨.privateRow 6 21, 262939475829344341620970377000⟩, ⟨.privateRow 6 22, 833064978835014711226175592000⟩, ⟨.privateRow 6 23, 1467013050198516670728308430000⟩, ⟨.privateRow 6 24, 2484544114669306391003560658400⟩, ⟨.privateRow 6 28, 145785123659231587065569478444000⟩, ⟨.privateRow 7 18, 20557217163115451400752570400⟩, ⟨.privateRow 7 19, 107360754434197720045013424000⟩, ⟨.privateRow 7 20, 295402028142247242817536936000⟩, ⟨.privateRow 7 21, 620911865334915674961506208000⟩, ⟨.privateRow 7 23, 4645124913485146312593580809600⟩, ⟨.privateRow 7 25, 5408026083760764175688176200000⟩, ⟨.privateRow 8 15, 615820775583523870937577000⟩, ⟨.privateRow 8 16, 9954920967284071831023972000⟩, ⟨.privateRow 8 17, 41450336567458279458380182800⟩, ⟨.privateRow 8 18, 109653420525114735322097044000⟩, ⟨.privateRow 8 19, 237524872327908718492764074250⟩, ⟨.privateRow 8 20, 458218643068602813785682294000⟩, ⟨.privateRow 8 21, 403082689472851988250050400000⟩, ⟨.privateRow 8 22, 2649462517905056118767581279200⟩, ⟨.privateRow 8 24, 5519545627848253225770690144000⟩, ⟨.privateRow 9 12, 17449467076746839318184000⟩, ⟨.privateRow 9 13, 375834675499162693007040000⟩, ⟨.privateRow 9 14, 4315834856982051591364176000⟩, ⟨.privateRow 9 15, 16389808530631667621407008000⟩, ⟨.privateRow 9 16, 42775623591937201904596257600⟩, ⟨.privateRow 9 17, 92776877617387750561526752000⟩, ⟨.privateRow 9 18, 180165747567411115960249800000⟩, ⟨.privateRow 9 20, 1205583680332439128493332560000⟩, ⟨.privateRow 9 21, 1146513744384235728033416083200⟩, ⟨.privateRow 9 23, 3544603311123994787179079568000⟩, ⟨.privateRow 10 11, 204158764797938020022752800⟩, ⟨.privateRow 10 12, 1928031885310704615126115200⟩, ⟨.privateRow 10 13, 7127234827497246519512254800⟩, ⟨.privateRow 10 14, 18608428953680588482353566400⟩, ⟨.privateRow 10 15, 40520803456279975327900521120⟩, ⟨.privateRow 10 16, 78979777882771544121964420800⟩, ⟨.privateRow 10 17, 174324102226793192827504751400⟩, ⟨.privateRow 10 18, 55688229228729863000052417600⟩, ⟨.privateRow 10 19, 809023601652875108780419339200⟩, ⟨.privateRow 10 20, 911553180302424187246204886400⟩, ⟨.privateRow 10 23, 1158239786259809604055235731200⟩, ⟨.privateRow 11 9, 114003184901412683545468800⟩, ⟨.privateRow 11 10, 959720689221076162500120000⟩, ⟨.privateRow 11 11, 3551637683467087448916528000⟩, ⟨.privateRow 11 12, 9425620465956084371705724000⟩, ⟨.privateRow 11 13, 20898116297187532834341456000⟩, ⟨.privateRow 11 14, 41578590150472368727368835200⟩, ⟨.privateRow 11 15, 92478297847407860199860048000⟩, ⟨.privateRow 11 16, 183524769979684882529000220000⟩, ⟨.privateRow 11 17, 116318147533594430895014544000⟩, ⟨.privateRow 11 18, 640820045415476509400761944000⟩, ⟨.privateRow 11 20, 1871647288118942732107734024000⟩, ⟨.privateRow 12 7, 62981670230133123164070375⟩, ⟨.privateRow 12 8, 559837068712294428125070000⟩, ⟨.privateRow 12 9, 2063399481825313749375258000⟩, ⟨.privateRow 12 10, 5581144931162565991154544000⟩, ⟨.privateRow 12 11, 12512358485719780468595314500⟩, ⟨.privateRow 12 12, 24978912120363100483980396000⟩, ⟨.privateRow 12 13, 55625411147253574378506955200⟩, ⟨.privateRow 12 14, 111631511501231508968138958000⟩, ⟨.privateRow 12 15, 208427340681587215590963561000⟩, ⟨.privateRow 12 16, 166703483717700929426270844000⟩, ⟨.privateRow 12 17, 543265891478410513052567928000⟩, ⟨.privateRow 12 18, 320383557682671855327415059600⟩, ⟨.privateRow 12 22, 4698936452529772053024962538000⟩, ⟨.privateRow 13 5, 67744989827370082058832000⟩, ⟨.privateRow 13 6, 359895258457903560937545000⟩, ⟨.privateRow 13 7, 1420386620047192720500177600⟩, ⟨.privateRow 13 8, 3948565121366713354286208000⟩, ⟨.privateRow 13 9, 9036139412358440176154976000⟩, ⟨.privateRow 13 10, 18282679129661500895627286000⟩, ⟨.privateRow 13 12, 162787823305678938683270354400⟩, ⟨.privateRow 13 13, 115614352361498975042514456000⟩, ⟨.privateRow 13 14, 276615495650744676936597087000⟩, ⟨.privateRow 13 15, 262579580570886438060032832000⟩, ⟨.privateRow 13 16, 560956742849719016981320140000⟩, ⟨.privateRow 13 17, 479668400472693866017559976000⟩, ⟨.privateRow 14 3, 69313160888188833958342000⟩, ⟨.privateRow 14 4, 293561622585270355588272000⟩, ⟨.privateRow 14 5, 1247636895987399011250156000⟩, ⟨.privateRow 14 6, 3410207515698890630750426400⟩, ⟨.privateRow 14 7, 8020522902776136500893860000⟩, ⟨.privateRow 14 8, 16507195854602509995002064000⟩, ⟨.privateRow 14 9, 36389409466299137828129550000⟩, ⟨.privateRow 14 11, 271485788566858024848033945600⟩, ⟨.privateRow 14 12, 227763046678588508387111812000⟩, ⟨.privateRow 14 13, 425600136143701487712709465500⟩, ⟨.privateRow 14 14, 485865454065949957809703608000⟩, ⟨.privateRow 14 16, 1958041344562624008255994826400⟩, ⟨.privateRow 15 2, 388153700973857470166715200⟩, ⟨.privateRow 15 3, 1232958814858135493470742400⟩, ⟨.privateRow 15 4, 3711719765562512058469214100⟩, ⟨.privateRow 15 5, 9082796602788264801901135680⟩, ⟨.privateRow 15 6, 19463135577403424575502433600⟩, ⟨.privateRow 15 7, 43264208670086113405505409600⟩, ⟨.privateRow 15 8, 88499043822039503198011065600⟩, ⟨.privateRow 15 9, 9209828723106981792137515200⟩, ⟨.privateRow 15 10, 546365149490801775006668315520⟩, ⟨.privateRow 15 11, 577960860750073773078238932800⟩, ⟨.privateRow 15 12, 869415770968819000989671208600⟩, ⟨.privateRow 15 13, 1112393056462364958430639089600⟩, ⟨.privateRow 15 16, 6327390518000094085555166154000⟩, ⟨.privateRow 16 1, 2911152757303931026250364000⟩, ⟨.privateRow 16 2, 4623595555718008100515284000⟩, ⟨.privateRow 16 3, 13918949120859420219259552875⟩, ⟨.privateRow 16 4, 29693758124500096467753712800⟩, ⟨.privateRow 16 5, 68308120055310095865946041000⟩, ⟨.privateRow 16 6, 141078941315498195887517640000⟩, ⟨.privateRow 16 7, 276195617849210456115503284500⟩, ⟨.privateRow 16 8, 70264641551290335224497422000⟩, ⟨.privateRow 16 9, 1372899640344533871979671662400⟩, ⟨.privateRow 16 10, 1845670848130692270642730776000⟩, ⟨.privateRow 16 15, 2338383452304382596835604883000⟩, ⟨.privateRow 16 18, 116919172615219129841780244150000⟩, ⟨.privateRow 17 1, 61647940742906774673537120000⟩, ⟨.privateRow 17 2, 43667291359558965393755460000⟩, ⟨.privateRow 17 3, 149051021173961268544018636800⟩, ⟨.privateRow 17 4, 319395045372774146880039936000⟩, ⟨.privateRow 17 5, 634183431437287128180079296000⟩, ⟨.privateRow 17 6, 1199394936009219582815149968000⟩, ⟨.privateRow 17 7, 533534905338611358992793984000⟩, ⟨.privateRow 17 8, 4667160100509662221284583564800⟩, ⟨.privateRow 17 10, 13388391530840778789725424036000⟩, ⟨.privateRow 18 0, 524007496314707584725065520000⟩, ⟨.privateRow 18 1, 296937581245000964677537128000⟩, ⟨.privateRow 18 8, 10689752924820034728391336608000⟩, ⟨.privateRow 18 11, 246953088402092468956818378120000⟩, ⟨.privateRow 19 6, 111173430418128361175269900723200⟩, ⟨.privateRow 19 8, 85518023398560277827130692864000⟩, ⟨.privateRow 19 12, 5644189544304978336590625729024000⟩, ⟨.hall 13 6, 6759642625318725293151000⟩, ⟨.hall 9 12, 1457482650916743606499344⟩, ⟨.hall 16 12, 3319504501541134020882768000⟩, ⟨.hall 8 13, 774808952026716904817520⟩, ⟨.hall 17 16, 5519545627848253225770690144000⟩, ⟨.hall 7 17, 2263417270244893858775680⟩, ⟨.hall 16 17, 1339130268359808272075167440000⟩, ⟨.hall 6 20, 16376788484710107287633800⟩, ⟨.hall 6 27, 781466281493821566403758426000⟩, ⟨.hall 4 29, 137118788252323916053623644836800⟩, ⟨.hall 3 30, 207689525990953198451610807456000⟩]
  caps := #[0, 1279916979674234669730255744000, 0, 0, 0, 17105020771234428179446622400, 0, 2094195290709061720665936000, 6197997717901737108284530750, 0, 710636258034006087709704240, 349534343514833549421802600, 220641668257198392261057000, 3433167327965905456449743000, 19036287304204829023915678700, 73897228846109610212770670600, 0, 0, 18765730792093108387493529600000, 0] }

theorem case_53_34_21_checked :
    (Witness.linear .conditional case_53_34_21).check 53 34 21 = true := by
  change case_53_34_21.check 53 34 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_34_22 : Certificate := {
  objectiveScale := 1385123495065939200000
  eta := 385991478100142082417868819200
  rows := #[⟨.count 2, 35041867337839583823355353600⟩, ⟨.count 3, 3393835042226887797508569600⟩, ⟨.count 4, 374779329816466137148185600⟩, ⟨.count 5, 42509692502330649815419200⟩, ⟨.count 6, 3965918834036678699980800⟩, ⟨.count 7, 200202633448966953604800⟩, ⟨.path 3, 536756790580659198777427200⟩, ⟨.path 7, 230773103773540623187200⟩, ⟨.privateRow 2 32, 3913205162867607845593555200⟩, ⟨.privateRow 3 31, 6431398375862813958468864000⟩, ⟨.privateRow 5 23, 2321714984092305655613760⟩, ⟨.privateRow 5 24, 12964974243908100680666400⟩, ⟨.privateRow 5 28, 1047762706628873540212427520⟩, ⟨.privateRow 6 20, 36721470685524802777600⟩, ⟨.privateRow 6 21, 1536277152507697803703500⟩, ⟨.privateRow 6 22, 5355760925428996905108000⟩, ⟨.privateRow 6 23, 11326278614566556356716000⟩, ⟨.privateRow 7 18, 63874173528956123292960⟩, ⟨.privateRow 7 19, 596370807575494152801600⟩, ⟨.privateRow 7 20, 1886433147319730283073800⟩, ⟨.privateRow 7 21, 4585593651854909746852800⟩, ⟨.privateRow 7 22, 10092754981490778486489600⟩, ⟨.privateRow 8 15, 1390296065617826066700⟩, ⟨.privateRow 8 16, 31850418957790197164400⟩, ⟨.privateRow 8 17, 210212765121415301285040⟩, ⟨.privateRow 8 18, 656219742971613903482400⟩, ⟨.privateRow 8 19, 1625256100707238671972300⟩, ⟨.privateRow 8 20, 3598086217818933860619600⟩, ⟨.privateRow 8 21, 9113854142146722475907400⟩, ⟨.privateRow 8 22, 8643192580732901091460560⟩, ⟨.privateRow 8 23, 16031503932639152375117700⟩, ⟨.privateRow 8 24, 24867762293684182246374000⟩, ⟨.privateRow 8 25, 27438883151033415252391200⟩, ⟨.privateRow 9 13, 933345610484694422400⟩, ⟨.privateRow 9 14, 13481658818112252768000⟩, ⟨.privateRow 9 15, 75742410450848838278400⟩, ⟨.privateRow 9 16, 239838710374216976742720⟩, ⟨.privateRow 9 17, 604877092305969740857600⟩, ⟨.privateRow 9 18, 1369062452979299268590400⟩, ⟨.privateRow 9 19, 3567246923272502082412800⟩, ⟨.privateRow 9 20, 7987882849731509765040000⟩, ⟨.privateRow 9 21, 11212965272200322872200960⟩, ⟨.privateRow 9 22, 20031385713421637969013600⟩, ⟨.privateRow 10 11, 520006840127186892480⟩, ⟨.privateRow 10 12, 5600073662908166534400⟩, ⟨.privateRow 10 13, 29423720370529991666160⟩, ⟨.privateRow 10 14, 94641244903148014431360⟩, ⟨.privateRow 10 15, 242063184079205498449440⟩, ⟨.privateRow 10 16, 549647230014436545351360⟩, ⟨.privateRow 10 17, 1448284050609231393918360⟩, ⟨.privateRow 10 18, 3354044118820355456496000⟩, ⟨.privateRow 10 19, 6986465232722131629432960⟩, ⟨.privateRow 10 20, 10692276645327191445795264⟩, ⟨.privateRow 10 21, 17165555794308471117487920⟩, ⟨.privateRow 10 22, 15868182062094483752991360⟩, ⟨.privateRow 11 9, 269633176362245055360⟩, ⟨.privateRow 11 10, 2600034200635934462400⟩, ⟨.privateRow 11 11, 13066838546785721913600⟩, ⟨.privateRow 11 12, 42467225277053596219200⟩, ⟨.privateRow 11 13, 108833754822578913254400⟩, ⟨.privateRow 11 14, 247118806135997593237440⟩, ⟨.privateRow 11 16, 2834687287243327547631600⟩, ⟨.privateRow 11 17, 2682079724300446172102400⟩, ⟨.privateRow 11 18, 6491418720921049707792000⟩, ⟨.privateRow 11 19, 10105581816880582429837440⟩, ⟨.privateRow 11 20, 14969696910161392667268000⟩, ⟨.privateRow 11 22, 36000073542005148566390400⟩, ⟨.privateRow 12 8, 1482982469992347804480⟩, ⟨.privateRow 12 9, 7150094051748819771600⟩, ⟨.privateRow 12 10, 22244737049885217067200⟩, ⟨.privateRow 12 11, 57465570712203477423600⟩, ⟨.privateRow 12 12, 130435049065236045530400⟩, ⟨.privateRow 12 13, 335895529453266777714720⟩, ⟨.privateRow 12 14, 74149123499617390224000⟩, ⟨.privateRow 12 15, 3007905537964166695305450⟩, ⟨.privateRow 12 16, 3402650313737799453529200⟩, ⟨.privateRow 12 18, 23340290349592064007759600⟩, ⟨.privateRow 12 22, 104383428606586381087836000⟩, ⟨.privateRow 13 6, 1191682341958136628600⟩, ⟨.privateRow 13 7, 4448947409977043413440⟩, ⟨.privateRow 13 8, 14300188103497639543200⟩, ⟨.privateRow 13 9, 37400491962993826497600⟩, ⟨.privateRow 13 10, 83417763937069564002000⟩, ⟨.privateRow 13 11, 211469448318389336275200⟩, ⟨.privateRow 13 12, 501459929495983893314880⟩, ⟨.privateRow 13 13, 198084087063263599598400⟩, ⟨.privateRow 13 14, 3571471978848535475914200⟩, ⟨.privateRow 13 15, 4889302408719669139056000⟩, ⟨.privateRow 13 16, 2227651524567076737729600⟩, ⟨.privateRow 13 17, 16954303015506801442417920⟩, ⟨.privateRow 13 19, 25699026931774535774635200⟩, ⟨.privateRow 14 4, 1215048662388688327200⟩, ⟨.privateRow 14 5, 3872967611363944042950⟩, ⟨.privateRow 14 6, 11016441205657440833280⟩, ⟨.privateRow 14 7, 29508324658011002232000⟩, ⟨.privateRow 14 8, 68323120938933166706400⟩, ⟨.privateRow 14 9, 168689255961629562759600⟩, ⟨.privateRow 14 10, 394338520429783393464000⟩, ⟨.privateRow 14 11, 888200572206131167183200⟩, ⟨.privateRow 14 12, 502625130008120738018400⟩, ⟨.privateRow 14 13, 4928996780062512785327700⟩, ⟨.privateRow 14 14, 8185609260132252019156800⟩, ⟨.privateRow 14 15, 6399863812911619534083600⟩, ⟨.privateRow 14 16, 16355284024949178097108320⟩, ⟨.privateRow 14 19, 89377764556649524660504800⟩, ⟨.privateRow 15 3, 3402136254688327316160⟩, ⟨.privateRow 15 4, 10844309311819043320260⟩, ⟨.privateRow 15 5, 30846035375840834333184⟩, ⟨.privateRow 15 6, 70229812686066185312160⟩, ⟨.privateRow 15 8, 761511498341070597600480⟩, ⟨.privateRow 15 9, 730840724529865222553280⟩, ⟨.privateRow 15 10, 1949083860310942719428064⟩, ⟨.privateRow 15 11, 1458760422982472790340160⟩, ⟨.privateRow 15 12, 8328429551477025269959680⟩, ⟨.privateRow 15 13, 16425513837635244282420480⟩, ⟨.privateRow 15 14, 17505125075789673484081920⟩, ⟨.privateRow 15 19, 486750438230768365777643520⟩, ⟨.privateRow 16 1, 12049232568687825911400⟩, ⟨.privateRow 16 2, 12758010955081227435600⟩, ⟨.privateRow 16 3, 40666159919321412450975⟩, ⟨.privateRow 16 4, 101213553576977737655760⟩, ⟨.privateRow 16 5, 247869927127292418748800⟩, ⟨.privateRow 16 7, 2295378804335030836121700⟩, ⟨.privateRow 16 8, 2385748048600189530457200⟩, ⟨.privateRow 16 9, 5400466037285883573489480⟩, ⟨.privateRow 16 10, 5205268469673140793724800⟩, ⟨.privateRow 16 11, 18381104283533278427840700⟩, ⟨.privateRow 16 12, 40867554235112337541208400⟩, ⟨.privateRow 16 13, 53860069582034581823958000⟩, ⟨.privateRow 17 0, 64262573699668404860800⟩, ⟨.privateRow 17 1, 68042725093766546323200⟩, ⟨.privateRow 17 2, 216886186236380866405200⟩, ⟨.privateRow 17 3, 462690530637612514997760⟩, ⟨.privateRow 17 4, 1156726326594031287494400⟩, ⟨.privateRow 17 6, 8964629031103742478081600⟩, ⟨.privateRow 17 7, 10831164694471383873811200⟩, ⟨.privateRow 17 8, 20936746511351966303648640⟩, ⟨.privateRow 17 9, 24291252858474657037382400⟩, ⟨.privateRow 17 10, 59137633447119849573151200⟩, ⟨.privateRow 17 11, 138311419337029169661830400⟩, ⟨.privateRow 17 13, 480041425536522984310176000⟩, ⟨.privateRow 18 1, 4301576027021553850369800⟩, ⟨.privateRow 18 2, 1966434755209853188740480⟩, ⟨.privateRow 18 3, 8427577522327942237459200⟩, ⟨.privateRow 18 4, 1512642119392194760569600⟩, ⟨.privateRow 18 9, 186811301744936052930345600⟩, ⟨.privateRow 18 11, 3927953423531681744509108800⟩, ⟨.privateRow 18 13, 1858280843673311263359753600⟩, ⟨.privateRow 19 7, 1769791279688867869866432000⟩, ⟨.privateRow 19 9, 1668660349420932563016921600⟩, ⟨.privateRow 19 10, 23567720541190090467054652800⟩, ⟨.privateRow 19 11, 43218303050002153382138269440⟩, ⟨.hall 16 4, 13986560158163123410880⟩, ⟨.hall 15 7, 344345774766025032000⟩, ⟨.hall 15 11, 3721803915596120554200⟩, ⟨.hall 18 13, 184879981896069232834261200⟩, ⟨.hall 16 16, 3549562159058154833193600⟩, ⟨.hall 17 16, 67090126942453814674675200⟩, ⟨.hall 7 17, 31480144007838714496⟩, ⟨.hall 9 21, 3411285978494435120352⟩, ⟨.hall 4 26, 192328702715436154547680⟩, ⟨.hall 5 28, 1119511648569471591245011200⟩, ⟨.hall 3 30, 2587634106343318765327795200⟩]
  caps := #[0, 57156899984042959977465600, 2671682653288837673971200, 1714453952195067714892800, 0, 26167078723683258804520, 1005362053150725388800, 30570470324573669582400, 18291081409133649231720, 533340348848396812800, 1146096561764237662320, 57320282605809485488800, 8216277545806409876280, 5743441561829607515880, 0, 912301277777673805865272, 186165231598768033405365, 10872942059238622462802560, 89076912729534622742009160, 0] }

theorem case_53_34_22_checked :
    (Witness.linear .conditional case_53_34_22).check 53 34 22 = true := by
  change case_53_34_22.check 53 34 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_35_1_checked :
    (Witness.rising).check 53 35 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_35_2_checked :
    (Witness.rising).check 53 35 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_35_3_checked :
    (Witness.rising).check 53 35 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_35_4_checked :
    (Witness.rising).check 53 35 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_35_5_checked :
    (Witness.rising).check 53 35 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_35_6_checked :
    (Witness.rising).check 53 35 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_35_7_checked :
    (Witness.rising).check 53 35 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_35_8_checked :
    (Witness.rising).check 53 35 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_35_9_checked :
    (Witness.rising).check 53 35 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_35_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_35_10_checked :
    (Witness.linear .positive case_53_35_10).check 53 35 10 = true := by
  change case_53_35_10.check 53 35 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_35_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_35_11_checked :
    (Witness.linear .positive case_53_35_11).check 53 35 11 = true := by
  change case_53_35_11.check 53 35 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_35_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_35_12_checked :
    (Witness.linear .positive case_53_35_12).check 53 35 12 = true := by
  change case_53_35_12.check 53 35 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_35_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_53_35_13_checked :
    (Witness.linear .positive case_53_35_13).check 53 35 13 = true := by
  change case_53_35_13.check 53 35 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_35_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_53_35_14_checked :
    (Witness.linear .positive case_53_35_14).check 53 35 14 = true := by
  change case_53_35_14.check 53 35 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_35_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_53_35_15_checked :
    (Witness.linear .positive case_53_35_15).check 53 35 15 = true := by
  change case_53_35_15.check 53 35 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_35_16 : Certificate := {
  objectiveScale := 69
  eta := 513158175
  rows := #[⟨.assumptionRow 16, 304⟩]
  caps := #[0, 0, 143825440, 40681204, 11630584, 3367598, 990080, 296582, 90948, 28743, 9456, 3290, 1244, 539, 19824, 5954, 938, 69, 0] }

theorem case_53_35_16_checked :
    (Witness.linear .conditional case_53_35_16).check 53 35 16 = true := by
  change case_53_35_16.check 53 35 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_35_17 : Certificate := {
  objectiveScale := 8323199418330720000000
  eta := 2153125990073890395566402400000
  rows := #[⟨.count 2, 320916222617909667882797664000⟩, ⟨.count 3, 47888491848195148453114812000⟩, ⟨.count 4, 7101385111278186172801156800⟩, ⟨.count 5, 1032577083040361809522572000⟩, ⟨.count 6, 152618876322024194946864000⟩, ⟨.count 7, 21836977586956292044284000⟩, ⟨.count 8, 3664947287321335727712000⟩, ⟨.count 9, 1099484186196400718313600⟩, ⟨.count 10, 610824547886889287952000⟩, ⟨.path 8, 845323597852577017574400⟩, ⟨.privateRow 4 26, 126654470004346493856847200⟩, ⟨.privateRow 4 27, 889201727340860212043244480⟩, ⟨.privateRow 4 28, 1609385248158678723663730800⟩, ⟨.privateRow 4 29, 2627716302963740475995508000⟩, ⟨.privateRow 4 31, 11230757572971620998375261200⟩, ⟨.privateRow 5 23, 16767679218555724248289500⟩, ⟨.privateRow 5 24, 178974085692278507856825600⟩, ⟨.privateRow 5 25, 416254387050409700253661200⟩, ⟨.privateRow 5 26, 671954996032912186619824800⟩, ⟨.privateRow 5 27, 987967257398436812917820400⟩, ⟨.privateRow 5 28, 1564567451301639857610938400⟩, ⟨.privateRow 5 29, 862560614684773535749218000⟩, ⟨.privateRow 6 21, 29142633092238372654948000⟩, ⟨.privateRow 6 22, 90797432906204252772043500⟩, ⟨.privateRow 6 23, 167805345821273233213140000⟩, ⟨.privateRow 6 24, 263803487479054399860984000⟩, ⟨.privateRow 6 25, 376699861714329530232055200⟩, ⟨.privateRow 6 26, 603096526597998911871393000⟩, ⟨.privateRow 6 27, 717500692142849595740760000⟩, ⟨.privateRow 6 29, 1871500969238155183004076000⟩, ⟨.privateRow 7 18, 2454205772759823031950000⟩, ⟨.privateRow 7 19, 17565568784232973380676800⟩, ⟨.privateRow 7 20, 40794353733874391731080000⟩, ⟨.privateRow 7 21, 70730210370938099780799000⟩, ⟨.privateRow 7 22, 107847930123335156626872000⟩, ⟨.privateRow 7 23, 150839122654222812170361000⟩, ⟨.privateRow 7 24, 236487268263136547358702000⟩, ⟨.privateRow 7 25, 283580750147094484871787000⟩, ⟨.privateRow 7 26, 280321201294829031022686000⟩, ⟨.privateRow 8 16, 2176062451847043088329000⟩, ⟨.privateRow 8 17, 9155427030259170122826000⟩, ⟨.privateRow 8 18, 19286785099528529267084400⟩, ⟨.privateRow 8 19, 32509439826424440992112000⟩, ⟨.privateRow 8 20, 48570095690568431037308250⟩, ⟨.privateRow 8 21, 66787119762703984109466000⟩, ⟨.privateRow 8 23, 331631917661489366661339600⟩, ⟨.privateRow 9 14, 1437787012718370170102400⟩, ⟨.privateRow 9 15, 4937498428752355077612000⟩, ⟨.privateRow 9 16, 10139687494922362180003200⟩, ⟨.privateRow 9 17, 16889298749072488811872800⟩, ⟨.privateRow 9 18, 25016658705678599059900800⟩, ⟨.privateRow 9 19, 34122186306331352848218600⟩, ⟨.privateRow 9 20, 51928812635355402180033600⟩, ⟨.privateRow 9 24, 197622102059671580962070400⟩, ⟨.privateRow 10 12, 907510756860521227814400⟩, ⟨.privateRow 10 13, 2960149732067232703152000⟩, ⟨.privateRow 10 14, 6108245478868892879520000⟩, ⟨.privateRow 10 15, 10239640602758398608940800⟩, ⟨.privateRow 10 17, 51261753446551942132238400⟩, ⟨.privateRow 10 18, 206153284911825134683800⟩, ⟨.privateRow 10 19, 55777007287042804694131200⟩, ⟨.privateRow 11 10, 600644138755441133152800⟩, ⟨.privateRow 11 11, 2034263896087586646483000⟩, ⟨.privateRow 11 12, 4328631651852282742506000⟩, ⟨.privateRow 11 13, 7425335910249997906666500⟩, ⟨.privateRow 11 14, 9322015543319230837722000⟩, ⟨.privateRow 11 15, 366494728732133572771200⟩, ⟨.privateRow 11 16, 57892593260835173624784000⟩, ⟨.privateRow 11 19, 42719541817839319576143000⟩, ⟨.privateRow 12 8, 442438762922534763259875⟩, ⟨.privateRow 12 9, 1631774149354975669243200⟩, ⟨.privateRow 12 10, 3668063739096268836324000⟩, ⟨.privateRow 12 11, 6534480190855898041992000⟩, ⟨.privateRow 12 12, 9898629950131286228865000⟩, ⟨.privateRow 12 13, 11987431752280202276058000⟩, ⟨.privateRow 12 14, 323955162004296640217400⟩, ⟨.privateRow 12 15, 73789786900978679160630000⟩, ⟨.privateRow 13 6, 367008026671534320072000⟩, ⟨.privateRow 13 7, 1544786189187155275110750⟩, ⟨.privateRow 13 8, 3759479657827640022276000⟩, ⟨.privateRow 13 9, 7096160691522688309524000⟩, ⟨.privateRow 13 10, 11481487792972792604856000⟩, ⟨.privateRow 13 11, 16477719351329656267848000⟩, ⟨.privateRow 13 12, 21836977586956292044284000⟩, ⟨.privateRow 13 13, 71990036000954808937200⟩, ⟨.privateRow 13 14, 26689639272946579165236000⟩, ⟨.privateRow 13 17, 6439108775640957910494000⟩, ⟨.privateRow 13 21, 3359535013377891083736000⟩, ⟨.privateRow 14 4, 381280561042093988074800⟩, ⟨.privateRow 14 5, 1761638528023364736345600⟩, ⟨.privateRow 14 6, 4757341545729763623933300⟩, ⟨.privateRow 14 7, 9608270138260768499484960⟩, ⟨.privateRow 14 8, 16489146341171077666092000⟩, ⟨.privateRow 14 9, 25244505957668153000644800⟩, ⟨.privateRow 14 10, 39514530871635195127752000⟩, ⟨.privateRow 14 12, 100450096899998943403706400⟩, ⟨.privateRow 14 14, 15909797956211012775121200⟩, ⟨.privateRow 14 19, 46169609755279017465057600⟩, ⟨.privateRow 15 2, 459725843935921937774400⟩, ⟨.privateRow 15 3, 2547647385144900738499800⟩, ⟨.privateRow 15 4, 7578715750767183709486800⟩, ⟨.privateRow 15 5, 16650695410054172683766550⟩, ⟨.privateRow 15 6, 30571768621738808861997600⟩, ⟨.privateRow 15 7, 49445156393322461271700200⟩, ⟨.privateRow 15 9, 246575871919381464333373500⟩, ⟨.privateRow 15 11, 215530968783258602477083080⟩, ⟨.privateRow 15 16, 538063127742603035971157760⟩, ⟨.privateRow 15 19, 302442139579344644813333400⟩, ⟨.privateRow 16 2, 27902804694444150945474000⟩, ⟨.privateRow 16 6, 1559784113354020860306000⟩, ⟨.privateRow 16 12, 5122136055240435252637365750⟩, ⟨.privateRow 17 1, 218369775869562920442840000⟩, ⟨.hall 16 3, 270426967021130551632000⟩, ⟨.hall 15 5, 6338132039557747303875⟩, ⟨.hall 16 9, 53896283637078466584000⟩, ⟨.hall 11 10, 157102058111784786000⟩, ⟨.hall 12 10, 1071188532412396398000⟩, ⟨.hall 13 10, 2690954798850910191600⟩, ⟨.hall 14 15, 26237854538359690426200⟩, ⟨.hall 15 15, 252116807795741503865250⟩, ⟨.hall 9 18, 74643735256888672728⟩, ⟨.hall 7 23, 1087029033632650961160⟩, ⟨.hall 4 25, 11948414220293327576800⟩, ⟨.hall 3 31, 833217176052301018314711375⟩, ⟨.assumptionRow 17, 11245587295470197978880⟩]
  caps := #[0, 205192137113778977955936000, 0, 0, 9056782175396086900109880, 177048704314017470111100, 568126253177637015026880, 618440114288034719881200, 127456672496652554073600, 0, 488015322184428675485400, 289131928839829646628705, 59594288567578181809920, 669258634047060250217640, 9654348469497043270815780, 15967267919245164367725660, 8017396234888152624811200, 0, 8323199418330720000000] }

theorem case_53_35_17_checked :
    (Witness.linear .conditional case_53_35_17).check 53 35 17 = true := by
  change case_53_35_17.check 53 35 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_35_18 : Certificate := {
  objectiveScale := 203174385812112000000
  eta := 53568479831624406027303724800
  rows := #[⟨.count 2, 7337446919656677285144883200⟩, ⟨.count 3, 989020138714452879770736000⟩, ⟨.count 4, 129310692763262794429726080⟩, ⟨.count 5, 16237644068446241309668800⟩, ⟨.count 6, 2011456408079254667731200⟩, ⟨.count 7, 302799889388274896217600⟩, ⟨.count 8, 82581788014984062604800⟩, ⟨.count 9, 24774536404495218781440⟩, ⟨.count 10, 13763631335830677100800⟩, ⟨.path 7, 72143201744832663244800⟩, ⟨.privateRow 2 33, 576682389339969539846419200⟩, ⟨.privateRow 3 29, 15991619158318267956492000⟩, ⟨.privateRow 3 30, 109399076703572151045950400⟩, ⟨.privateRow 3 31, 181074333854188387938124800⟩, ⟨.privateRow 4 26, 3370541268753234938522160⟩, ⟨.privateRow 4 27, 20921958357282853954155072⟩, ⟨.privateRow 4 28, 42648418170684180773198280⟩, ⟨.privateRow 4 29, 66475930716578400028371360⟩, ⟨.privateRow 4 30, 107168450851745192643814080⟩, ⟨.privateRow 5 23, 353221478112304599918120⟩, ⟨.privateRow 5 24, 3623093370374399421477120⟩, ⟨.privateRow 5 25, 8969365294951257104388480⟩, ⟨.privateRow 5 26, 15433494076485094120999488⟩, ⟨.privateRow 5 27, 23836299149827361160643680⟩, ⟨.privateRow 5 28, 39781056420502205621292480⟩, ⟨.privateRow 5 29, 44214190991570068328059200⟩, ⟨.privateRow 6 21, 466215702708931189414400⟩, ⟨.privateRow 6 22, 1749210075305480873685600⟩, ⟨.privateRow 6 23, 3511551778467085913788800⟩, ⟨.privateRow 6 24, 5885672849984593295229600⟩, ⟨.privateRow 6 25, 8852571051901493930133120⟩, ⟨.privateRow 6 26, 14712830339740999868001600⟩, ⟨.privateRow 6 27, 17567800725401877460910400⟩, ⟨.privateRow 6 28, 15099440912799243708708000⟩, ⟨.privateRow 7 18, 11797398287854866086400⟩, ⟨.privateRow 7 19, 273330971581737428639280⟩, ⟨.privateRow 7 20, 760604484058642894070400⟩, ⟨.privateRow 7 21, 1451817326799139457757600⟩, ⟨.privateRow 7 22, 2386094026327502944939200⟩, ⟨.privateRow 7 23, 3549787988989329810122400⟩, ⟨.privateRow 7 24, 5825112872106938315986080⟩, ⟨.privateRow 7 25, 7165137561172103068756200⟩, ⟨.privateRow 7 26, 6050590646883564444062400⟩, ⟨.privateRow 8 16, 7885413786152992089000⟩, ⟨.privateRow 8 17, 136854288850589118900000⟩, ⟨.privateRow 8 18, 346843509662933062940160⟩, ⟨.privateRow 8 19, 653007842266633235782400⟩, ⟨.privateRow 8 20, 1061950180255185680058600⟩, ⟨.privateRow 8 21, 1567333518367718354853600⟩, ⟨.privateRow 8 22, 2558314974547527106111200⟩, ⟨.privateRow 8 23, 3246496541339060961151200⟩, ⟨.privateRow 8 24, 390112925674950754075800⟩, ⟨.privateRow 9 14, 3493844877557018033280⟩, ⟨.privateRow 9 15, 67785884328966084721440⟩, ⟨.privateRow 9 16, 174172498358875477493760⟩, ⟨.privateRow 9 17, 328124971046203342083072⟩, ⟨.privateRow 9 18, 533723037356100700908800⟩, ⟨.privateRow 9 19, 786419485451025312846960⟩, ⟨.privateRow 9 20, 1279231221013062645968640⟩, ⟨.privateRow 9 21, 361295322565555273896000⟩, ⟨.privateRow 10 12, 1278051481184277159360⟩, ⟨.privateRow 10 13, 34938448775570180332800⟩, ⟨.privateRow 10 14, 97836479412196396391520⟩, ⟨.privateRow 10 15, 189312492828289222304640⟩, ⟨.privateRow 10 16, 311058068189773302478080⟩, ⟨.privateRow 10 17, 461999225172716394683520⟩, ⟨.privateRow 10 18, 102539053451938544400960⟩, ⟨.privateRow 11 10, 344090783395766927520⟩, ⟨.privateRow 11 11, 19293661783262645578800⟩, ⟨.privateRow 11 12, 61803998402239675058400⟩, ⟨.privateRow 11 13, 127456961016181999402200⟩, ⟨.privateRow 11 14, 181898900495125880320800⟩, ⟨.privateRow 12 9, 11715471910855873960800⟩, ⟨.privateRow 12 10, 44222687927241678082800⟩, ⟨.privateRow 12 11, 66549426239181295872000⟩, ⟨.privateRow 13 7, 7772765017779377916300⟩, ⟨.privateRow 13 8, 28117132586054097505920⟩, ⟨.privateRow 14 5, 5788821414775843604160⟩, ⟨.privateRow 14 6, 3514641573256762188240⟩, ⟨.privateRow 15 3, 2733610112533037257520⟩, ⟨.hall 5 29, 4772883256482683051629920⟩, ⟨.hall 4 30, 25688175132329811276215040⟩, ⟨.hall 3 31, 72631166436842633358163425⟩, ⟨.hall 2 32, 171292979851524720078489600⟩, ⟨.assumptionRow 18, 207734869333648483200⟩]
  caps := #[0, 0, 0, 590507286284745781718745, 0, 33860458864991113520704, 10754430114040605907200, 10295378595605317860360, 24924624084059524037720, 1063697247192866098560, 0, 3347121578426865346800, 23820753807610893289200, 627765091522481932800, 104136798877680128590800, 0, 130557459739350806553600, 23897049305963095785600, 3043055303660143516800] }

theorem case_53_35_18_checked :
    (Witness.linear .conditional case_53_35_18).check 53 35 18 = true := by
  change case_53_35_18.check 53 35 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_35_19 : Certificate := {
  objectiveScale := 144759757985386544000000
  eta := 38953954600658613046523068876800
  rows := #[⟨.count 2, 5174695076102251179611920588800⟩, ⟨.count 3, 668239575544454311337752612800⟩, ⟨.count 4, 81911533578007448206683792000⟩, ⟨.count 5, 9738790628168627482637980800⟩, ⟨.count 6, 1114995706981739103557836800⟩, ⟨.count 7, 182928983176691571677457600⟩, ⟨.count 8, 51737490191387515221907200⟩, ⟨.count 9, 19955889073820898728449920⟩, ⟨.count 10, 7391070027341073603129600⟩, ⟨.path 6, 70343008220032626480494400⟩, ⟨.path 7, 35493297192793514262988800⟩, ⟨.privateRow 2 33, 438623050772556012977726112000⟩, ⟨.privateRow 3 29, 7662691850845858058044612800⟩, ⟨.privateRow 3 30, 77815956899107075796349602400⟩, ⟨.privateRow 3 31, 136343068794360784756931731200⟩, ⟨.privateRow 4 26, 1158211469409460154750421360⟩, ⟨.privateRow 4 27, 13206253058802620197967922336⟩, ⟨.privateRow 4 28, 30043036670385312455161119840⟩, ⟨.privateRow 4 29, 50001266249714869190252030880⟩, ⟨.privateRow 4 30, 85531494900648422530656591840⟩, ⟨.privateRow 5 24, 1895990467809573323862410880⟩, ⟨.privateRow 5 25, 5682219441448258619068878720⟩, ⟨.privateRow 5 26, 10702100460846392495649303552⟩, ⟨.privateRow 5 27, 17863886297600011457978389200⟩, ⟨.privateRow 5 28, 32102778305826144908530418880⟩, ⟨.privateRow 5 29, 39038206463767420707535657920⟩, ⟨.privateRow 6 21, 126792046540458179310830400⟩, ⟨.privateRow 6 22, 933881495463546456202576200⟩, ⟨.privateRow 6 23, 2171089110990484549115222400⟩, ⟨.privateRow 6 24, 4010887334837089275298329600⟩, ⟨.privateRow 6 25, 6580797578915139334123649280⟩, ⟨.privateRow 6 26, 11913612983713738390358865600⟩, ⟨.privateRow 6 27, 15823840983892753996586001600⟩, ⟨.privateRow 6 28, 15720278014581082048599292800⟩, ⟨.privateRow 7 19, 84060223221670174604165040⟩, ⟨.privateRow 7 20, 390700173945279529632100800⟩, ⟨.privateRow 7 21, 866734944099086256281287200⟩, ⟨.privateRow 7 22, 1586214130765688367561446400⟩, ⟨.privateRow 7 23, 2596575288980260920199467600⟩, ⟨.privateRow 7 24, 4689369965561220448557048000⟩, ⟨.privateRow 7 25, 6469298008216965423767865600⟩, ⟨.privateRow 7 26, 7114388840424716389498159200⟩, ⟨.privateRow 7 27, 3562759719965088229337150400⟩, ⟨.privateRow 8 17, 39727001396958270616821600⟩, ⟨.privateRow 8 18, 165282803486414758449985680⟩, ⟨.privateRow 8 19, 371503922624268685690639200⟩, ⟨.privateRow 8 20, 680440384392087588588118800⟩, ⟨.privateRow 8 21, 1113543889654939964100079200⟩, ⟨.privateRow 8 22, 2016684253085125853753924400⟩, ⟨.privateRow 8 23, 2881962980410968124700309280⟩, ⟨.privateRow 8 24, 3141897674435019506980373400⟩, ⟨.privateRow 9 15, 17122645563340153847250240⟩, ⟨.privateRow 9 16, 74448232639035541384250880⟩, ⟨.privateRow 9 17, 174059699143882283353702080⟩, ⟨.privateRow 9 18, 324221605199361762057285120⟩, ⟨.privateRow 9 19, 533265702472658460465800640⟩, ⟨.privateRow 9 20, 968124586867004340958504320⟩, ⟨.privateRow 9 21, 1438548596321484292289124480⟩, ⟨.privateRow 9 22, 468298196932330423494291456⟩, ⟨.privateRow 10 13, 7391070027341073603129600⟩, ⟨.privateRow 10 14, 36277835384199102935361120⟩, ⟨.privateRow 10 15, 90775778244889003980255360⟩, ⟨.privateRow 10 16, 175020538247436622922108928⟩, ⟨.privateRow 10 17, 293014865083921673510737920⟩, ⟨.privateRow 10 18, 534651528102784911766387440⟩, ⟨.privateRow 10 19, 345479730420857040420572160⟩, ⟨.privateRow 11 11, 3365576530307096015710800⟩, ⟨.privateRow 11 12, 19330490840738192500492800⟩, ⟨.privateRow 11 13, 53431277072653177922624400⟩, ⟨.privateRow 11 14, 109018282903280835646161600⟩, ⟨.privateRow 11 15, 188841839198564430559961280⟩, ⟨.privateRow 11 16, 154596548071884122865460800⟩, ⟨.privateRow 12 9, 1742180792158967349309120⟩, ⟨.privateRow 12 10, 11510837376764605700792400⟩, ⟨.privateRow 12 11, 35737041890440355883264000⟩, ⟨.privateRow 12 12, 79366013865019623690748800⟩, ⟨.privateRow 12 13, 52265423764769020479273600⟩, ⟨.privateRow 13 7, 1088862995099354593318200⟩, ⟨.privateRow 13 8, 7743025742928743774707200⟩, ⟨.privateRow 13 9, 27584529209183649697394400⟩, ⟨.privateRow 13 10, 22335651181525222427040000⟩, ⟨.privateRow 14 5, 888170599924179432981120⟩, ⟨.privateRow 14 6, 6133928205726364209025860⟩, ⟨.privateRow 14 7, 10569230139097735252475328⟩, ⟨.privateRow 15 4, 4662895649601942023150880⟩, ⟨.hall 5 29, 6849867723481913180294724480⟩, ⟨.hall 4 30, 24974067989964809911090896000⟩, ⟨.hall 3 31, 62337814793061212725439444325⟩, ⟨.hall 2 32, 136118873003531438857636800000⟩, ⟨.assumptionRow 19, 112338506864272070828160⟩]
  caps := #[0, 8150147288963780222178566400, 2085747718864966870599916800, 0, 124874002009843656192585468, 11624987350131052899883200, 19389377726935323242204520, 4072060585004716711218240, 5046294258049202808613600, 0, 0, 2555469348403106152358000, 797906633347993771235920, 502333795559452601773600, 36738209855455606695721524, 3022240880039122498305120, 331170487985829570887128320, 80810021117634549110198400, 15428995090432645602749440] }

theorem case_53_35_19_checked :
    (Witness.linear .conditional case_53_35_19).check 53 35 19 = true := by
  change case_53_35_19.check 53 35 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_35_20 : Certificate := {
  objectiveScale := 771954016681848000000
  eta := 242011751793965851839780038400
  rows := #[⟨.count 2, 33101175508258046829819379200⟩, ⟨.count 3, 4379735450098181633253393600⟩, ⟨.count 4, 545880070591947276028683840⟩, ⟨.count 5, 62209155846644690731848000⟩, ⟨.count 6, 5888376420425560035374400⟩, ⟨.count 7, 397424854822110801285600⟩, ⟨.count 8, 20645447003746015651200⟩, ⟨.path 7, 327298308332104607097600⟩, ⟨.privateRow 2 33, 2931632829084930476454748800⟩, ⟨.privateRow 3 29, 32659806819488462634220200⟩, ⟨.privateRow 3 30, 503736003487025440629498000⟩, ⟨.privateRow 3 31, 905248656815877953014035600⟩, ⟨.privateRow 4 26, 4858991975027473725241800⟩, ⟨.privateRow 4 27, 80745375504000854512625760⟩, ⟨.privateRow 4 28, 193117253204952683576129160⟩, ⟨.privateRow 4 29, 330165429391740239963265600⟩, ⟨.privateRow 4 30, 581455272596452222898049120⟩, ⟨.privateRow 5 23, 208242513215463159653220⟩, ⟨.privateRow 5 24, 11131371954157488244754400⟩, ⟨.privateRow 5 25, 34921478671879189102352640⟩, ⟨.privateRow 5 26, 67713084550364780318631840⟩, ⟨.privateRow 5 27, 116679070948977991125191520⟩, ⟨.privateRow 5 28, 217584430517179633549561920⟩, ⟨.privateRow 5 29, 277073253786123590347712160⟩, ⟨.privateRow 6 21, 1094044838444540845262400⟩, ⟨.privateRow 6 22, 5519339055233600005609200⟩, ⟨.privateRow 6 23, 13117337555221913648263200⟩, ⟨.privateRow 6 24, 24898531976083193363535600⟩, ⟨.privateRow 6 25, 42295737406660069521309120⟩, ⟨.privateRow 6 26, 79989862744272698979161400⟩, ⟨.privateRow 6 27, 112398237512751254779915200⟩, ⟨.privateRow 6 28, 119973641888340060665644800⟩, ⟨.privateRow 7 18, 63411015797219905214400⟩, ⟨.privateRow 7 19, 657778688287207877229840⟩, ⟨.privateRow 7 20, 2302090230483179233297200⟩, ⟨.privateRow 7 21, 5114817328003951511443500⟩, ⟨.privateRow 7 22, 9621041638528854339577200⟩, ⟨.privateRow 7 23, 16347814563915635970569400⟩, ⟨.privateRow 7 24, 31004816174050672654580880⟩, ⟨.privateRow 7 25, 45534547205677200046275900⟩, ⟨.privateRow 7 26, 54371505138282111052072800⟩, ⟨.privateRow 7 27, 41839104359180787110852400⟩, ⟨.privateRow 8 16, 43871574882960283258800⟩, ⟨.privateRow 8 17, 318831391796486764431600⟩, ⟨.privateRow 8 18, 978078051802467491475600⟩, ⟨.privateRow 8 19, 2144832549833613848208000⟩, ⟨.privateRow 8 20, 4019087878432368890598450⟩, ⟨.privateRow 8 21, 6836223639115399432503600⟩, ⟨.privateRow 8 22, 13042331031137300678986200⟩, ⟨.privateRow 8 23, 19910985226587751144408560⟩, ⟨.privateRow 8 24, 25365512324977448479455600⟩, ⟨.privateRow 8 25, 10171323557178870377491200⟩, ⟨.privateRow 9 14, 22868802834918663490560⟩, ⟨.privateRow 9 15, 153808580177907816601440⟩, ⟨.privateRow 9 16, 452135289382037742761280⟩, ⟨.privateRow 9 17, 992426637470070972353184⟩, ⟨.privateRow 9 18, 1866119015283042636916800⟩, ⟨.privateRow 9 19, 3178624634314245934697880⟩, ⟨.privateRow 9 20, 6081853752346379839191360⟩, ⟨.privateRow 9 21, 9653811018951636918501120⟩, ⟨.privateRow 9 22, 10352452945558402088137728⟩, ⟨.privateRow 10 12, 11944865766453051912480⟩, ⟨.privateRow 10 13, 79564376529821183394240⟩, ⟨.privateRow 10 14, 235702186626100345351200⟩, ⟨.privateRow 10 15, 522329809194774195975360⟩, ⟨.privateRow 10 16, 990362092769696370788064⟩, ⟨.privateRow 10 17, 1695449986718742240866880⟩, ⟨.privateRow 10 18, 3242625520025858583216600⟩, ⟨.privateRow 10 19, 5318562083122170003401280⟩, ⟨.privateRow 10 20, 598029781541842920029760⟩, ⟨.privateRow 11 10, 6881815667915338550400⟩, ⟨.privateRow 11 11, 46083587061933070650000⟩, ⟨.privateRow 11 12, 142135962064251415444800⟩, ⟨.privateRow 11 13, 322154995954286785890600⟩, ⟨.privateRow 11 14, 619128802760065173903600⟩, ⟨.privateRow 11 15, 1069950290969137261123440⟩, ⟨.privateRow 11 16, 2045619707287834384106400⟩, ⟨.privateRow 11 17, 535813866769095812447550⟩, ⟨.privateRow 12 8, 4815734847972005882925⟩, ⟨.privateRow 12 9, 31091060071117511665200⟩, ⟨.privateRow 12 10, 101383891536252755430000⟩, ⟨.privateRow 12 11, 238330132719068015841600⟩, ⟨.privateRow 12 12, 468731525202608572604700⟩, ⟨.privateRow 12 13, 822868530577876909526400⟩, ⟨.privateRow 12 14, 54341765863431476910480⟩, ⟨.privateRow 13 6, 3816805328423633145600⟩, ⟨.privateRow 13 7, 25345972884063188857500⟩, ⟨.privateRow 13 8, 87054968199129032662560⟩, ⟨.privateRow 13 9, 215513186579920142971200⟩, ⟨.privateRow 13 10, 268901275397691923632800⟩, ⟨.privateRow 14 4, 3514641573256762188240⟩, ⟨.privateRow 14 5, 26049696366491296218720⟩, ⟨.privateRow 14 6, 92259341297990007441300⟩, ⟨.privateRow 14 7, 77322114611648768141280⟩, ⟨.privateRow 15 2, 3884603844125895050160⟩, ⟨.privateRow 15 3, 32803321350396447090240⟩, ⟨.privateRow 15 4, 21708080305409413515600⟩, ⟨.hall 6 28, 887703370306389643406400⟩, ⟨.hall 5 29, 58708572839680955592360960⟩, ⟨.hall 4 30, 186261491314176884184458880⟩, ⟨.hall 3 31, 439800279967518365472677100⟩, ⟨.hall 2 32, 927558642984300991177113600⟩, ⟨.assumptionRow 20, 316692297357974137600⟩]
  caps := #[0, 37405720280855192003337600, 212415821917578139660800, 941722378184289936534300, 81078261909548712768960, 27550589938939784728440, 105311402740484772014040, 0, 8152129301052321678240, 33387813533375923219136, 8080650644570590246776, 6242620122181645883450, 0, 0, 0, 0, 5063563028898054877996800, 1522297820285730058771200, 382256601689326389625600] }

theorem case_53_35_20_checked :
    (Witness.linear .conditional case_53_35_20).check 53 35 20 = true := by
  change case_53_35_20.check 53 35 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_35_21 : Certificate := {
  objectiveScale := 220633838032899491200000
  eta := 102712306953258746070317861270400
  rows := #[⟨.count 2, 13824553021939837710237729024000⟩, ⟨.count 3, 1785935662754039814287018548800⟩, ⟨.count 4, 215612294837593799150496691200⟩, ⟨.count 5, 23384421682753739246101663200⟩, ⟨.count 6, 2064484238708376308931307200⟩, ⟨.count 7, 121952655451127714451638400⟩, ⟨.path 6, 84921870027293274455726400⟩, ⟨.path 7, 118036518357409839207820800⟩, ⟨.privateRow 2 33, 1334893766568043962387633926400⟩, ⟨.privateRow 3 32, 2366780916585829727255865793200⟩, ⟨.privateRow 4 27, 30827802008213319297657412944⟩, ⟨.privateRow 4 29, 256660542390314628437297746320⟩, ⟨.privateRow 4 31, 866491909878580080336058577760⟩, ⟨.privateRow 5 25, 20534504270247028490523494400⟩, ⟨.privateRow 5 26, 17593238511538115880263217408⟩, ⟨.privateRow 5 27, 37239549977595966833319767280⟩, ⟨.privateRow 5 28, 117975256702628791993165679040⟩, ⟨.privateRow 5 29, 73425951666331837903982171520⟩, ⟨.privateRow 6 21, 378440383185642351988814400⟩, ⟨.privateRow 6 22, 1043675180802731377695494700⟩, ⟨.privateRow 6 23, 5682620419567088857585783200⟩, ⟨.privateRow 6 24, 10045124084123245908224834400⟩, ⟨.privateRow 6 25, 15077703665739782924595779040⟩, ⟨.privateRow 6 26, 31081594195111076866268019000⟩, ⟨.privateRow 6 27, 56800901093689532145308342400⟩, ⟨.privateRow 6 28, 50762792831531911140494484000⟩, ⟨.privateRow 7 17, 181477165849892432219700⟩, ⟨.privateRow 7 18, 31280064222854186498959200⟩, ⟨.privateRow 7 19, 227354593376745239084840160⟩, ⟨.privateRow 7 20, 577339356957124457701605600⟩, ⟨.privateRow 7 21, 1833645283747313135147848800⟩, ⟨.privateRow 7 22, 3860485973196540328138726800⟩, ⟨.privateRow 7 23, 6605768836936084532797080000⟩, ⟨.privateRow 7 24, 12228802525361831566638040560⟩, ⟨.privateRow 7 25, 19851605695153883268080763300⟩, ⟨.privateRow 7 26, 28987710655535017983317120400⟩, ⟨.privateRow 7 27, 26636855449115511416343126600⟩, ⟨.privateRow 8 14, 197975090018064471512400⟩, ⟨.privateRow 8 15, 1599029573222828423754000⟩, ⟨.privateRow 8 16, 21249326328605586608997600⟩, ⟨.privateRow 8 17, 110866050410116104046944000⟩, ⟨.privateRow 8 18, 275224970143113228296538480⟩, ⟨.privateRow 8 19, 691373008807529593292748000⟩, ⟨.privateRow 8 20, 1484219249865429342928462800⟩, ⟨.privateRow 8 21, 2726512939728783901668772800⟩, ⟨.privateRow 8 22, 5418116271917715768194192400⟩, ⟨.privateRow 8 23, 8559136256786988522684194160⟩, ⟨.privateRow 8 25, 41034758849920931827475343600⟩, ⟨.privateRow 9 12, 221732100820232208093888⟩, ⟨.privateRow 9 13, 1187850540108386829074400⟩, ⟨.privateRow 9 14, 12195265545112771445163840⟩, ⟨.privateRow 9 15, 54601529826982181243119920⟩, ⟨.privateRow 9 17, 576392596082193624940061856⟩, ⟨.privateRow 9 18, 494708953830029193169474560⟩, ⟨.privateRow 9 19, 1183079340438951475310951160⟩, ⟨.privateRow 9 21, 9105798273684202679055667200⟩, ⟨.privateRow 9 22, 3650597307904303074057772032⟩, ⟨.privateRow 9 24, 18183140927763142224739285440⟩, ⟨.privateRow 10 10, 138582563012645130058680⟩, ⟨.privateRow 10 11, 886928403280928832375552⟩, ⟨.privateRow 10 12, 7285483312664772551656320⟩, ⟨.privateRow 10 13, 29677988879015695544874240⟩, ⟨.privateRow 10 14, 29379503358680767572440160⟩, ⟨.privateRow 10 15, 143722716258932331246311040⟩, ⟨.privateRow 10 16, 479384801973342033898985856⟩, ⟨.privateRow 10 17, 474013957753474187080711680⟩, ⟨.privateRow 10 18, 1224931274468770304588672520⟩, ⟨.privateRow 10 20, 7067525936894218106152601760⟩, ⟨.privateRow 10 21, 4171446012731028530870314944⟩, ⟨.privateRow 10 22, 1222852536023580627637792320⟩, ⟨.privateRow 10 23, 4189628044998287571934013760⟩, ⟨.privateRow 11 8, 163038309426641329480800⟩, ⟨.privateRow 11 9, 692912815063225650293400⟩, ⟨.privateRow 11 10, 4896583893113461262073360⟩, ⟨.privateRow 11 11, 18708646006707092557921800⟩, ⟨.privateRow 11 12, 30807969777426494297660400⟩, ⟨.privateRow 11 13, 62246667886513104251357100⟩, ⟨.privateRow 11 14, 197543144367115967210918400⟩, ⟨.privateRow 11 15, 506935015500255885754651440⟩, ⟨.privateRow 11 16, 588513950927032985649194400⟩, ⟨.privateRow 11 17, 1319652456287913250983780300⟩, ⟨.privateRow 11 19, 3912647695723680838656732000⟩, ⟨.privateRow 12 6, 120984777233261621479800⟩, ⟨.privateRow 12 7, 640507644176090937246000⟩, ⟨.privateRow 12 8, 3947128357235160400778475⟩, ⟨.privateRow 12 9, 14227809802631566686024480⟩, ⟨.privateRow 12 10, 29554852724125338961494000⟩, ⟨.privateRow 12 11, 49585145622985993788028800⟩, ⟨.privateRow 12 12, 102716075871039116636350200⟩, ⟨.privateRow 12 13, 262514969363953489225442400⟩, ⟨.privateRow 12 14, 742169017459720090805685120⟩, ⟨.privateRow 12 15, 788094838897466202319417200⟩, ⟨.privateRow 12 16, 1637377728880654469702243250⟩, ⟨.privateRow 12 18, 2683684328588209287664923600⟩, ⟨.privateRow 13 4, 229234314757758861751200⟩, ⟨.privateRow 13 5, 725908663399569728878800⟩, ⟨.privateRow 13 6, 3843045865056545623476000⟩, ⟨.privateRow 13 7, 13338571689967093768147950⟩, ⟨.privateRow 13 8, 31359254258861412287564160⟩, ⟨.privateRow 13 10, 204706243078678663543821600⟩, ⟨.privateRow 13 11, 117960157802430080942805000⟩, ⟨.privateRow 13 12, 487414671624474728863528800⟩, ⟨.privateRow 13 13, 1247836992383860363942657200⟩, ⟨.privateRow 13 14, 1321637706496149953045335200⟩, ⟨.privateRow 13 16, 5741730125015339535508771200⟩, ⟨.privateRow 14 3, 1192018436740346081106240⟩, ⟨.privateRow 14 4, 4403845891290723021864720⟩, ⟨.privateRow 14 5, 15987070798635229793660160⟩, ⟨.privateRow 14 6, 40342373968431087682439310⟩, ⟨.privateRow 14 7, 56620875745166438852546400⟩, ⟨.privateRow 14 8, 41252352328621262592569520⟩, ⟨.privateRow 14 10, 1188094709386075775255931960⟩, ⟨.privateRow 14 11, 624888574133018697881739360⟩, ⟨.privateRow 14 12, 2598898196703139543331879760⟩, ⟨.privateRow 14 13, 2883889937953810618889696640⟩, ⟨.privateRow 14 14, 792692260432330143935649600⟩, ⟨.privateRow 14 16, 13781521156373511216709793760⟩, ⟨.privateRow 15 1, 3963461302161650719678248⟩, ⟨.privateRow 15 2, 6258096792886816925807760⟩, ⟨.privateRow 15 3, 26423075347744338131188320⟩, ⟨.privateRow 15 4, 65280539094427188324112320⟩, ⟨.privateRow 15 5, 128812492320253648389543060⟩, ⟨.privateRow 15 6, 166465374690789330226486416⟩, ⟨.privateRow 15 7, 124565926639366165475602080⟩, ⟨.privateRow 15 9, 3563812287527017605444024660⟩, ⟨.privateRow 15 11, 10847993584016438019759364776⟩, ⟨.privateRow 15 13, 14580583265327172585016354830⟩, ⟨.privateRow 16 1, 114731774536258310306475600⟩, ⟨.privateRow 16 2, 121105762010494883101279800⟩, ⟨.privateRow 16 3, 326402695472135941620561600⟩, ⟨.privateRow 16 4, 569747562185737290953748150⟩, ⟨.privateRow 16 5, 713423034389097129542084640⟩, ⟨.privateRow 16 6, 580363976387955998238600600⟩, ⟨.privateRow 16 8, 528461506954886762623766400⟩, ⟨.privateRow 16 10, 237807678129699043180694880⟩, ⟨.privateRow 16 11, 126346338621130843497298816800⟩, ⟨.privateRow 16 13, 509587881706497949672917600⟩, ⟨.privateRow 17 1, 3346922877380949496617187200⟩, ⟨.privateRow 17 2, 1212352868896504926019228800⟩, ⟨.privateRow 17 3, 3963461302161650719678248000⟩, ⟨.privateRow 17 5, 12003625657975285036739836800⟩, ⟨.privateRow 17 10, 567567658469548383057925113600⟩, ⟨.privateRow 17 11, 377321515965789148513369209600⟩, ⟨.privateRow 18 2, 202136526410244186703590648000⟩, ⟨.privateRow 18 9, 5950300414476373318222735075200⟩, ⟨.privateRow 18 10, 6367300581922691881163105412000⟩, ⟨.privateRow 18 11, 3072475201435711637894577849600⟩, ⟨.hall 16 5, 25632291875004827495683200⟩, ⟨.hall 15 7, 667223555123962098707445⟩, ⟨.hall 17 17, 145238837494768045261098465600⟩, ⟨.hall 16 18, 5507125177740398894710828800⟩, ⟨.hall 15 19, 59451919532424760795173720⟩, ⟨.hall 8 21, 28033930857731800911840⟩, ⟨.hall 6 22, 67741269769969567825680⟩, ⟨.hall 7 23, 233903902650972468194280⟩, ⟨.hall 5 24, 554932737819874684690992⟩, ⟨.hall 4 26, 5055733582789269266734848⟩]
  caps := #[0, 2293521746091569633612649600, 1260995462054531460459417600, 95806147383599330249436480, 67396258346154565075124800, 41309079973997799844863576, 1465135602712745915397600, 87424187541796788574320, 5667502277833377272509680, 11400641236590371437479808, 4039591456456607687729856, 0, 1877061963309733633813380, 0, 80838907332507906768155970, 235871520079233118900599780, 547492419835736234803974030, 4633227705260094248785276800, 0] }

theorem case_53_35_21_checked :
    (Witness.linear .conditional case_53_35_21).check 53 35 21 = true := by
  change case_53_35_21.check 53 35 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_35_22 : Certificate := {
  objectiveScale := 3519504683261424000000
  eta := 1650129579039326737046946451200
  rows := #[⟨.count 2, 202861030089133950813639360000⟩, ⟨.count 3, 23167070579086810013087049600⟩, ⟨.count 4, 2355915492295656470793694080⟩, ⟨.count 5, 196042171934877347424945600⟩, ⟨.count 6, 10677882274522703108668800⟩, ⟨.path 6, 8714984931154802670678000⟩, ⟨.path 7, 134852388279333127603200⟩, ⟨.privateRow 2 33, 22331760455190376097972064000⟩, ⟨.privateRow 3 32, 37814830251699276167424832800⟩, ⟨.privateRow 4 27, 348614123136368848246968480⟩, ⟨.privateRow 5 23, 152206655228942039926200⟩, ⟨.privateRow 5 24, 35416314290985827804542080⟩, ⟨.privateRow 5 25, 146808392523488895576817440⟩, ⟨.privateRow 5 26, 265497112848948179084069184⟩, ⟨.privateRow 5 29, 5258435524849489595370357600⟩, ⟨.privateRow 6 20, 121765324183153631940960⟩, ⟨.privateRow 6 21, 2924449238928732527812800⟩, ⟨.privateRow 6 22, 17339850491851012394669400⟩, ⟨.privateRow 6 23, 51275244205477441494259200⟩, ⟨.privateRow 6 24, 109370238618868505817739200⟩, ⟨.privateRow 6 28, 5059911213613955654678923200⟩, ⟨.privateRow 7 17, 23416408496760313834800⟩, ⟨.privateRow 7 18, 212876440879639216680000⟩, ⟨.privateRow 7 19, 1634465313073869905669040⟩, ⟨.privateRow 7 20, 6853202220051851848984800⟩, ⟨.privateRow 7 21, 18258944525348854712685300⟩, ⟨.privateRow 7 22, 40122343358591886304941600⟩, ⟨.privateRow 7 23, 80224615509900835198024800⟩, ⟨.privateRow 7 24, 95866776385736724839671200⟩, ⟨.privateRow 8 15, 16047608620157417872800⟩, ⟨.privateRow 8 16, 124177923846456209730000⟩, ⟨.privateRow 8 17, 750486216119309892986400⟩, ⟨.privateRow 8 18, 2685223425255769079201520⟩, ⟨.privateRow 8 19, 6834752928508949783539200⟩, ⟨.privateRow 8 20, 14800766743259115637718700⟩, ⟨.privateRow 8 21, 29151299814057794332159200⟩, ⟨.privateRow 8 22, 67195158151794384209097600⟩, ⟨.privateRow 8 23, 88138510076042302717320480⟩, ⟨.privateRow 8 24, 81927627036937948931464800⟩, ⟨.privateRow 8 25, 95835554507741044421224800⟩, ⟨.privateRow 9 13, 10218069162222682400640⟩, ⟨.privateRow 9 14, 67858459308094224147840⟩, ⟨.privateRow 9 15, 351671880333163985955360⟩, ⟨.privateRow 9 16, 1153093623033856644241920⟩, ⟨.privateRow 9 17, 2880133094525166745993728⟩, ⟨.privateRow 9 18, 6217505861709498117041280⟩, ⟨.privateRow 9 19, 12317456622177684355538160⟩, ⟨.privateRow 9 20, 28280209417978310657504640⟩, ⟨.privateRow 9 21, 56339027337441796529662080⟩, ⟨.privateRow 9 22, 79523145061914248051220864⟩, ⟨.privateRow 9 23, 94403037978248325585779520⟩, ⟨.privateRow 9 24, 104786299258593608018563200⟩, ⟨.privateRow 10 11, 6357909700938557938176⟩, ⟨.privateRow 10 12, 40872276648890729602560⟩, ⟨.privateRow 10 13, 183401241373227632832000⟩, ⟨.privateRow 10 14, 566251332739840316368800⟩, ⟨.privateRow 10 15, 1387180298386594459238400⟩, ⟨.privateRow 10 16, 2968349091625689237385920⟩, ⟨.privateRow 10 17, 5841329537737300105699200⟩, ⟨.privateRow 10 18, 13408235505244955701806480⟩, ⟨.privateRow 10 19, 27357177170324195013980160⟩, ⟨.privateRow 10 20, 51220910028186257389430400⟩, ⟨.privateRow 10 21, 75341229956121911567385600⟩, ⟨.privateRow 10 22, 98122415153297381979612480⟩, ⟨.privateRow 10 25, 595887139333340169558122880⟩, ⟨.privateRow 11 9, 5588006573090529437850⟩, ⟨.privateRow 11 10, 27815854941606190979520⟩, ⟨.privateRow 11 11, 112824513666208784840400⟩, ⟨.privateRow 11 12, 330122234471809739097600⟩, ⟨.privateRow 11 14, 3267459843465298667659200⟩, ⟨.privateRow 11 15, 2452762351815203054586960⟩, ⟨.privateRow 11 16, 7291727688263908635345600⟩, ⟨.privateRow 11 17, 15005660317605768383773200⟩, ⟨.privateRow 11 18, 28708516817028144761464800⟩, ⟨.privateRow 11 19, 50411269964707362901990800⟩, ⟨.privateRow 11 20, 73237159214467557549720480⟩, ⟨.privateRow 11 21, 92321319262886333685865800⟩, ⟨.privateRow 12 7, 5509743175708309137600⟩, ⟨.privateRow 12 8, 23416408496760313834800⟩, ⟨.privateRow 12 9, 84299070588337129805280⟩, ⟨.privateRow 12 10, 237509286181426040324400⟩, ⟨.privateRow 12 11, 335034767722878336405600⟩, ⟨.privateRow 12 12, 487841843682506538225000⟩, ⟨.privateRow 12 13, 4278816461680748255268000⟩, ⟨.privateRow 12 14, 3718525669285537836966240⟩, ⟨.privateRow 12 15, 9876520739300239035211200⟩, ⟨.privateRow 12 16, 19201454967343457344536000⟩, ⟨.privateRow 12 17, 34723188599481722515032000⟩, ⟨.privateRow 12 18, 57979027437978537054964800⟩, ⟨.privateRow 12 19, 52508954413135327743155520⟩, ⟨.privateRow 12 22, 358153967957949000103266000⟩, ⟨.privateRow 13 5, 5203646332613403074400⟩, ⟨.privateRow 13 6, 22038972702833236550400⟩, ⟨.privateRow 13 7, 81957429738661098421800⟩, ⟨.privateRow 13 8, 218553145969762929124800⟩, ⟨.privateRow 13 9, 428185755369331452979200⟩, ⟨.privateRow 13 10, 583608950226949360190400⟩, ⟨.privateRow 13 11, 811768827887690879606400⟩, ⟨.privateRow 13 12, 7816822909100352036489600⟩, ⟨.privateRow 13 13, 6088266209157681597048000⟩, ⟨.privateRow 13 14, 15069759779248415303462400⟩, ⟨.privateRow 13 15, 27830401498399632992659800⟩, ⟨.privateRow 13 16, 47421572407153458417446400⟩, ⟨.privateRow 13 17, 74916896250635164062136800⟩, ⟨.privateRow 13 18, 78735331929506879238131520⟩, ⟨.privateRow 13 22, 372601892000450113739337600⟩, ⟨.privateRow 14 4, 27058960929589695986880⟩, ⟨.privateRow 14 5, 100277325797891226304320⟩, ⟨.privateRow 14 6, 258751313889201467874540⟩, ⟨.privateRow 14 7, 568238179521383615724480⟩, ⟨.privateRow 14 8, 974122593465229055527680⟩, ⟨.privateRow 14 9, 1292585749021169323680960⟩, ⟨.privateRow 14 10, 1968539407627650383045520⟩, ⟨.privateRow 14 11, 17312815183859298214151040⟩, ⟨.privateRow 14 12, 14100424540409190578763168⟩, ⟨.privateRow 14 13, 30468390006717997681226880⟩, ⟨.privateRow 14 15, 204635324812945618021921920⟩, ⟨.privateRow 14 16, 90796343399238224883975840⟩, ⟨.privateRow 14 20, 1029038754671831343533052960⟩, ⟨.privateRow 15 2, 44860908909582917030880⟩, ⟨.privateRow 15 3, 142059544880345903931120⟩, ⟨.privateRow 15 4, 401109303191564905217280⟩, ⟨.privateRow 15 5, 905629598612205137560890⟩, ⟨.privateRow 15 6, 1818362174468427570318336⟩, ⟨.privateRow 15 7, 2922367780395687166583040⟩, ⟨.privateRow 15 8, 4196220402619448239196160⟩, ⟨.privateRow 15 10, 60052443972146223025428000⟩, ⟨.privateRow 15 12, 74249788790794125787998720⟩, ⟨.privateRow 15 13, 154702844374696689380989680⟩, ⟨.privateRow 15 14, 277137877840857666297624960⟩, ⟨.privateRow 15 20, 7228842000781281667438972320⟩, ⟨.privateRow 16 1, 672913633643743755463200⟩, ⟨.privateRow 16 2, 710297724401729519655600⟩, ⟨.privateRow 16 3, 1754853201463096460325600⟩, ⟨.privateRow 16 6, 42922276774561655259188400⟩, ⟨.privateRow 16 10, 492662501645039594833124160⟩, ⟨.privateRow 16 12, 529526953541489356903249800⟩, ⟨.privateRow 16 14, 1615927323013934657216490000⟩, ⟨.privateRow 17 0, 7177745425533266724940800⟩, ⟨.privateRow 17 1, 5682381795213836157244800⟩, ⟨.privateRow 17 2, 10027732579789122630432000⟩, ⟨.privateRow 17 7, 14205954488034590393112000⟩, ⟨.privateRow 17 14, 27964137290606330497033109760⟩, ⟨.privateRow 18 2, 543377759167323082536534000⟩, ⟨.privateRow 18 7, 52691176646528298912633600⟩, ⟨.privateRow 18 13, 139800229878568882674999467520⟩, ⟨.privateRow 18 17, 1228758239397039930642615552000⟩, ⟨.hall 15 5, 40407803981058142178550⟩, ⟨.hall 16 5, 325461496010699594145600⟩, ⟨.hall 17 5, 5479439588241913437343200⟩, ⟨.hall 12 10, 548534566810985040000⟩, ⟨.hall 17 12, 93665633987041255339200⟩, ⟨.hall 7 16, 38394480723866023680⟩, ⟨.hall 8 16, 57338318035502035840⟩, ⟨.hall 15 16, 576154810505427659906400⟩, ⟨.hall 10 17, 115895951226282741696⟩, ⟨.hall 4 27, 818766835024653732016800⟩, ⟨.hall 5 27, 2357128746790144773320160⟩, ⟨.hall 3 31, 12958360928730727599931917075⟩]
  caps := #[0, 10251088843283302745491200, 1339809186500033511834000, 3657759191120863354125600, 536675812423827217107120, 535951012193647433222400, 746476974017523744611880, 134852388279333127603200, 4164379465408472494800, 433525877417954606251776, 19835770066374480623856, 20459159057478105619380, 1003694918009254922506440, 0, 837556026761578637265324, 6939909485769637195995462, 28007556889767650104595400, 0, 0] }

theorem case_53_35_22_checked :
    (Witness.linear .conditional case_53_35_22).check 53 35 22 = true := by
  change case_53_35_22.check 53 35 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_36_1_checked :
    (Witness.rising).check 53 36 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_36_2_checked :
    (Witness.rising).check 53 36 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_36_3_checked :
    (Witness.rising).check 53 36 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_36_4_checked :
    (Witness.rising).check 53 36 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_36_5_checked :
    (Witness.rising).check 53 36 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_36_6_checked :
    (Witness.rising).check 53 36 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_36_7_checked :
    (Witness.rising).check 53 36 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_36_8_checked :
    (Witness.rising).check 53 36 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_36_9_checked :
    (Witness.rising).check 53 36 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_36_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_36_10_checked :
    (Witness.linear .positive case_53_36_10).check 53 36 10 = true := by
  change case_53_36_10.check 53 36 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_36_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_36_11_checked :
    (Witness.linear .positive case_53_36_11).check 53 36 11 = true := by
  change case_53_36_11.check 53 36 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_36_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_53_36_12_checked :
    (Witness.linear .positive case_53_36_12).check 53 36 12 = true := by
  change case_53_36_12.check 53 36 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_36_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_53_36_13_checked :
    (Witness.linear .positive case_53_36_13).check 53 36 13 = true := by
  change case_53_36_13.check 53 36 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_36_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_53_36_14_checked :
    (Witness.linear .positive case_53_36_14).check 53 36 14 = true := by
  change case_53_36_14.check 53 36 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_36_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_53_36_15_checked :
    (Witness.linear .positive case_53_36_15).check 53 36 15 = true := by
  change case_53_36_15.check 53 36 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_36_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_53_36_16_checked :
    (Witness.linear .positive case_53_36_16).check 53 36 16 = true := by
  change case_53_36_16.check 53 36 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_36_17 : Certificate := {
  objectiveScale := 923
  eta := 7607503575
  rows := #[⟨.assumptionRow 17, 2260⟩]
  caps := #[0, 0, 2136766125, 605433784, 173279810, 50178050, 14731860, 4460664, 1383954, 441584, 146025, 50616, 12956636, 6875022, 2371985, 606620, 113970, 14354] }

theorem case_53_36_17_checked :
    (Witness.linear .conditional case_53_36_17).check 53 36 17 = true := by
  change case_53_36_17.check 53 36 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_36_18 : Certificate := {
  objectiveScale := 60336494755954560000
  eta := 37480689155494818743301792000
  rows := #[⟨.count 2, 4396492144116765531926287200⟩, ⟨.count 3, 492436344849970912923692160⟩, ⟨.count 4, 53230719769708598048131200⟩, ⟨.count 5, 5178554185740881710564800⟩, ⟨.count 6, 521869801663809784785600⟩, ⟨.count 7, 89411259725617760330400⟩, ⟨.count 8, 30655289048783232113280⟩, ⟨.count 9, 10218429682927744037760⟩, ⟨.path 6, 163309237725618658433760⟩, ⟨.path 7, 5906953511868862252800⟩, ⟨.privateRow 2 33, 19178715211145009590870800⟩, ⟨.privateRow 2 34, 324211614283641828798054000⟩, ⟨.privateRow 3 30, 25845601927400179591506840⟩, ⟨.privateRow 3 31, 66729751972745811147918720⟩, ⟨.privateRow 3 32, 99972858338730494438761440⟩, ⟨.privateRow 4 27, 6197203894757741194329000⟩, ⟨.privateRow 4 28, 15598688371731274467241584⟩, ⟨.privateRow 4 29, 25225881537924405472073940⟩, ⟨.privateRow 4 30, 36330836025828891184157520⟩, ⟨.privateRow 4 31, 54952890115199170337923680⟩, ⟨.privateRow 5 23, 76719321270235284600960⟩, ⟨.privateRow 5 24, 942376430312148822910920⟩, ⟨.privateRow 5 25, 3407637759875118396918720⟩, ⟨.privateRow 5 26, 6076437870141949314644640⟩, ⟨.privateRow 5 27, 9289282469615814169183680⟩, ⟨.privateRow 5 28, 13090903255582182370660320⟩, ⟨.privateRow 5 29, 20342217243315990636694080⟩, ⟨.privateRow 5 30, 19899296975750039255247840⟩, ⟨.privateRow 6 21, 139165280443682609276160⟩, ⟨.privateRow 6 22, 609219804079048602039600⟩, ⟨.privateRow 6 23, 1464413497938030341601900⟩, ⟨.privateRow 6 24, 2418665811557272271794800⟩, ⟨.privateRow 6 25, 3626883610922096848323000⟩, ⟨.privateRow 6 26, 5000583202096556835240480⟩, ⟨.privateRow 6 27, 7679180318713303595995800⟩, ⟨.privateRow 6 28, 8063334478271385798685200⟩, ⟨.privateRow 6 29, 4126451284309675445724600⟩, ⟨.privateRow 7 18, 1976779551756855245400⟩, ⟨.privateRow 7 19, 100193693644291516214400⟩, ⟨.privateRow 7 20, 313669296874157000016240⟩, ⟨.privateRow 7 21, 645747986907239380164000⟩, ⟨.privateRow 7 22, 1051950841465686506744400⟩, ⟨.privateRow 7 23, 1545276815316215986118400⟩, ⟨.privateRow 7 24, 2102076963345135916339200⟩, ⟨.privateRow 7 25, 3187420173238961300921280⟩, ⟨.privateRow 7 26, 2886250205530528416379800⟩, ⟨.privateRow 8 16, 884287184099516310960⟩, ⟨.privateRow 8 17, 61523462049294125560680⟩, ⟨.privateRow 8 18, 164772178637209872608880⟩, ⟨.privateRow 8 19, 317282241654906452372448⟩, ⟨.privateRow 8 20, 512908401029178707673120⟩, ⟨.privateRow 8 21, 745945366853725314756480⟩, ⟨.privateRow 8 22, 1003595772430403432280000⟩, ⟨.privateRow 8 23, 1349258486049917535652560⟩, ⟨.privateRow 9 14, 81098648277204317760⟩, ⟨.privateRow 9 15, 37904260533253341131520⟩, ⟨.privateRow 9 16, 96507391449873138134400⟩, ⟨.privateRow 9 17, 180525591065056811333760⟩, ⟨.privateRow 9 18, 289976326779971758582656⟩, ⟨.privateRow 9 19, 421100225698923575284480⟩, ⟨.privateRow 9 20, 390713012737501101888240⟩, ⟨.privateRow 10 13, 24633714414200811519600⟩, ⟨.privateRow 10 14, 65732014018064045781360⟩, ⟨.privateRow 10 15, 122727598170996759120180⟩, ⟨.privateRow 10 16, 196937008434607430545920⟩, ⟨.privateRow 10 17, 56967745482322173010512⟩, ⟨.privateRow 11 11, 17760603972707745589440⟩, ⟨.privateRow 11 12, 52786530887573167542000⟩, ⟨.privateRow 11 13, 78462942208195177432800⟩, ⟨.privateRow 12 9, 14844854133866384102475⟩, ⟨.privateRow 12 10, 30776937021199038589920⟩, ⟨.privateRow 13 7, 12751569814409831845440⟩, ⟨.privateRow 14 5, 2899276675910054359920⟩, ⟨.hall 4 31, 7537756947781652578997010⟩, ⟨.hall 3 32, 28837260101029004319895200⟩, ⟨.hall 2 33, 79938174325444745857747200⟩, ⟨.assumptionRow 18, 64752120563844501216⟩]
  caps := #[0, 0, 130699168503348807853920, 93102143632686206269680, 0, 29308403411458394823600, 12026078679695995174260, 0, 0, 12883016923118016834368, 4047085469879341100640, 1568558683708989777090, 544510719358095657024, 198671987499423444864, 80669171964794790096720, 208344008057462635438080, 46311809522303266793280, 8005609032755892098112] }

theorem case_53_36_18_checked :
    (Witness.linear .conditional case_53_36_18).check 53 36 18 = true := by
  change case_53_36_18.check 53 36 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_36_19 : Certificate := {
  objectiveScale := 1466947081600000
  eta := 651721636654828336396800
  rows := #[⟨.count 2, 76634845521281065418400⟩, ⟨.count 3, 8667240016488202749600⟩, ⟨.count 4, 910280430867761553600⟩, ⟨.count 5, 88844574724893187200⟩, ⟨.count 6, 9411501559840380000⟩, ⟨.count 7, 2156089448254341600⟩, ⟨.count 8, 766609581601543680⟩, ⟨.count 9, 191652395400385920⟩, ⟨.path 6, 3420384270419756640⟩, ⟨.privateRow 2 33, 3143159175939891708600⟩, ⟨.privateRow 2 34, 8838529344877297665600⟩, ⟨.privateRow 3 30, 785076088450018365000⟩, ⟨.privateRow 3 31, 1856776319737788889440⟩, ⟨.privateRow 3 32, 2806861127869302023520⟩, ⟨.privateRow 3 33, 4786965764047239252480⟩, ⟨.privateRow 4 26, 3076216509844969920⟩, ⟨.privateRow 4 27, 130424588616267986040⟩, ⟨.privateRow 4 28, 385841447148464090784⟩, ⟨.privateRow 4 29, 642090282418550085120⟩, ⟨.privateRow 4 30, 981243152628958018800⟩, ⟨.privateRow 4 31, 1583936889518016273240⟩, ⟨.privateRow 5 24, 17317162870106299200⟩, ⟨.privateRow 5 25, 70430299672954066560⟩, ⟨.privateRow 5 26, 142929337022109237600⟩, ⟨.privateRow 5 27, 233254654659083977920⟩, ⟨.privateRow 5 28, 352743078462817442400⟩, ⟨.privateRow 5 29, 591745023407777279040⟩, ⟨.privateRow 5 30, 645930175054964960160⟩, ⟨.privateRow 6 21, 1060362509075349480⟩, ⟨.privateRow 6 22, 10777912156676464800⟩, ⟨.privateRow 6 23, 29795245354861336350⟩, ⟨.privateRow 6 24, 55115545801389044400⟩, ⟨.privateRow 6 25, 90109898823493949400⟩, ⟨.privateRow 6 26, 134822897011900056960⟩, ⟨.privateRow 6 27, 225672121569039245100⟩, ⟨.privateRow 6 28, 268541511174112176000⟩, ⟨.privateRow 6 29, 218346836188296816000⟩, ⟨.privateRow 7 19, 752920124787230400⟩, ⟨.privateRow 7 20, 5390223620635854000⟩, ⟨.privateRow 7 21, 12818655255847240800⟩, ⟨.privateRow 7 22, 23280632494841521800⟩, ⟨.privateRow 7 23, 37665562606239110400⟩, ⟨.privateRow 7 24, 56132476879023745200⟩, ⟨.privateRow 7 25, 93629039881495678560⟩, ⟨.privateRow 7 26, 116522945221332850200⟩, ⟨.privateRow 7 27, 63496263857056430400⟩, ⟨.privateRow 8 17, 411254098463328120⟩, ⟨.privateRow 8 18, 2667888458698554000⟩, ⟨.privateRow 8 19, 6072985279249728840⟩, ⟨.privateRow 8 20, 10964114120197077840⟩, ⟨.privateRow 8 21, 17617047533444849490⟩, ⟨.privateRow 8 22, 26098949416488268320⟩, ⟨.privateRow 8 23, 43497108239412587760⟩, ⟨.privateRow 8 24, 46734436618384106592⟩, ⟨.privateRow 9 15, 221137379308137600⟩, ⟨.privateRow 9 16, 1407225458819500320⟩, ⟨.privateRow 9 17, 3277449549624781440⟩, ⟨.privateRow 9 18, 5928447431051937792⟩, ⟨.privateRow 9 19, 9509271322396926080⟩, ⟨.privateRow 9 20, 14051847157203295440⟩, ⟨.privateRow 9 21, 22137372719501719680⟩, ⟨.privateRow 10 13, 128338657634187000⟩, ⟨.privateRow 10 14, 825579549417047040⟩, ⟨.privateRow 10 15, 2050281354960378540⟩, ⟨.privateRow 10 16, 3791668413546271440⟩, ⟨.privateRow 10 17, 6118502723157320496⟩, ⟨.privateRow 10 18, 7269481831089638160⟩, ⟨.privateRow 11 11, 84418317021598560⟩, ⟨.privateRow 11 12, 554911910151627600⟩, ⟨.privateRow 11 13, 1505840249574460800⟩, ⟨.privateRow 11 14, 2931825334398760800⟩, ⟨.privateRow 11 15, 1925857674559072800⟩, ⟨.privateRow 12 9, 66664802715536025⟩, ⟨.privateRow 12 10, 443386295708035680⟩, ⟨.privateRow 12 11, 1322091885787101000⟩, ⟨.privateRow 12 12, 506773160914482000⟩, ⟨.privateRow 13 7, 62005186747183680⟩, ⟨.privateRow 13 8, 442340573312497860⟩, ⟨.privateRow 13 9, 240934439931913728⟩, ⟨.privateRow 14 5, 81566346851949960⟩, ⟨.privateRow 14 6, 143940612091676400⟩, ⟨.hall 5 30, 21956122348634073600⟩, ⟨.hall 4 31, 278406333392418200970⟩, ⟨.hall 3 32, 826964115119715212640⟩, ⟨.assumptionRow 19, 1235756221539840⟩]
  caps := #[0, 32060853782711994240, 13402607178909748800, 915149125196706400, 1202768731620442272, 0, 4081845583495680, 137111861108439360, 151365798556823214, 61485547684642816, 71387512778982400, 21629841328775680, 487079481957895035, 296416128971058096, 0, 15318782668834444800, 4261070526865152000, 982788825442744320] }

theorem case_53_36_19_checked :
    (Witness.linear .conditional case_53_36_19).check 53 36 19 = true := by
  change case_53_36_19.check 53 36 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_36_20 : Certificate := {
  objectiveScale := 1235530296000000
  eta := 633222389188806085468800
  rows := #[⟨.count 2, 74082634528283551170000⟩, ⟨.count 3, 8197907256702082679760⟩, ⟨.count 4, 829040349403219393440⟩, ⟨.count 5, 68892191418031581600⟩, ⟨.count 6, 4141060686329767200⟩, ⟨.count 7, 239565494250482400⟩, ⟨.count 8, 95826197700192960⟩, ⟨.path 6, 3342309791097600960⟩, ⟨.privateRow 2 33, 2988998780389706284200⟩, ⟨.privateRow 2 34, 8872787210555116648800⟩, ⟨.privateRow 3 30, 710850712814743901400⟩, ⟨.privateRow 3 31, 1791305731997957054880⟩, ⟨.privateRow 3 32, 2808574021153192972680⟩, ⟨.privateRow 3 33, 4942268088453351976320⟩, ⟨.privateRow 4 26, 2062463341827877560⟩, ⟨.privateRow 4 27, 116191261090602718020⟩, ⟨.privateRow 4 28, 353100715522091376840⟩, ⟨.privateRow 4 29, 615234562717545560790⟩, ⟨.privateRow 4 30, 976593870858396871080⟩, ⟨.privateRow 4 31, 1640217668845861745640⟩, ⟨.privateRow 5 23, 1020625058044912320⟩, ⟨.privateRow 5 24, 14597238919312429380⟩, ⟨.privateRow 5 25, 61642646216508820320⟩, ⟨.privateRow 5 26, 129464615457164267280⟩, ⟨.privateRow 5 27, 220244194902760636608⟩, ⟨.privateRow 5 28, 348583194773367994440⟩, ⟨.privateRow 5 29, 614533405851337452480⟩, ⟨.privateRow 5 30, 716252914710092279520⟩, ⟨.privateRow 6 20, 77003194580512200⟩, ⟨.privateRow 6 21, 1590543763613024220⟩, ⟨.privateRow 6 22, 8892126103389929400⟩, ⟨.privateRow 6 23, 25528697981067030750⟩, ⟨.privateRow 6 24, 48975661450445558400⟩, ⟨.privateRow 6 25, 83610734135226398100⟩, ⟨.privateRow 6 26, 131547694469075604720⟩, ⟨.privateRow 6 27, 233373867012175289400⟩, ⟨.privateRow 6 28, 300122327519354340000⟩, ⟨.privateRow 6 29, 275051133086335105500⟩, ⟨.privateRow 7 18, 57039403392972000⟩, ⟨.privateRow 7 19, 1053154802646601200⟩, ⟨.privateRow 7 20, 4339557810137309760⟩, ⟨.privateRow 7 21, 10702493389967979600⟩, ⟨.privateRow 7 22, 20191948801112088000⟩, ⟨.privateRow 7 23, 34206530214765308400⟩, ⟨.privateRow 7 24, 53768193608385055800⟩, ⟨.privateRow 7 25, 95590054570146055920⟩, ⟨.privateRow 7 26, 129254140058644200600⟩, ⟨.privateRow 7 27, 128304433992151216800⟩, ⟨.privateRow 8 16, 22113737930813760⟩, ⟨.privateRow 8 17, 602906493863714040⟩, ⟨.privateRow 8 18, 2140844371347492720⟩, ⟨.privateRow 8 19, 4932653526617432616⟩, ⟨.privateRow 8 20, 9257875433368642080⟩, ⟨.privateRow 8 21, 15580740832315749090⟩, ⟨.privateRow 8 22, 24367233129477638400⟩, ⟨.privateRow 8 23, 43387307387881116660⟩, ⟨.privateRow 8 24, 61467714514788774192⟩, ⟨.privateRow 8 25, 29385702438499797390⟩, ⟨.privateRow 9 14, 6084203028583680⟩, ⟨.privateRow 9 15, 351362724900707520⟩, ⟨.privateRow 9 16, 1164110846135677440⟩, ⟨.privateRow 9 17, 2606666165723430720⟩, ⟨.privateRow 9 18, 4865841372109798080⟩, ⟨.privateRow 9 19, 8158240238771983360⟩, ⟨.privateRow 9 20, 12692978437038059160⟩, ⟨.privateRow 9 21, 22484172292130989440⟩, ⟨.privateRow 9 22, 21626553173560214880⟩, ⟨.privateRow 10 13, 222453673232590800⟩, ⟨.privateRow 10 14, 733438974705323040⟩, ⟨.privateRow 10 15, 1632039929581411350⟩, ⟨.privateRow 10 16, 3037037106657251880⟩, ⟨.privateRow 10 17, 5081184133052731704⟩, ⟨.privateRow 10 18, 7889690277315887040⟩, ⟨.privateRow 10 19, 9163380155080951800⟩, ⟨.privateRow 11 11, 156287965296743280⟩, ⟨.privateRow 11 12, 550022818432230000⟩, ⟨.privateRow 11 13, 1243897758608274000⟩, ⟨.privateRow 11 14, 2327207658433257600⟩, ⟨.privateRow 11 15, 3899939571986749200⟩, ⟨.privateRow 11 16, 1902834497189545920⟩, ⟨.privateRow 12 9, 129408146447805225⟩, ⟨.privateRow 12 10, 497763860276002320⟩, ⟨.privateRow 12 11, 1176437694980047500⟩, ⟨.privateRow 12 12, 1761640035559866000⟩, ⟨.privateRow 13 7, 128439315404880480⟩, ⟨.privateRow 13 8, 550572841250662230⟩, ⟨.privateRow 13 9, 552141424843968960⟩, ⟨.privateRow 14 5, 163132693703899920⟩, ⟨.privateRow 14 6, 244699040555849880⟩, ⟨.privateRow 15 3, 120203037466031520⟩, ⟨.hall 5 30, 56614735834807550400⟩, ⟨.hall 4 31, 338327010948531940335⟩, ⟨.hall 3 32, 905757206178698874000⟩, ⟨.assumptionRow 20, 657309648323328⟩]
  caps := #[0, 134361712260502446720, 8523128836434466800, 0, 0, 70880160263753568, 0, 136998276149301840, 23082289099126236, 38845337013129920, 86418832387312446, 45227711657558400, 657309648323328, 695390545047318120, 0, 0, 10734185178026069760, 3067153471109984256] }

theorem case_53_36_20_checked :
    (Witness.linear .conditional case_53_36_20).check 53 36 20 = true := by
  change case_53_36_20.check 53 36 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_36_21 : Certificate := {
  objectiveScale := 17158190696224578000000
  eta := 9209144142872319538632003264000
  rows := #[⟨.count 2, 1196441316643458631648390488000⟩, ⟨.count 3, 149993991849906385008830402400⟩, ⟨.count 4, 17601624670516976421248716800⟩, ⟨.count 5, 1835576667775207877640120000⟩, ⟨.count 6, 155557344726712532003400000⟩, ⟨.count 7, 7919283004269001629264000⟩, ⟨.path 6, 15541327097157979549504800⟩, ⟨.path 7, 8367265687207518707616000⟩, ⟨.privateRow 2 34, 406552231590157736641525968000⟩, ⟨.privateRow 3 30, 16958550607416746813946661200⟩, ⟨.privateRow 3 33, 366519860039427719955514984800⟩, ⟨.privateRow 4 27, 2457702341785573530632384400⟩, ⟨.privateRow 4 28, 7820427725852855148926130240⟩, ⟨.privateRow 4 29, 10664311546412140987759088700⟩, ⟨.privateRow 4 31, 61921156641915190489273404000⟩, ⟨.privateRow 5 24, 307536870524710675770721800⟩, ⟨.privateRow 5 25, 1305437236946571568572532800⟩, ⟨.privateRow 5 26, 2803765581354266676829281600⟩, ⟨.privateRow 5 27, 4590559465823177504433135360⟩, ⟨.privateRow 5 28, 7359729093710223314144860800⟩, ⟨.privateRow 5 29, 9295277281696465112352499200⟩, ⟨.privateRow 5 30, 3698531428222317160912838400⟩, ⟨.privateRow 5 31, 63176193299170307197476835200⟩, ⟨.privateRow 6 21, 32563337496125156699378400⟩, ⟨.privateRow 6 22, 190528940374532719753794000⟩, ⟨.privateRow 6 23, 539071015038361720280115750⟩, ⟨.privateRow 6 25, 3869488950076974233584575000⟩, ⟨.privateRow 6 26, 1803739264554474046090090800⟩, ⟨.privateRow 6 28, 16576017812584346618580078000⟩, ⟨.privateRow 6 30, 5880586155152156084835198000⟩, ⟨.privateRow 7 17, 87025087959000017904000⟩, ⟨.privateRow 7 18, 2663330296078563047937000⟩, ⟨.privateRow 7 19, 23397881603522050268280000⟩, ⟨.privateRow 7 20, 93447539450374219225315200⟩, ⟨.privateRow 7 21, 224788219561651462913196000⟩, ⟨.privateRow 7 22, 234043095929735673150570000⟩, ⟨.privateRow 7 23, 628855717747156843662576000⟩, ⟨.privateRow 7 24, 1916937872926209644378868000⟩, ⟨.privateRow 7 25, 1654225086977447740329974400⟩, ⟨.privateRow 7 26, 1158831510330041675910783000⟩, ⟨.privateRow 7 27, 5679540071740207918473228000⟩, ⟨.privateRow 7 28, 1195246070572885745902488000⟩, ⟨.privateRow 8 14, 26397610014230005430880⟩, ⟨.privateRow 8 15, 169698921520050034912800⟩, ⟨.privateRow 8 16, 2193032216566800451180800⟩, ⟨.privateRow 8 17, 13858745257470752851212000⟩, ⟨.privateRow 8 18, 46255812093116668607292000⟩, ⟨.privateRow 8 19, 103287248583178453749675720⟩, ⟨.privateRow 8 20, 154140044474758040045146800⟩, ⟨.privateRow 8 21, 239632554157302321175510350⟩, ⟨.privateRow 8 22, 469613482153151796615355200⟩, ⟨.privateRow 8 23, 1406200685458032389302977600⟩, ⟨.privateRow 8 24, 1184012001968258433591260640⟩, ⟨.privateRow 8 25, 985851742993937340323002200⟩, ⟨.privateRow 8 26, 1010830481469902482961972400⟩, ⟨.privateRow 9 12, 21998008345191671192400⟩, ⟨.privateRow 9 13, 152519524526662253600640⟩, ⟨.privateRow 9 14, 1583856600853800325852800⟩, ⟨.privateRow 9 15, 8460772440458335074000000⟩, ⟨.privateRow 9 16, 25371036291454394108568000⟩, ⟨.privateRow 9 17, 54699047659789326404956800⟩, ⟨.privateRow 9 18, 91951674882901185584232000⟩, ⟨.privateRow 9 19, 137541325066736191259859200⟩, ⟨.privateRow 9 20, 207771188820335334412218000⟩, ⟨.privateRow 9 21, 445164267163781624918659200⟩, ⟨.privateRow 9 23, 1621657978394177693629820160⟩, ⟨.privateRow 10 10, 23292008836085298909600⟩, ⟨.privateRow 10 11, 136112676635873465502975⟩, ⟨.privateRow 10 12, 1227488865661695252535920⟩, ⟨.privateRow 10 13, 5798046485268376192854000⟩, ⟨.privateRow 10 14, 16310677110715578355657200⟩, ⟨.privateRow 10 15, 34564370612382413361058500⟩, ⟨.privateRow 10 16, 60690505205443348849723200⟩, ⟨.privateRow 10 17, 93962292845651704331217360⟩, ⟨.privateRow 10 18, 135507731406380694545184000⟩, ⟨.privateRow 10 19, 233371371032052141762373500⟩, ⟨.privateRow 10 20, 425576612018698812555483600⟩, ⟨.privateRow 10 21, 91830685837002631392673800⟩, ⟨.privateRow 10 22, 221541942044425320578660400⟩, ⟨.privateRow 11 8, 31425726207416673132000⟩, ⟨.privateRow 11 9, 149734342517691207276000⟩, ⟨.privateRow 11 10, 1095972201483656475478500⟩, ⟨.privateRow 11 11, 4695003495388050965920800⟩, ⟨.privateRow 11 12, 12747621366565663336902000⟩, ⟨.privateRow 11 13, 26847239635351505523384000⟩, ⟨.privateRow 11 14, 48010653213380822377413000⟩, ⟨.privateRow 11 15, 76570210346471061207624000⟩, ⟨.privateRow 11 16, 112284119739099773100636000⟩, ⟨.privateRow 11 17, 182646320717505704243184000⟩, ⟨.privateRow 11 22, 784079725306597848811683000⟩, ⟨.privateRow 12 6, 27290762232756584562000⟩, ⟨.privateRow 12 7, 172841494140791702226000⟩, ⟨.privateRow 12 8, 1159054725414720826692000⟩, ⟨.privateRow 12 9, 4634312561649977515934625⟩, ⟨.privateRow 12 10, 12410019279308844219826800⟩, ⟨.privateRow 12 11, 26259561288390282188193000⟩, ⟨.privateRow 12 12, 47624479385562759797964000⟩, ⟨.privateRow 12 13, 77562620495680276373917500⟩, ⟨.privateRow 12 14, 116432315598478773954060000⟩, ⟨.privateRow 12 15, 189779960566589289044148000⟩, ⟨.privateRow 12 16, 277352984264590418171988000⟩, ⟨.privateRow 13 4, 62222937890685012801360⟩, ⟨.privateRow 13 5, 261991317434463211795200⟩, ⟨.privateRow 13 6, 1521005148438966979588800⟩, ⟨.privateRow 13 7, 5783073051016607072126400⟩, ⟨.privateRow 13 8, 15555734472671253200340000⟩, ⟨.privateRow 13 9, 33185566875032006827392000⟩, ⟨.privateRow 13 10, 61156258955416126867622400⟩, ⟨.privateRow 13 11, 101471252560194020876064000⟩, ⟨.privateRow 13 12, 155661049623197007024735600⟩, ⟨.privateRow 13 13, 257150432410049152904529600⟩, ⟨.privateRow 13 20, 2186825152168124774903797200⟩, ⟨.privateRow 14 2, 192594807756882182480400⟩, ⟨.privateRow 14 3, 404449096289452583208840⟩, ⟨.privateRow 14 4, 2554415344986016315003200⟩, ⟨.privateRow 14 5, 9661839522470256154433400⟩, ⟨.privateRow 14 6, 25694413176035811168561600⟩, ⟨.privateRow 14 7, 55864531424980638055721025⟩, ⟨.privateRow 14 8, 105156765035257671634298400⟩, ⟨.privateRow 14 9, 178246494578994459885610200⟩, ⟨.privateRow 14 11, 1026289581834485929892431500⟩, ⟨.privateRow 14 13, 550455220049944965747231240⟩, ⟨.privateRow 14 22, 20303344633730519677083768000⟩, ⟨.privateRow 15 2, 11324574696104672329847520⟩, ⟨.privateRow 15 3, 19867674905446793561136000⟩, ⟨.privateRow 15 4, 59768588673885770629750800⟩, ⟨.privateRow 15 7, 1357690677455215715989497120⟩, ⟨.privateRow 15 8, 191439238910340889385517600⟩, ⟨.privateRow 15 10, 4103585469741262515079469400⟩, ⟨.privateRow 15 11, 341453085534065120248432800⟩, ⟨.privateRow 15 19, 9135156921524435679410332800⟩, ⟨.privateRow 16 1, 155712902071439244535403400⟩, ⟨.privateRow 16 2, 171358696059478594464798000⟩, ⟨.privateRow 16 4, 599536307440835593933104000⟩, ⟨.privateRow 16 5, 380434931197266336080815125⟩, ⟨.privateRow 16 9, 165150047651526471476943000⟩, ⟨.privateRow 16 10, 49249031093173387507189158000⟩, ⟨.privateRow 16 19, 61789710685621118399730531000⟩, ⟨.privateRow 17 3, 21583307067870081381591744000⟩, ⟨.privateRow 17 12, 1035349241591369667756309516000⟩, ⟨.hall 14 8, 5725384628129349303120⟩, ⟨.hall 11 12, 230430951844722202860⟩, ⟨.hall 16 18, 3683466927469835526234614400⟩, ⟨.hall 8 19, 118199204521095325152⟩, ⟨.hall 3 29, 5623888405259459251781865⟩]
  caps := #[0, 212148394999847014745836800, 86128118453922110340138000, 0, 0, 19484431689663859501477440, 465246058030201896058800, 447982682938517078352000, 656887382847775724835330, 1036807991715742846348000, 1654388999067713830430355, 0, 5844836000894279242845255, 6507709956848125699787520, 135025321520309187242368665, 0, 403017804620253022407582375, 0] }

theorem case_53_36_21_checked :
    (Witness.linear .conditional case_53_36_21).check 53 36 21 = true := by
  change case_53_36_21.check 53 36 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_36_22 : Certificate := {
  objectiveScale := 2111777316458409600000
  eta := 1007434164965471650463235379200
  rows := #[⟨.count 2, 123267995567099358310390255200⟩, ⟨.count 3, 14031148048473689016681077280⟩, ⟨.count 4, 1420425226168557472229446080⟩, ⟨.count 5, 116979123234487824066556800⟩, ⟨.count 6, 6222293789068501280136000⟩, ⟨.path 6, 5401981801661535296256960⟩, ⟨.path 7, 59297251136879403648000⟩, ⟨.privateRow 2 34, 58661296925822202668610153600⟩, ⟨.privateRow 4 28, 1002224860605263501191505520⟩, ⟨.privateRow 4 29, 1017189477167973246770232600⟩, ⟨.privateRow 5 23, 221237112500213378849280⟩, ⟨.privateRow 5 24, 22898041143772084710900480⟩, ⟨.privateRow 5 25, 62720721393810492903770880⟩, ⟨.privateRow 5 26, 309828748737017573742238560⟩, ⟨.privateRow 5 29, 4699408125173282486826981120⟩, ⟨.privateRow 6 20, 122560332208925025214800⟩, ⟨.privateRow 6 21, 1928911074611235396842160⟩, ⟨.privateRow 6 22, 13596864205742280575112000⟩, ⟨.privateRow 6 23, 32485558823761800433376700⟩, ⟨.privateRow 6 24, 99438180743399477600649600⟩, ⟨.privateRow 6 25, 148937515501120209808144200⟩, ⟨.privateRow 6 28, 2968794639959894594114666400⟩, ⟨.privateRow 7 17, 30458780785650006266400⟩, ⟨.privateRow 7 18, 150843485795600031033600⟩, ⟨.privateRow 7 19, 1306167456548263905086400⟩, ⟨.privateRow 7 20, 6431589125609896323195120⟩, ⟨.privateRow 7 22, 65015899307369169625966500⟩, ⟨.privateRow 7 23, 54796589848926632702080800⟩, ⟨.privateRow 7 24, 117243099334630124120865600⟩, ⟨.privateRow 7 25, 127047925911344126138049600⟩, ⟨.privateRow 7 26, 232911769786268672917818000⟩, ⟨.privateRow 7 27, 1184668171131469293726256800⟩, ⟨.privateRow 7 28, 994209414878799804542457600⟩, ⟨.privateRow 8 14, 2639761001423000543088⟩, ⟨.privateRow 8 15, 16969892152005003491280⟩, ⟨.privateRow 8 16, 106605732749775021932400⟩, ⟨.privateRow 8 17, 745732482901997653422360⟩, ⟨.privateRow 8 18, 3063322653014963812047120⟩, ⟨.privateRow 8 19, 2451018089821256004257208⟩, ⟨.privateRow 8 20, 16278526175441836682376000⟩, ⟨.privateRow 8 21, 39670658299510030036594350⟩, ⟨.privateRow 8 22, 45818708810413509426456000⟩, ⟨.privateRow 8 23, 107867233920647359691933400⟩, ⟨.privateRow 8 24, 132647990321505777290172000⟩, ⟨.privateRow 8 25, 219977883651082192756880760⟩, ⟨.privateRow 8 26, 568485730461450281956716240⟩, ⟨.privateRow 9 12, 2199800834519167119240⟩, ⟨.privateRow 9 13, 14078725340922669563136⟩, ⟨.privateRow 9 14, 75421742897800015516800⟩, ⟨.privateRow 9 15, 444021337675253424683520⟩, ⟨.privateRow 9 16, 1607321143088671441791360⟩, ⟨.privateRow 9 17, 2134206773271686499684480⟩, ⟨.privateRow 9 18, 5599813004351991818737344⟩, ⟨.privateRow 9 19, 15795547681107406212640640⟩, ⟨.privateRow 9 20, 31905911303865999897456960⟩, ⟨.privateRow 9 21, 47002830173908969670069760⟩, ⟨.privateRow 9 22, 93130768130203459160144640⟩, ⟨.privateRow 9 24, 417443005561695229215459360⟩, ⟨.privateRow 10 10, 2329200883608529890960⟩, ⟨.privateRow 10 11, 12373879694170315045725⟩, ⟨.privateRow 10 12, 58074742031306011947936⟩, ⟨.privateRow 10 13, 299801428018755061679280⟩, ⟨.privateRow 10 14, 986864497455060203031360⟩, ⟨.privateRow 10 15, 1676248235903605344860880⟩, ⟨.privateRow 10 16, 2973330800693725157169120⟩, ⟨.privateRow 10 17, 6846220157190551908498728⟩, ⟨.privateRow 10 18, 15455800663331668179780240⟩, ⟨.privateRow 10 19, 35404144580960105408828370⟩, ⟨.privateRow 10 20, 47775903038611419829116960⟩, ⟨.privateRow 10 21, 86808540531795372859448880⟩, ⟨.privateRow 10 22, 38804486720918107983393600⟩, ⟨.privateRow 10 23, 224234498265876781132610160⟩, ⟨.privateRow 10 25, 160127902346319212943718080⟩, ⟨.privateRow 11 8, 3142572620741667313200⟩, ⟨.privateRow 11 9, 13309719334905885091200⟩, ⟨.privateRow 11 10, 53030912975015635910250⟩, ⟨.privateRow 11 11, 237578490128070048877920⟩, ⟨.privateRow 11 12, 739402443765932294977200⟩, ⟨.privateRow 11 13, 1440265205721450296311200⟩, ⟨.privateRow 11 14, 2347501747694025482960400⟩, ⟨.privateRow 11 15, 4144767598338191761809600⟩, ⟨.privateRow 11 16, 8320903785199786711890960⟩, ⟨.privateRow 11 17, 20967244525588404313670400⟩, ⟨.privateRow 11 18, 42594429301532558763112800⟩, ⟨.privateRow 11 19, 56437012756953783039571200⟩, ⟨.privateRow 11 21, 256234058233840882716000480⟩, ⟨.privateRow 11 25, 620758654920343027711022400⟩, ⟨.privateRow 12 6, 5458152446551316912400⟩, ⟨.privateRow 12 7, 17284149414079170222600⟩, ⟨.privateRow 12 8, 61002880284985306668000⟩, ⟨.privateRow 12 9, 233336017090068798005100⟩, ⟨.privateRow 12 10, 691365976563166808904000⟩, ⟨.privateRow 12 11, 1459276043388684228793800⟩, ⟨.privateRow 12 14, 21551763033046354433925600⟩, ⟨.privateRow 12 15, 5382284127544253607317640⟩, ⟨.privateRow 12 16, 32160040676463309394184400⟩, ⟨.privateRow 12 17, 61497003615293687652010800⟩, ⟨.privateRow 12 18, 81749088400190452532834400⟩, ⟨.privateRow 12 19, 29936146785185122825543200⟩, ⟨.privateRow 12 20, 46335347749263439532746080⟩, ⟨.privateRow 12 22, 495916814988759552026839200⟩, ⟨.privateRow 13 5, 26199131743446321179520⟩, ⟨.privateRow 13 6, 82963917187580017068480⟩, ⟨.privateRow 13 7, 292813825367929472006400⟩, ⟨.privateRow 13 8, 840009661524247672818360⟩, ⟨.privateRow 13 9, 1841798961564276378920256⟩, ⟨.privateRow 13 10, 2346693657591549054222720⟩, ⟨.privateRow 13 13, 47425191934136649756963840⟩, ⟨.privateRow 13 14, 10702345317197822201833920⟩, ⟨.privateRow 13 17, 480787752090195853199994240⟩, ⟨.privateRow 13 20, 32231481827374836631104480⟩, ⟨.privateRow 13 21, 235866416564289988525688640⟩, ⟨.privateRow 13 22, 107770128426666442171955520⟩, ⟨.privateRow 14 3, 40444909628945258320884⟩, ⟨.privateRow 14 4, 170294356332401087666880⟩, ⟨.privateRow 14 5, 494326673242664268366360⟩, ⟨.privateRow 14 6, 1332302905424079097629120⟩, ⟨.privateRow 14 7, 3033368222170894374066300⟩, ⟨.privateRow 14 8, 5338728071020774098356688⟩, ⟨.privateRow 14 9, 5835622675033530129156120⟩, ⟨.privateRow 14 12, 130379681403854441823504240⟩, ⟨.privateRow 14 13, 38665333605271666954765104⟩, ⟨.privateRow 14 14, 5392654617192701109451200⟩, ⟨.privateRow 14 17, 943040476181573606515278600⟩, ⟨.privateRow 14 20, 2294844172346353957126958160⟩, ⟨.privateRow 15 1, 179755153906423370315040⟩, ⟨.privateRow 15 2, 377485823203489077661584⟩, ⟨.privateRow 15 3, 1192060494326807613668160⟩, ⟨.privateRow 15 4, 3145715193362408980513200⟩, ⟨.privateRow 15 5, 7105615495595088520688640⟩, ⟨.privateRow 15 6, 13683861091126479065232420⟩, ⟨.privateRow 15 7, 21390863314864381067489760⟩, ⟨.privateRow 15 8, 23458047584788249826112720⟩, ⟨.privateRow 15 12, 13212003812122117718155440⟩, ⟨.privateRow 15 13, 1120713466221914239457502720⟩, ⟨.privateRow 15 16, 1480373569996349666229511920⟩, ⟨.privateRow 15 18, 4261814943967391686799283360⟩, ⟨.privateRow 15 20, 7219416368766728610277794000⟩, ⟨.privateRow 16 1, 9909002859091588288616580⟩, ⟨.privateRow 16 3, 42467155110392521236928200⟩, ⟨.privateRow 16 4, 44965223058062669544982800⟩, ⟨.privateRow 16 6, 326525237071018052177270160⟩, ⟨.privateRow 16 9, 141557183701308404123094000⟩, ⟨.privateRow 16 14, 355915204734718273223779200⟩, ⟨.privateRow 16 16, 1534479871322183100694338960⟩, ⟨.privateRow 16 20, 283878776194603873628452707600⟩, ⟨.privateRow 17 4, 4275026947779513804517438800⟩, ⟨.privateRow 17 9, 6671204002796206972491993600⟩, ⟨.privateRow 17 14, 2868892256346516990228038400⟩, ⟨.hall 14 8, 1511029345155787032576⟩, ⟨.hall 12 9, 70431867189862378200⟩, ⟨.hall 13 9, 694876994567226014544⟩, ⟨.hall 12 10, 140736830114517797160⟩, ⟨.hall 14 10, 4465761092632895655600⟩, ⟨.hall 16 16, 79190214799592631276622080⟩, ⟨.hall 12 20, 136496958613953288951600⟩, ⟨.hall 5 22, 421196693174445767040⟩, ⟨.hall 6 24, 5973499843479457167648⟩, ⟨.hall 4 28, 708303289430605280315904⟩, ⟨.hall 3 30, 27658308776361215851538640⟩, ⟨.hall 4 30, 28353838661646865369632630⟩, ⟨.hall 2 33, 26316313139389122375919192800⟩]
  caps := #[0, 0, 0, 6309254763554235242349600, 0, 1288848980506762228562190, 562222628168225122992660, 59297251136879403648000, 53393279196244811264280, 2510360952333637771368, 66969495857200106880675, 151020752587145653212900, 232263249413945939311980, 55407738914285250821328, 7174514007673451253016488, 4708875731271584221044696, 4996135895340296616109200, 0] }

theorem case_53_36_22_checked :
    (Witness.linear .conditional case_53_36_22).check 53 36 22 = true := by
  change case_53_36_22.check 53 36 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_36_23 : Certificate := {
  objectiveScale := 985
  eta := 34912800
  rows := #[⟨.assumptionRow 23, 383⟩]
  caps := #[0, 0, 14692860, 7607710, 3871406, 1595902, 916237, 432972, 206397, 115260, 49180, 28714, 29716, 79698312, 78947660, 55681970, 32878170, 16969128] }

theorem case_53_36_23_checked :
    (Witness.linear .conditional case_53_36_23).check 53 36 23 = true := by
  change case_53_36_23.check 53 36 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_37_1_checked :
    (Witness.rising).check 53 37 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_37_2_checked :
    (Witness.rising).check 53 37 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_37_3_checked :
    (Witness.rising).check 53 37 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_37_4_checked :
    (Witness.rising).check 53 37 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_37_5_checked :
    (Witness.rising).check 53 37 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_37_6_checked :
    (Witness.rising).check 53 37 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_37_7_checked :
    (Witness.rising).check 53 37 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_37_8_checked :
    (Witness.rising).check 53 37 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_37_9_checked :
    (Witness.rising).check 53 37 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_37_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_37_10_checked :
    (Witness.linear .positive case_53_37_10).check 53 37 10 = true := by
  change case_53_37_10.check 53 37 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_37_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_53_37_11_checked :
    (Witness.linear .positive case_53_37_11).check 53 37 11 = true := by
  change case_53_37_11.check 53 37 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_37_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_53_37_12_checked :
    (Witness.linear .positive case_53_37_12).check 53 37 12 = true := by
  change case_53_37_12.check 53 37 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_37_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_53_37_13_checked :
    (Witness.linear .positive case_53_37_13).check 53 37 13 = true := by
  change case_53_37_13.check 53 37 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_37_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_53_37_14_checked :
    (Witness.linear .positive case_53_37_14).check 53 37 14 = true := by
  change case_53_37_14.check 53 37 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_37_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_53_37_15_checked :
    (Witness.linear .positive case_53_37_15).check 53 37 15 = true := by
  change case_53_37_15.check 53 37 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_37_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_53_37_16_checked :
    (Witness.linear .positive case_53_37_16).check 53 37 16 = true := by
  change case_53_37_16.check 53 37 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_37_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_53_37_17_checked :
    (Witness.linear .positive case_53_37_17).check 53 37 17 = true := by
  change case_53_37_17.check 53 37 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_37_18 : Certificate := {
  objectiveScale := 1481055365790000
  eta := 1054901698940308605586200
  rows := #[⟨.count 2, 122060269492221474414000⟩, ⟨.count 3, 13371690579597961130520⟩, ⟨.count 4, 1389094742377230688800⟩, ⟨.count 5, 128619883553447286000⟩, ⟨.count 6, 12026794306296369600⟩, ⟨.count 7, 1403126002401243120⟩, ⟨.count 8, 623611556622774720⟩, ⟨.path 6, 5254445013283065600⟩, ⟨.privateRow 2 34, 9430409862138755009520⟩, ⟨.privateRow 2 35, 14847879357409954695840⟩, ⟨.privateRow 3 30, 650669616627810755976⟩, ⟨.privateRow 3 31, 1851207609715687723500⟩, ⟨.privateRow 3 32, 3740633699115828354840⟩, ⟨.privateRow 3 33, 4536055807548504499260⟩, ⟨.privateRow 3 34, 6864994413319853570760⟩, ⟨.privateRow 4 27, 212774035935559938840⟩, ⟨.privateRow 4 28, 380347369936622688600⟩, ⟨.privateRow 4 29, 864546108708114528696⟩, ⟨.privateRow 4 30, 1208567548675427890950⟩, ⟨.privateRow 4 31, 1595989012207490180280⟩, ⟨.privateRow 4 32, 2222551587803569102080⟩, ⟨.privateRow 5 23, 1506690064483239636⟩, ⟨.privateRow 5 24, 42954957935944934880⟩, ⟨.privateRow 5 25, 89436754742343523515⟩, ⟨.privateRow 5 26, 197339649909146264520⟩, ⟨.privateRow 5 27, 318916063648952389620⟩, ⟨.privateRow 5 28, 442893381881756197392⟩, ⟨.privateRow 5 29, 571256025668096588820⟩, ⟨.privateRow 5 30, 818634935035893535560⟩, ⟨.privateRow 5 31, 661841172227881605960⟩, ⟨.privateRow 6 21, 7288966246240224000⟩, ⟨.privateRow 6 22, 19627060152636436500⟩, ⟨.privateRow 6 23, 49313568629366441400⟩, ⟨.privateRow 6 24, 85168913151706409025⟩, ⟨.privateRow 6 25, 128572158179215951200⟩, ⟨.privateRow 6 26, 177450895621141342200⟩, ⟨.privateRow 6 27, 224767422479894374080⟩, ⟨.privateRow 6 28, 316371505779518389200⟩, ⟨.privateRow 6 29, 176504342365553202000⟩, ⟨.privateRow 7 18, 716981968259975880⟩, ⟨.privateRow 7 19, 3875300387584385760⟩, ⟨.privateRow 7 20, 12309241748338178280⟩, ⟨.privateRow 7 21, 24995687499919288152⟩, ⟨.privateRow 7 22, 40234081322822947560⟩, ⟨.privateRow 7 23, 58793485082759231805⟩, ⟨.privateRow 7 24, 79720465116021649920⟩, ⟨.privateRow 7 25, 100189878123841145640⟩, ⟨.privateRow 7 26, 92486048215419082224⟩, ⟨.privateRow 8 16, 439868865832135740⟩, ⟨.privateRow 8 17, 2890199714347859760⟩, ⟨.privateRow 8 18, 7639241568628990320⟩, ⟨.privateRow 8 19, 14172989923244880000⟩, ⟨.privateRow 8 20, 22060258815530655720⟩, ⟨.privateRow 8 21, 31449077251351319560⟩, ⟨.privateRow 8 22, 41976852905170523340⟩, ⟨.privateRow 8 23, 18830841825877000920⟩, ⟨.privateRow 9 14, 363773408029951920⟩, ⟨.privateRow 9 15, 2260591892757558360⟩, ⟨.privateRow 9 16, 5396638470774012000⟩, ⟨.privateRow 9 17, 9185278552756285980⟩, ⟨.privateRow 9 18, 15335175096950960160⟩, ⟨.privateRow 9 19, 13384263034016302428⟩, ⟨.privateRow 10 12, 350781500600310780⟩, ⟨.privateRow 10 13, 2024510374893222216⟩, ⟨.privateRow 10 14, 4595953538477541240⟩, ⟨.privateRow 10 15, 7755740430855222960⟩, ⟨.privateRow 11 10, 402858306011561400⟩, ⟨.privateRow 11 11, 2150624676299524425⟩, ⟨.privateRow 11 12, 2071281241639930320⟩, ⟨.privateRow 12 8, 571643926904210160⟩, ⟨.privateRow 12 9, 821437911769915440⟩, ⟨.privateRow 13 6, 406168053326675640⟩, ⟨.hall 4 32, 78975949278012827040⟩, ⟨.hall 3 33, 768865885416640851840⟩, ⟨.assumptionRow 18, 1658555317536975⟩]
  caps := #[0, 156150856023317555400, 49971303178326399870, 0, 0, 0, 2472664314636318075, 143304313140450000, 101952703336894410, 1355453937164565819, 72554711012623125, 2341021891490954100, 6811721221894875, 1658555317536975, 24972080869965329100, 6382045826781349725, 1345315054670311725] }

theorem case_53_37_18_checked :
    (Witness.linear .conditional case_53_37_18).check 53 37 18 = true := by
  change case_53_37_18.check 53 37 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_37_19 : Certificate := {
  objectiveScale := 18909726171336000000
  eta := 15928684586418393371037456000
  rows := #[⟨.count 2, 1609228452147964671098275200⟩, ⟨.count 3, 147080590969029382567702800⟩, ⟨.count 4, 11914520745220148333678400⟩, ⟨.count 5, 858041617454125908804000⟩, ⟨.count 6, 78003783404920537164000⟩, ⟨.count 7, 23401135021476161149200⟩, ⟨.count 8, 13867339271985873273600⟩, ⟨.path 5, 390920449343832600192000⟩, ⟨.path 6, 7796168671651027668000⟩, ⟨.privateRow 2 34, 130879948049002671956236800⟩, ⟨.privateRow 2 35, 214539005750779948064626800⟩, ⟨.privateRow 3 30, 8445581063227039302370800⟩, ⟨.privateRow 3 31, 23836191837252414383263500⟩, ⟨.privateRow 3 32, 51328594344434354166819600⟩, ⟨.privateRow 3 33, 65997701075846517818841000⟩, ⟨.privateRow 3 34, 105171386825091432821976000⟩, ⟨.privateRow 4 27, 2437538635706414826643200⟩, ⟨.privateRow 4 28, 4492460754241959222523800⟩, ⟨.privateRow 4 29, 11019705915589417028782800⟩, ⟨.privateRow 4 30, 16627620772521739932751800⟩, ⟨.privateRow 4 31, 23485824843458646303835200⟩, ⟨.privateRow 4 32, 34971324779951731683111600⟩, ⟨.privateRow 5 23, 2860138724847086362680⟩, ⟨.privateRow 5 24, 421756964346498925544400⟩, ⟨.privateRow 5 25, 952528343185681440428250⟩, ⟨.privateRow 5 26, 2293364295902898432442800⟩, ⟨.privateRow 5 27, 4063439945514896268121800⟩, ⟨.privateRow 5 28, 6105987586302122657698560⟩, ⟨.privateRow 5 29, 8539557049900586425716000⟩, ⟨.privateRow 5 30, 13299645070538951586462000⟩, ⟨.privateRow 5 31, 12462033015405162008820000⟩, ⟨.privateRow 6 21, 48288056393522237292000⟩, ⟨.privateRow 6 22, 179408701831317235477200⟩, ⟨.privateRow 6 23, 511770854085192942240000⟩, ⟨.privateRow 6 24, 982940532548909387953500⟩, ⟨.privateRow 6 25, 1627466691856403316204000⟩, ⟨.privateRow 6 26, 2446285318448757957171000⟩, ⟨.privateRow 6 27, 3384621306598266355420800⟩, ⟨.privateRow 6 28, 5249468899857330911763000⟩, ⟨.privateRow 6 29, 5439216198378030472404000⟩, ⟨.privateRow 6 30, 753107956445125662381000⟩, ⟨.privateRow 7 18, 1114339762927436245200⟩, ⟨.privateRow 7 19, 24051166549850498958900⟩, ⟨.privateRow 7 20, 108597475078019241350400⟩, ⟨.privateRow 7 21, 255406673662968387399840⟩, ⟨.privateRow 7 22, 457250749387891339280400⟩, ⟨.privateRow 7 23, 733653441417350837933550⟩, ⟨.privateRow 7 24, 1087913991406585614242400⟩, ⟨.privateRow 7 25, 1498044087962116792297200⟩, ⟨.privateRow 7 26, 2315820895315798004774640⟩, ⟨.privateRow 7 27, 1288733935825580017573800⟩, ⟨.privateRow 8 17, 16334125584791052654000⟩, ⟨.privateRow 8 18, 66014312992682750896200⟩, ⟨.privateRow 8 19, 141431102234174105262000⟩, ⟨.privateRow 8 20, 244498525539200928155160⟩, ⟨.privateRow 8 21, 382603742552776906361200⟩, ⟨.privateRow 8 22, 558377082873556178532300⟩, ⟨.privateRow 8 23, 763817999722150466293200⟩, ⟨.privateRow 8 24, 654942877699832806484400⟩, ⟨.privateRow 9 15, 11824383039952240157400⟩, ⟨.privateRow 9 16, 45002182733608002210000⟩, ⟨.privateRow 9 17, 92304477029155968977400⟩, ⟨.privateRow 9 18, 156243941911068106258800⟩, ⟨.privateRow 9 19, 239731627664455784217360⟩, ⟨.privateRow 9 20, 344757462456315460552000⟩, ⟨.privateRow 9 21, 103246674423457322107350⟩, ⟨.privateRow 10 13, 9954768548818430457120⟩, ⟨.privateRow 10 14, 35977255203085798773600⟩, ⟨.privateRow 10 15, 68831909971594715761200⟩, ⟨.privateRow 10 16, 133256463316739250988500⟩, ⟨.privateRow 10 17, 94921487078455251068400⟩, ⟨.privateRow 11 11, 9750472925615067145500⟩, ⟨.privateRow 11 12, 35163610296821321515200⟩, ⟨.privateRow 11 13, 70442192156484362643000⟩, ⟨.privateRow 12 9, 11777041808193885022800⟩, ⟨.privateRow 12 10, 26303061487433026371075⟩, ⟨.privateRow 13 7, 11576751981523920991800⟩, ⟨.privateRow 14 5, 2795624317519708474800⟩, ⟨.hall 4 32, 2803678843525429592923200⟩, ⟨.hall 3 33, 13708837186425688101795000⟩, ⟨.assumptionRow 19, 17064485939042518977⟩]
  caps := #[0, 1978164342233765077392000, 1868975917984923092244900, 82753702024586054467005, 3902651921285660595195, 9956359413661492105560, 10949779680623580375150, 3288936412899464949216, 0, 3844239259001999553234, 1514142329360559300630, 1000367516710451164275, 83477189462919113862, 17367370148943953254116, 142196935173463668359862, 261096675754668836907825, 68912551075841458745760] }

theorem case_53_37_19_checked :
    (Witness.linear .conditional case_53_37_19).check 53 37 19 = true := by
  change case_53_37_19.check 53 37 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_37_20 : Certificate := {
  objectiveScale := 6079126783970240000
  eta := 5527075078830752041560966000
  rows := #[⟨.count 2, 549695781805811222216194560⟩, ⟨.count 3, 48442578173981508451334400⟩, ⟨.count 4, 3618484078177970975413440⟩, ⟨.count 5, 183866060883026980458000⟩, ⟨.count 6, 6686038577564617471200⟩, ⟨.count 7, 1560075668098410743280⟩, ⟨.path 5, 147474800179214315808000⟩, ⟨.path 6, 626205492843776445600⟩, ⟨.privateRow 2 34, 47109344936956359479702280⟩, ⟨.privateRow 2 35, 79940877359476063836906000⟩, ⟨.privateRow 3 30, 2651593752681093094178304⟩, ⟨.privateRow 3 31, 8153438322046229766754200⟩, ⟨.privateRow 3 32, 18371352015103513585199040⟩, ⟨.privateRow 3 33, 24678094100473474590449520⟩, ⟨.privateRow 3 34, 40846866903280460525302800⟩, ⟨.privateRow 4 27, 750873970539447325908480⟩, ⟨.privateRow 4 28, 1434972457380423900818880⟩, ⟨.privateRow 4 29, 3735668047647420170958672⟩, ⟨.privateRow 4 30, 5933970671564890749314520⟩, ⟨.privateRow 4 31, 8793700805165570385371280⟩, ⟨.privateRow 4 32, 13762987543964179577216160⟩, ⟨.privateRow 5 23, 6292305194663589997896⟩, ⟨.privateRow 5 24, 123666950579102591300640⟩, ⟨.privateRow 5 25, 285298837803496864677330⟩, ⟨.privateRow 5 26, 723439986852138538348080⟩, ⟨.privateRow 5 27, 1363605186341382317292960⟩, ⟨.privateRow 5 28, 2160630510998770383693120⟩, ⟨.privateRow 5 29, 3198452276871856006722720⟩, ⟨.privateRow 5 30, 5296432130088261641519040⟩, ⟨.privateRow 5 31, 5453467365790580240384280⟩, ⟨.privateRow 6 20, 433354352249558539800⟩, ⟨.privateRow 6 21, 16917703673534713904400⟩, ⟨.privateRow 6 22, 50405301943084366157880⟩, ⟨.privateRow 6 23, 149899334035275868243200⟩, ⟨.privateRow 6 24, 305421956689028150871900⟩, ⟨.privateRow 6 25, 536793382941616431259200⟩, ⟨.privateRow 6 26, 854946229223771919234000⟩, ⟨.privateRow 6 27, 1258758196202831982577920⟩, ⟨.privateRow 6 28, 2095423062538133239411500⟩, ⟨.privateRow 6 29, 2413783742030041066686000⟩, ⟨.privateRow 6 30, 1238031476612381668417200⟩, ⟨.privateRow 7 18, 1422926158815033974640⟩, ⟨.privateRow 7 19, 7763233681727805841560⟩, ⟨.privateRow 7 20, 29681959139794438167600⟩, ⟨.privateRow 7 21, 73323556400625304934160⟩, ⟨.privateRow 7 22, 139044839307501211484400⟩, ⟨.privateRow 7 23, 236630048657641086668220⟩, ⟨.privateRow 7 24, 372985437791283303214800⟩, ⟨.privateRow 7 25, 548180874042770136888720⟩, ⟨.privateRow 7 26, 914293488686702890461696⟩, ⟨.privateRow 7 27, 1127210387189248133832060⟩, ⟨.privateRow 7 28, 2674415431025846988480⟩, ⟨.privateRow 8 15, 11556116059988227728⟩, ⟨.privateRow 8 16, 705748516520709621960⟩, ⟨.privateRow 8 17, 5346926007756091521840⟩, ⟨.privateRow 8 18, 17651967281632017854520⟩, ⟨.privateRow 8 19, 39758292026386770760560⟩, ⟨.privateRow 8 20, 72508850218396134879336⟩, ⟨.privateRow 8 21, 120145086637010940945440⟩, ⟨.privateRow 8 22, 186320703749697694187010⟩, ⟨.privateRow 8 23, 271973191471822939578480⟩, ⟨.privateRow 8 24, 454097580577237408571760⟩, ⟨.privateRow 8 25, 179651380268576988259488⟩, ⟨.privateRow 9 14, 520025222699470247760⟩, ⟨.privateRow 9 15, 4011623146538770482720⟩, ⟨.privateRow 9 16, 11987248082226250070160⟩, ⟨.privateRow 9 17, 25409010186899115716940⟩, ⟨.privateRow 9 18, 45147644334363098782800⟩, ⟨.privateRow 9 19, 73028875441095605127096⟩, ⟨.privateRow 9 20, 111131316110220123317600⟩, ⟨.privateRow 9 21, 160557787508461438995900⟩, ⟨.privateRow 9 22, 70574851652070962196000⟩, ⟨.privateRow 10 12, 487523646280753357275⟩, ⟨.privateRow 10 13, 3491597923839300234960⟩, ⟨.privateRow 10 14, 9758432495350263118680⟩, ⟨.privateRow 10 15, 19972397289391741933200⟩, ⟨.privateRow 10 16, 34823117591482382662500⟩, ⟨.privateRow 10 17, 55311773687125471807200⟩, ⟨.privateRow 10 18, 57187916633436028103664⟩, ⟨.privateRow 11 10, 546244981827174630000⟩, ⟨.privateRow 11 11, 3644819641241822718675⟩, ⟨.privateRow 11 12, 9880479231289934707440⟩, ⟨.privateRow 11 13, 19925456237107252860600⟩, ⟨.privateRow 11 14, 30144319227908852274000⟩, ⟨.privateRow 12 8, 771783465434928066120⟩, ⟨.privateRow 12 9, 4710816723277554009120⟩, ⟨.privateRow 12 10, 12819550356011047804155⟩, ⟨.privateRow 12 11, 4194870129775726665264⟩, ⟨.privateRow 13 6, 1290288146547557757600⟩, ⟨.privateRow 13 7, 6265065778236474889680⟩, ⟨.privateRow 14 4, 2655843101643723051060⟩, ⟨.hall 4 32, 1555023994506473032301760⟩, ⟨.hall 3 33, 5852853291763555316759520⟩, ⟨.assumptionRow 20, 3834627731380542096⟩]
  caps := #[0, 223322282067947253150960, 80880057905038073826144, 38867203021693725526848, 0, 2730118188329354109144, 3122080002738729247800, 2166676877638346895936, 486311679821273690384, 179455547946501829002, 28432522798454638864, 3831239002397787493150, 0, 21245185176754624957872, 0, 220563377180172686836176, 69470385035372103903120] }

theorem case_53_37_20_checked :
    (Witness.linear .conditional case_53_37_20).check 53 37 20 = true := by
  change case_53_37_20.check 53 37 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_37_21 : Certificate := {
  objectiveScale := 37819452342672000000
  eta := 50234475514660528393884582000
  rows := #[⟨.count 2, 5202477934947856210260412800⟩, ⟨.count 3, 483788379395420590981089600⟩, ⟨.count 4, 39567976302027406194561600⟩, ⟨.count 5, 2410688353799687077116000⟩, ⟨.count 6, 78003783404920537164000⟩, ⟨.path 5, 957463912475746419744000⟩, ⟨.path 6, 77037629900422755564000⟩, ⟨.privateRow 2 34, 452688456675172594053177000⟩, ⟨.privateRow 2 35, 774868783335572637377265600⟩, ⟨.privateRow 3 30, 24051315128485555950399360⟩, ⟨.privateRow 3 31, 77749806800619992319781500⟩, ⟨.privateRow 3 32, 176277159466432711309022400⟩, ⟨.privateRow 3 33, 239211788165050135208974200⟩, ⟨.privateRow 3 34, 400394906003807687177805600⟩, ⟨.privateRow 4 27, 7207549586614657633953600⟩, ⟨.privateRow 4 28, 13604045549111962920775800⟩, ⟨.privateRow 4 29, 35491052845381087947872880⟩, ⟨.privateRow 4 30, 56646068923712562229435500⟩, ⟨.privateRow 4 31, 84843972316356783315786000⟩, ⟨.privateRow 4 32, 134884142263788592863988800⟩, ⟨.privateRow 5 23, 141372571256727411641040⟩, ⟨.privateRow 5 24, 1253013155647294977936000⟩, ⟨.privateRow 5 25, 2769737911579598097288150⟩, ⟨.privateRow 5 26, 6843319675532089901236800⟩, ⟨.privateRow 5 27, 12844746816206129279254800⟩, ⟨.privateRow 5 28, 20436099780278838787971840⟩, ⟨.privateRow 5 29, 30627999830648227678070400⟩, ⟨.privateRow 5 30, 51758977123982772876632400⟩, ⟨.privateRow 5 31, 55016811328665739819266000⟩, ⟨.privateRow 6 20, 46430823455309843550000⟩, ⟨.privateRow 6 21, 204802141277421237186000⟩, ⟨.privateRow 6 22, 521696732343861402127800⟩, ⟨.privateRow 6 23, 1452562516897448838882000⟩, ⟨.privateRow 6 24, 2865710423661723543906000⟩, ⟨.privateRow 6 25, 5001793621597149546312000⟩, ⟨.privateRow 6 26, 7997245031942567453052000⟩, ⟨.privateRow 6 27, 11931607288251702356104800⟩, ⟨.privateRow 6 28, 20332521899314733588980500⟩, ⟨.privateRow 6 29, 24328513335290216424372000⟩, ⟨.privateRow 6 30, 15412247537755549467987000⟩, ⟨.privateRow 7 16, 222867952585487249040⟩, ⟨.privateRow 7 17, 10427036353106724865800⟩, ⟨.privateRow 7 18, 39259047032366600023200⟩, ⟨.privateRow 7 19, 98619069019078107700200⟩, ⟨.privateRow 7 20, 309786454093827276165600⟩, ⟨.privateRow 7 21, 707382881506336528452960⟩, ⟨.privateRow 7 22, 1296967668518321629830000⟩, ⟨.privateRow 7 23, 2182852303104481674816150⟩, ⟨.privateRow 7 24, 3449359140444526937284800⟩, ⟨.privateRow 7 25, 5134691904275804978507400⟩, ⟨.privateRow 7 26, 8775425633053560430950000⟩, ⟨.privateRow 7 27, 11253438680863446781213500⟩, ⟨.privateRow 7 28, 2512464718813726254177600⟩, ⟨.privateRow 8 13, 50982864970536298800⟩, ⟨.privateRow 8 14, 2383448937372571968900⟩, ⟨.privateRow 8 15, 9187112267690641043760⟩, ⟨.privateRow 8 16, 22843965140012443026600⟩, ⟨.privateRow 8 17, 69803385662351967872400⟩, ⟨.privateRow 8 18, 185186759861311349341200⟩, ⟨.privateRow 8 19, 384661081396789962055200⟩, ⟨.privateRow 8 20, 675512764286611851840240⟩, ⟨.privateRow 8 21, 1101490462451211239607200⟩, ⟨.privateRow 8 22, 1706116084806511971192600⟩, ⟨.privateRow 8 23, 2516055369160936882078800⟩, ⟨.privateRow 8 24, 4297286208357372333503400⟩, ⟨.privateRow 8 25, 3152566241745088465337040⟩, ⟨.privateRow 9 10, 45616247605216688400⟩, ⟨.privateRow 9 11, 625956286582695668600⟩, ⟨.privateRow 9 12, 2651108978467887537600⟩, ⟨.privateRow 9 13, 6933669635992936636800⟩, ⟨.privateRow 9 14, 20223203104979398524000⟩, ⟨.privateRow 9 15, 53302585326695700395400⟩, ⟨.privateRow 9 16, 127939538764138898134800⟩, ⟨.privateRow 9 17, 248745398191246601845200⟩, ⟨.privateRow 9 18, 423111431196387156132000⟩, ⟨.privateRow 9 19, 669619145096017855698960⟩, ⟨.privateRow 9 20, 903495673956746271200800⟩, ⟨.privateRow 9 21, 1686398461779157057631700⟩, ⟨.privateRow 9 22, 1237288583437096710920400⟩, ⟨.privateRow 10 8, 222867952585487249040⟩, ⟨.privateRow 10 9, 938391379307314732800⟩, ⟨.privateRow 10 10, 2662033878104431030200⟩, ⟨.privateRow 10 11, 7931477136130575627600⟩, ⟨.privateRow 10 12, 20197408203059781944250⟩, ⟨.privateRow 10 13, 48808081616221707539760⟩, ⟨.privateRow 10 14, 107454191425145637930000⟩, ⟨.privateRow 10 15, 199809691337219529812400⟩, ⟨.privateRow 10 16, 331144632883269804198600⟩, ⟨.privateRow 10 17, 511178040339258481207200⟩, ⟨.privateRow 10 18, 738250092939426512445000⟩, ⟨.privateRow 11 5, 84419679009654261000⟩, ⟨.privateRow 11 6, 353758654897598808000⟩, ⟨.privateRow 11 7, 1207201409838055932300⟩, ⟨.privateRow 11 8, 4007713182458323338000⟩, ⟨.privateRow 11 9, 10524319983203564538000⟩, ⟨.privateRow 11 10, 24908771171319163128000⟩, ⟨.privateRow 11 11, 55600911087733537651125⟩, ⟨.privateRow 11 12, 114157917935455135341600⟩, ⟨.privateRow 11 13, 205622218159229307150000⟩, ⟨.privateRow 11 14, 299585959340876128998000⟩, ⟨.privateRow 12 3, 177648368002924618800⟩, ⟨.privateRow 12 4, 742893175284957496800⟩, ⟨.privateRow 12 5, 2140239862130472788400⟩, ⟨.privateRow 12 6, 7763233681727805841560⟩, ⟨.privateRow 12 7, 17418889978392029727600⟩, ⟨.privateRow 12 8, 39043163545531655109600⟩, ⟨.privateRow 12 9, 81718249281345324648000⟩, ⟨.privateRow 12 10, 106999832652761534460975⟩, ⟨.privateRow 13 1, 1021478116016816558100⟩, ⟨.privateRow 13 2, 1598835312026321569200⟩, ⟨.privateRow 13 3, 5571698814637181226000⟩, ⟨.privateRow 13 5, 74159311222820882118060⟩, ⟨.privateRow 13 6, 5806296659464009909200⟩, ⟨.privateRow 14 0, 13279215508218615255300⟩, ⟨.privateRow 14 1, 16166001488266140310800⟩, ⟨.privateRow 15 0, 16166001488266140310800⟩, ⟨.hall 4 32, 16710639084859833933019200⟩, ⟨.hall 3 33, 58819113398168336983770000⟩, ⟨.assumptionRow 21, 4185174834424311728⟩]
  caps := #[0, 3800358912099127196538720, 0, 17532910697386225421280, 53784542560162896733680, 0, 7046130385083884653320, 4185174834424311728, 14810732746959416967140, 333911515829058895728, 60782168886951067920, 21394606075606535552570, 3769480609117787060640, 28019888661697163575344, 127314414531501880502820, 0, 1222530874880050066339008] }

theorem case_53_37_21_checked :
    (Witness.linear .conditional case_53_37_21).check 53 37 21 = true := by
  change case_53_37_21.check 53 37 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_37_22 : Certificate := {
  objectiveScale := 65002183713967500000
  eta := 88009328702269694466026280000
  rows := #[⟨.count 2, 9191341806168596735108448000⟩, ⟨.count 3, 860015113174270398394249200⟩, ⟨.count 4, 67368524707541085639811200⟩, ⟨.count 5, 3983764652465584576590000⟩, ⟨.count 6, 100290578663469262068000⟩, ⟨.path 5, 1743490644652661224320000⟩, ⟨.path 6, 114385673836076643000000⟩, ⟨.privateRow 2 35, 3822661209919876336312700400⟩, ⟨.privateRow 3 30, 26802768581788453031297520⟩, ⟨.privateRow 3 33, 1534147767664496620444809000⟩, ⟨.privateRow 4 27, 7685601344910527783144400⟩, ⟨.privateRow 4 28, 20439777101496499327581000⟩, ⟨.privateRow 4 29, 41377218341116391682268320⟩, ⟨.privateRow 4 30, 86030929887168324156298200⟩, ⟨.privateRow 4 32, 824492190211669585769763600⟩, ⟨.privateRow 5 24, 1412363741745918360999600⟩, ⟨.privateRow 5 25, 3380071085899645990752900⟩, ⟨.privateRow 5 26, 10307006041499969590245600⟩, ⟨.privateRow 5 27, 18733908647748415675554000⟩, ⟨.privateRow 5 28, 35535180699993014423182800⟩, ⟨.privateRow 5 29, 62796388660249814725755600⟩, ⟨.privateRow 5 30, 86596828763441640529485600⟩, ⟨.privateRow 6 20, 11607705863827460887500⟩, ⟨.privateRow 6 21, 191463831993895863948000⟩, ⟨.privateRow 6 22, 585585545418367746852600⟩, ⟨.privateRow 6 23, 1795944251251384748514000⟩, ⟨.privateRow 6 24, 4259563743790125047277000⟩, ⟨.privateRow 6 25, 7723170514060652776554000⟩, ⟨.privateRow 6 26, 13877244514323006040224000⟩, ⟨.privateRow 6 27, 23927103389577911056934400⟩, ⟨.privateRow 6 28, 48234196638314077873482000⟩, ⟨.privateRow 6 29, 63127347569839263290580000⟩, ⟨.privateRow 6 30, 53702819024880471246801000⟩, ⟨.privateRow 7 17, 2865445104670550344800⟩, ⟨.privateRow 7 18, 26229843650445807002400⟩, ⟨.privateRow 7 19, 91097275619317913045100⟩, ⟨.privateRow 7 20, 343115343366838778408400⟩, ⟨.privateRow 7 21, 869519317012278502129560⟩, ⟨.privateRow 7 22, 1860575957501176050735600⟩, ⟨.privateRow 7 23, 3366838301214882685341150⟩, ⟨.privateRow 7 24, 5829748065452234676495600⟩, ⟨.privateRow 7 25, 9799503875183874340288800⟩, ⟨.privateRow 7 26, 19674337118341643370753120⟩, ⟨.privateRow 7 27, 31726924560188501055211800⟩, ⟨.privateRow 7 28, 40395930745882491324745200⟩, ⟨.privateRow 7 29, 36982150882154290387575000⟩, ⟨.privateRow 8 14, 650031528374337809700⟩, ⟨.privateRow 8 15, 4333543522495585398000⟩, ⟨.privateRow 8 16, 15229310093341628684400⟩, ⟨.privateRow 8 17, 64003104332242492032000⟩, ⟨.privateRow 8 18, 202809836852793396626400⟩, ⟨.privateRow 8 19, 463767948607436648229600⟩, ⟨.privateRow 8 20, 922784757680209954650120⟩, ⟨.privateRow 8 21, 1637501645700331869057600⟩, ⟨.privateRow 8 22, 2735657687163400672122450⟩, ⟨.privateRow 8 23, 4401270616975730689791600⟩, ⟨.privateRow 8 24, 8547914598122542197555000⟩, ⟨.privateRow 8 25, 13873232891176467269741280⟩, ⟨.privateRow 8 26, 19369639482498518053440600⟩, ⟨.privateRow 8 27, 20634600836714979431116800⟩, ⟨.privateRow 9 11, 144451450749852846600⟩, ⟨.privateRow 9 12, 917691569469653378400⟩, ⟨.privateRow 9 13, 3250157641871689048500⟩, ⟨.privateRow 9 14, 13347314049286403025840⟩, ⟨.privateRow 9 15, 48473779687343476666200⟩, ⟨.privateRow 9 16, 137606674314321357868800⟩, ⟨.privateRow 9 17, 292947542120701572904800⟩, ⟨.privateRow 9 18, 550990360960211430694800⟩, ⟨.privateRow 9 19, 952426195374079758772440⟩, ⟨.privateRow 9 20, 1556897736181913980654800⟩, ⟨.privateRow 9 21, 2456469145726622582856300⟩, ⟨.privateRow 9 22, 4624510016148860417580000⟩, ⟨.privateRow 9 23, 7743608920347361547686200⟩, ⟨.privateRow 9 24, 11774931117584104820029680⟩, ⟨.privateRow 9 25, 4335710294256833190699000⟩, ⟨.privateRow 10 9, 351896767240243024800⟩, ⟨.privateRow 10 10, 928616469106196871000⟩, ⟨.privateRow 10 11, 3736315675697874469200⟩, ⟨.privateRow 10 12, 13372077155129234942400⟩, ⟨.privateRow 10 13, 43682118706755500811840⟩, ⟨.privateRow 10 14, 112707507450374980228800⟩, ⟨.privateRow 10 15, 228868243616634982668000⟩, ⟨.privateRow 10 16, 412027127342419551662700⟩, ⟨.privateRow 10 17, 689269795178025110212800⟩, ⟨.privateRow 10 18, 1096176024791719034403240⟩, ⟨.privateRow 10 19, 1680052915906931379013200⟩, ⟨.privateRow 10 20, 3041311797969705372212100⟩, ⟨.privateRow 10 21, 5014051358989351345009200⟩, ⟨.privateRow 10 22, 7843837591246223729962800⟩, ⟨.privateRow 10 23, 11169027443821693485639600⟩, ⟨.privateRow 11 7, 278584940731859061300⟩, ⟨.privateRow 11 8, 1466236530167679270000⟩, ⟨.privateRow 11 9, 4952621168566383312000⟩, ⟨.privateRow 11 10, 16059602465718934122000⟩, ⟨.privateRow 11 11, 48055902276245688074250⟩, ⟨.privateRow 11 12, 115891335344453369500800⟩, ⟨.privateRow 11 13, 228439651400124430266000⟩, ⟨.privateRow 11 14, 399019353571324286262000⟩, ⟨.privateRow 11 15, 648638603670678514393500⟩, ⟨.privateRow 11 16, 1004931858930924322944000⟩, ⟨.privateRow 11 17, 1501015660663256622284400⟩, ⟨.privateRow 11 18, 2597030725266997249230000⟩, ⟨.privateRow 11 19, 4184345809792523100726000⟩, ⟨.privateRow 11 20, 5968881344423460287682000⟩, ⟨.privateRow 11 22, 24866491809725739811638000⟩, ⟨.privateRow 12 5, 583701780581038033200⟩, ⟨.privateRow 12 6, 2451547478440359739440⟩, ⟨.privateRow 12 7, 8386872952559125424400⟩, ⟨.privateRow 12 8, 24515474784403597394400⟩, ⟨.privateRow 12 9, 67778077345115828090400⟩, ⟨.privateRow 12 10, 154753934576547708552150⟩, ⟨.privateRow 12 11, 299088792369723888211680⟩, ⟨.privateRow 12 13, 1848089637593501957424000⟩, ⟨.privateRow 12 15, 3282844941584227178359200⟩, ⟨.privateRow 12 16, 2298325761037837255725000⟩, ⟨.privateRow 12 17, 4719228895997692498422000⟩, ⟨.privateRow 12 20, 45600826055222724786700200⟩, ⟨.privateRow 12 22, 18398863825694899844497200⟩, ⟨.privateRow 13 3, 1671509644391154367800⟩, ⟨.privateRow 13 4, 7004421366972456398400⟩, ⟨.privateRow 13 5, 18386606088302698045800⟩, ⟨.privateRow 13 6, 50321237715354752546400⟩, ⟨.privateRow 13 7, 126663286386085253204400⟩, ⟨.privateRow 13 8, 276880656388558276454400⟩, ⟨.privateRow 13 9, 530913250799740406072475⟩, ⟨.privateRow 13 10, 522179612907796624500720⟩, ⟨.privateRow 13 13, 11096316774290678270640300⟩, ⟨.privateRow 13 14, 3028775475636771714453600⟩, ⟨.privateRow 13 15, 5762362348074065567553720⟩, ⟨.privateRow 13 16, 11215829713864645807938000⟩, ⟨.privateRow 13 18, 4764757634883013465011600⟩, ⟨.privateRow 13 19, 65940498301349576091587400⟩, ⟨.privateRow 13 24, 435578698231890916705002000⟩, ⟨.privateRow 14 3, 128998093508409405337200⟩, ⟨.privateRow 14 4, 95610351659174029838160⟩, ⟨.privateRow 14 5, 335474918102365016976000⟩, ⟨.privateRow 14 7, 2783948474781832045287600⟩, ⟨.privateRow 14 8, 1225007630633167257301425⟩, ⟨.privateRow 14 9, 1572259116173084046227520⟩, ⟨.privateRow 14 14, 27599521512281569946615520⟩, ⟨.privateRow 14 15, 10552549923864392922878400⟩, ⟨.privateRow 14 16, 38582760659129186624274150⟩, ⟨.privateRow 14 18, 362947518270631192157859600⟩, ⟨.privateRow 15 6, 1443528838775764764223200⟩, ⟨.privateRow 15 7, 7389883430323659389574450⟩, ⟨.privateRow 15 9, 23026159691251078852690200⟩, ⟨.privateRow 15 11, 41364756308100986520259500⟩, ⟨.privateRow 15 12, 41373206717969852911785600⟩, ⟨.privateRow 15 13, 63246247622543620737942840⟩, ⟨.privateRow 15 14, 89112388870485720773233200⟩, ⟨.privateRow 15 15, 129113812386409596127281900⟩, ⟨.privateRow 15 16, 190583300973953566144065600⟩, ⟨.privateRow 15 17, 1043321404049720163378410400⟩, ⟨.privateRow 15 19, 1629399580504948747671075900⟩, ⟨.privateRow 16 5, 12794914707330642228342000⟩, ⟨.hall 15 5, 4422169374985720678320000⟩, ⟨.hall 13 9, 17427964895023758075⟩, ⟨.hall 15 10, 166504095381688519455000⟩, ⟨.hall 7 17, 705439240945575136⟩, ⟨.hall 13 21, 54796446603083930144400⟩, ⟨.hall 6 25, 100751748338038644000⟩, ⟨.hall 5 26, 176883426432101424750⟩, ⟨.hall 3 31, 328713842714138877095100⟩, ⟨.hall 2 33, 9328570781491175930876160⟩]
  caps := #[0, 0, 0, 228035744989923043293120, 62544140078397417039600, 0, 73707448507567525521000, 18617935312420723538100, 0, 9180681042516956481600, 34646894747224441701120, 168914379915488862796500, 60526840972589555451030, 55986932770007149336140, 0, 46753339921043636870049060, 0] }

theorem case_53_37_22_checked :
    (Witness.linear .conditional case_53_37_22).check 53 37 22 = true := by
  change case_53_37_22.check 53 37 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_37_23 : Certificate := {
  objectiveScale := 13
  eta := 416520
  rows := #[⟨.assumptionRow 23, 5⟩]
  caps := #[0, 0, 161460, 93610, 46046, 20020, 11305, 5130, 2601, 1428, 580, 364, 3714500, 3684784, 2615008, 1563320, 823650] }

theorem case_53_37_23_checked :
    (Witness.linear .conditional case_53_37_23).check 53 37 23 = true := by
  change case_53_37_23.check 53 37 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_37_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208012, 208012, 149226, 90440] }

theorem case_53_37_24_checked :
    (Witness.linear .negative case_53_37_24).check 53 37 24 = true := by
  change case_53_37_24.check 53 37 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_38_1_checked :
    (Witness.rising).check 53 38 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_38_2_checked :
    (Witness.rising).check 53 38 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_38_3_checked :
    (Witness.rising).check 53 38 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_38_4_checked :
    (Witness.rising).check 53 38 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_38_5_checked :
    (Witness.rising).check 53 38 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_38_6_checked :
    (Witness.rising).check 53 38 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_38_7_checked :
    (Witness.rising).check 53 38 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_38_8_checked :
    (Witness.rising).check 53 38 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_38_9_checked :
    (Witness.rising).check 53 38 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_38_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_53_38_10_checked :
    (Witness.linear .positive case_53_38_10).check 53 38 10 = true := by
  change case_53_38_10.check 53 38 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_38_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_53_38_11_checked :
    (Witness.linear .positive case_53_38_11).check 53 38 11 = true := by
  change case_53_38_11.check 53 38 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_38_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_53_38_12_checked :
    (Witness.linear .positive case_53_38_12).check 53 38 12 = true := by
  change case_53_38_12.check 53 38 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_38_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_53_38_13_checked :
    (Witness.linear .positive case_53_38_13).check 53 38 13 = true := by
  change case_53_38_13.check 53 38 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_38_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_53_38_14_checked :
    (Witness.linear .positive case_53_38_14).check 53 38 14 = true := by
  change case_53_38_14.check 53 38 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_38_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_53_38_15_checked :
    (Witness.linear .positive case_53_38_15).check 53 38 15 = true := by
  change case_53_38_15.check 53 38 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_38_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_53_38_16_checked :
    (Witness.linear .positive case_53_38_16).check 53 38 16 = true := by
  change case_53_38_16.check 53 38 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_38_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_53_38_17_checked :
    (Witness.linear .positive case_53_38_17).check 53 38 17 = true := by
  change case_53_38_17.check 53 38 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_38_18 : Certificate := {
  objectiveScale := 17
  eta := 589294500
  rows := #[⟨.assumptionRow 18, 45⟩]
  caps := #[0, 0, 164812365, 46468395, 13223620, 3803648, 1107890, 327522, 98566, 30316, 9581, 3135, 1074, 285890, 154836, 52118] }

theorem case_53_38_18_checked :
    (Witness.linear .conditional case_53_38_18).check 53 38 18 = true := by
  change case_53_38_18.check 53 38 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_38_19 : Certificate := {
  objectiveScale := 211572195471000000
  eta := 436994453387441845559664000
  rows := #[⟨.count 2, 36888541613234697892746240⟩, ⟨.count 3, 2817253618908049993351680⟩, ⟨.count 4, 175824269866916539989120⟩, ⟨.count 5, 9701286566487775459200⟩, ⟨.count 6, 831538848556095039360⟩, ⟨.count 7, 215584145921950565760⟩, ⟨.path 4, 41400876646107942163200⟩, ⟨.path 5, 5101071101550132508800⟩, ⟨.privateRow 2 35, 2781174072201254980810560⟩, ⟨.privateRow 2 36, 4234519193066518866269760⟩, ⟨.privateRow 3 31, 294327795106699595265024⟩, ⟨.privateRow 3 32, 536873818249703249995680⟩, ⟨.privateRow 3 33, 1095598629575352775192320⟩, ⟨.privateRow 3 34, 1284126965184098544949440⟩, ⟨.privateRow 3 35, 1892397632902882066241280⟩, ⟨.privateRow 4 27, 16451765135668852549560⟩, ⟨.privateRow 4 28, 71251660146316508670240⟩, ⟨.privateRow 4 29, 116496282852574036972560⟩, ⟨.privateRow 4 30, 253115805840205573897632⟩, ⟨.privateRow 4 31, 354125832553489779783000⟩, ⟨.privateRow 4 32, 464545337292888835183200⟩, ⟨.privateRow 4 33, 636346653008226119079120⟩, ⟨.privateRow 5 24, 5229455425363886580864⟩, ⟨.privateRow 5 25, 14423605953349549756800⟩, ⟨.privateRow 5 26, 27244446440886502747920⟩, ⟨.privateRow 5 27, 59778403890643721162880⟩, ⟨.privateRow 5 28, 95380585702897271736960⟩, ⟨.privateRow 5 29, 133341874026239595644928⟩, ⟨.privateRow 5 30, 172659802582133622756000⟩, ⟨.privateRow 5 31, 247151824431950470032000⟩, ⟨.privateRow 5 32, 173052473705062889857920⟩, ⟨.privateRow 6 21, 1054822428260972411040⟩, ⟨.privateRow 6 22, 3208564041903316212480⟩, ⟨.privateRow 6 23, 6291977287407785797824⟩, ⟨.privateRow 6 24, 15296208448747921094400⟩, ⟨.privateRow 6 25, 26557271975760285319560⟩, ⟨.privateRow 6 26, 40138248229509285947520⟩, ⟨.privateRow 6 27, 55913288131614464591040⟩, ⟨.privateRow 6 28, 71660170104456368058624⟩, ⟨.privateRow 6 29, 102209983468353348588000⟩, ⟨.privateRow 6 30, 23452475302795050832320⟩, ⟨.privateRow 7 18, 169387543224389730240⟩, ⟨.privateRow 7 19, 750990925903937685120⟩, ⟨.privateRow 7 20, 1639979395763409660960⟩, ⟨.privateRow 7 21, 4101698360722825699200⟩, ⟨.privateRow 7 22, 8179878450981438609408⟩, ⟨.privateRow 7 23, 13260135959485054640000⟩, ⟨.privateRow 7 24, 19514214922827989604240⟩, ⟨.privateRow 7 25, 26767631505900964124160⟩, ⟨.privateRow 7 26, 34200884863760871896640⟩, ⟨.privateRow 7 27, 16846361117043851352960⟩, ⟨.privateRow 8 15, 25263767100228581925⟩, ⟨.privateRow 8 16, 170670782188210864560⟩, ⟨.privateRow 8 17, 477364894541461967040⟩, ⟨.privateRow 8 18, 1293504875531703394560⟩, ⟨.privateRow 8 19, 2755434865064930668620⟩, ⟨.privateRow 8 20, 5046628870445660971200⟩, ⟨.privateRow 8 21, 7887684938919366324744⟩, ⟨.privateRow 8 22, 11342121454893732543040⟩, ⟨.privateRow 8 23, 14646247913572516561320⟩, ⟨.privateRow 9 12, 5132955855284537280⟩, ⟨.privateRow 9 13, 39855892523385818880⟩, ⟨.privateRow 9 14, 142439524984145909520⟩, ⟨.privateRow 9 15, 478391485712518874496⟩, ⟨.privateRow 9 16, 1126317170531007037440⟩, ⟨.privateRow 9 17, 2215067872934327241600⟩, ⟨.privateRow 9 18, 3818919156331695736320⟩, ⟨.privateRow 9 19, 5831971116304195175040⟩, ⟨.privateRow 9 20, 1370499213360971453760⟩, ⟨.privateRow 10 9, 2309830134878041776⟩, ⟨.privateRow 10 10, 9725600567907544320⟩, ⟨.privateRow 10 11, 43630124769918566880⟩, ⟨.privateRow 10 12, 190221305225250499200⟩, ⟨.privateRow 10 13, 560133807707925130680⟩, ⟨.privateRow 10 14, 1213430764189264612992⟩, ⟨.privateRow 10 15, 2243834988167240582400⟩, ⟨.privateRow 10 16, 781788661035644908800⟩, ⟨.privateRow 11 7, 4399676447386746240⟩, ⟨.privateRow 11 8, 13858980809268250656⟩, ⟨.privateRow 11 9, 77804804543260354560⟩, ⟨.privateRow 11 10, 302844395461787699520⟩, ⟨.privateRow 11 11, 820669059686080725120⟩, ⟨.privateRow 11 12, 421543999615242624120⟩, ⟨.privateRow 12 5, 11549150674390208880⟩, ⟨.privateRow 12 6, 36297330690940656480⟩, ⟨.privateRow 12 7, 177856920385609216752⟩, ⟨.privateRow 12 8, 280826716398330342240⟩, ⟨.privateRow 13 3, 44188054754188625280⟩, ⟨.privateRow 13 4, 92393205395121671040⟩, ⟨.hall 3 34, 168651917322386666268672⟩, ⟨.assumptionRow 19, 203041604549609280⟩]
  caps := #[0, 13116502216583650684800, 10953337092431938652448, 130088993833792603584, 0, 248374635964130964288, 32725377867531323520, 0, 205579946595852881143, 485399755415916727488, 0, 27793027255323552768, 355965931593714622752, 1064540836265064238080, 13011546355482887372160, 3807374287878541860480] }

theorem case_53_38_19_checked :
    (Witness.linear .conditional case_53_38_19).check 53 38 19 = true := by
  change case_53_38_19.check 53 38 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_38_20 : Certificate := {
  objectiveScale := 293973997917600000
  eta := 681341404890007211902231680
  rows := #[⟨.count 2, 53945528440844294948453760⟩, ⟨.count 3, 3677064788315052264049920⟩, ⟨.count 4, 181922221422994570277760⟩, ⟨.count 5, 6467524377658516972800⟩, ⟨.count 6, 554359232370730026240⟩, ⟨.path 4, 99690119461559702275200⟩, ⟨.path 5, 3190391159331877300800⟩, ⟨.privateRow 2 35, 4300580334924030861063360⟩, ⟨.privateRow 2 36, 6797691497137984264261440⟩, ⟨.privateRow 3 31, 408359489205358761662592⟩, ⟨.privateRow 3 32, 784349018900536645876320⟩, ⟨.privateRow 3 33, 1687438705601370492650880⟩, ⟨.privateRow 3 34, 2082958619030320512761280⟩, ⟨.privateRow 3 35, 3208538843756390270206080⟩, ⟨.privateRow 4 27, 21025228802727375266040⟩, ⟨.privateRow 4 28, 93320437206408427810080⟩, ⟨.privateRow 4 29, 158843168658671469532560⟩, ⟨.privateRow 4 30, 367960560146341811000352⟩, ⟨.privateRow 4 31, 547862835116385533745000⟩, ⟨.privateRow 4 32, 760465375305897693912480⟩, ⟨.privateRow 4 33, 1106524126113325912792800⟩, ⟨.privateRow 5 23, 8399382308647424640⟩, ⟨.privateRow 5 24, 6301216607947297964928⟩, ⟨.privateRow 5 25, 17636836318757670094080⟩, ⟨.privateRow 5 26, 34520411365752334342320⟩, ⟨.privateRow 5 27, 80725263456652020011520⟩, ⟨.privateRow 5 28, 138374223946760555994240⟩, ⟨.privateRow 5 29, 205907497543568156079744⟩, ⟨.privateRow 5 30, 285102333547996696411680⟩, ⟨.privateRow 5 31, 439329691653803545795200⟩, ⟨.privateRow 5 32, 381399151871062258053120⟩, ⟨.privateRow 6 21, 1251157989725605962000⟩, ⟨.privateRow 6 22, 3683129142341895704640⟩, ⟨.privateRow 6 23, 7372977790530709348992⟩, ⟨.privateRow 6 24, 19038133267250348771520⟩, ⟨.privateRow 6 25, 35565609501784648245960⟩, ⟨.privateRow 6 26, 57587365019845121535360⟩, ⟨.privateRow 6 27, 85740894606672910725120⟩, ⟨.privateRow 6 28, 118060037853886471254912⟩, ⟨.privateRow 6 29, 183181078846503103045680⟩, ⟨.privateRow 6 30, 136095191547014221441920⟩, ⟨.privateRow 7 18, 224383498816724058240⟩, ⟨.privateRow 7 19, 843384131299059356160⟩, ⟨.privateRow 7 20, 1806800461060157122560⟩, ⟨.privateRow 7 21, 4695254710533910373760⟩, ⟨.privateRow 7 22, 10040061652936554919680⟩, ⟨.privateRow 7 23, 17469159760818375209600⟩, ⟨.privateRow 7 24, 27494678038831623940320⟩, ⟨.privateRow 7 25, 40380230434115556990720⟩, ⟨.privateRow 7 26, 55476986883915278922240⟩, ⟨.privateRow 7 27, 86492359343886566982912⟩, ⟨.privateRow 7 28, 1154915067439020888000⟩, ⟨.privateRow 8 15, 45474780780411447465⟩, ⟨.privateRow 8 16, 208398007724552213568⟩, ⟨.privateRow 8 17, 525486355684754504040⟩, ⟨.privateRow 8 18, 1397151099532641166560⟩, ⟨.privateRow 8 19, 3108004770374787323040⟩, ⟨.privateRow 8 20, 6092701942135125648240⟩, ⟨.privateRow 8 21, 10162097678395944793512⟩, ⟨.privateRow 8 22, 15584937215607676316400⟩, ⟨.privateRow 8 23, 22501595230603590301200⟩, ⟨.privateRow 8 24, 30709191643203565411920⟩, ⟨.privateRow 8 25, 1405788284866052647560⟩, ⟨.privateRow 9 12, 11976896995663920320⟩, ⟨.privateRow 9 13, 59783838785078728320⟩, ⟨.privateRow 9 14, 173237260115853133200⟩, ⟨.privateRow 9 15, 521508314896908987648⟩, ⟨.privateRow 9 16, 1205511346583968469760⟩, ⟨.privateRow 9 17, 2468556923633763621120⟩, ⟨.privateRow 9 18, 4519567630578035075040⟩, ⟨.privateRow 9 19, 7321461579037671811200⟩, ⟨.privateRow 9 20, 10963993706887771630080⟩, ⟨.privateRow 9 21, 6029512144674236458240⟩, ⟨.privateRow 10 9, 4619660269756083552⟩, ⟨.privateRow 10 10, 21882601277791974720⟩, ⟨.privateRow 10 11, 69294904046341253280⟩, ⟨.privateRow 10 12, 230983013487804177600⟩, ⟨.privateRow 10 13, 606330410405485966200⟩, ⟨.privateRow 10 14, 1293504875531703394560⟩, ⟨.privateRow 10 15, 2474818001655044760000⟩, ⟨.privateRow 10 16, 4296284050873157703360⟩, ⟨.privateRow 10 17, 2760247011179259922320⟩, ⟨.privateRow 11 7, 8799352894773492480⟩, ⟨.privateRow 11 8, 32337621888292584864⟩, ⟨.privateRow 11 9, 121570007098844304000⟩, ⟨.privateRow 11 10, 369572821580486684160⟩, ⟨.privateRow 11 11, 891322687341173767680⟩, ⟨.privateRow 11 12, 1795892929867677480840⟩, ⟨.privateRow 11 13, 825379301529753594624⟩, ⟨.privateRow 12 5, 23098301348780417760⟩, ⟨.privateRow 12 6, 84693771612194865120⟩, ⟨.privateRow 12 7, 279489446320243054896⟩, ⟨.privateRow 12 8, 762243944509753786080⟩, ⟨.privateRow 12 9, 197618800428454685280⟩, ⟨.privateRow 13 3, 88376109508377250560⟩, ⟨.privateRow 13 4, 277179616185365013120⟩, ⟨.privateRow 13 5, 48396440921254208640⟩, ⟨.hall 4 33, 26215213307257022368320⟩, ⟨.hall 3 34, 334777540428683862846336⟩, ⟨.assumptionRow 20, 210465672888686670⟩]
  caps := #[0, 14712445279021772842560, 12857476427016267350304, 724608521405457265044, 1682011040691569542812, 0, 0, 578558542494812922732, 3313525545547002877, 848742770941909373664, 0, 518910876661244041260, 171127659508950630486, 0, 42795647603890807986360, 14565576218256547504020] }

theorem case_53_38_20_checked :
    (Witness.linear .conditional case_53_38_20).check 53 38 20 = true := by
  change case_53_38_20.check 53 38 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_38_21 : Certificate := {
  objectiveScale := 762154809416000000
  eta := 2354798947367408188413967200
  rows := #[⟨.count 2, 188637590574125501133124800⟩, ⟨.count 3, 12992448034168753283733600⟩, ⟨.count 4, 659341012000937024959200⟩, ⟨.count 5, 16168810944146292432000⟩, ⟨.path 4, 310706043737573469585600⟩, ⟨.path 5, 15887772749504768112000⟩, ⟨.privateRow 2 35, 15309669625478404793416800⟩, ⟨.privateRow 2 36, 24549971842797895065171600⟩, ⟨.privateRow 3 31, 1411929866546900596415520⟩, ⟨.privateRow 3 32, 2734550150928741707562000⟩, ⟨.privateRow 3 33, 5984038433259628195053600⟩, ⟨.privateRow 3 34, 7536687001340190559866000⟩, ⟨.privateRow 3 35, 11838918864810659220799200⟩, ⟨.privateRow 4 27, 83648332868856834753675⟩, ⟨.privateRow 4 28, 320913774971279079103800⟩, ⟨.privateRow 4 29, 542992943248684329000600⟩, ⟨.privateRow 4 30, 1273010907659997968902440⟩, ⟨.privateRow 4 31, 1931653196045134386224400⟩, ⟨.privateRow 4 32, 2743019528089961194074000⟩, ⟨.privateRow 4 33, 4104683641185024138040800⟩, ⟨.privateRow 5 23, 3149768365742784240000⟩, ⟨.privateRow 5 24, 25003911210054802225200⟩, ⟨.privateRow 5 25, 62018939121475421685600⟩, ⟨.privateRow 5 26, 117108387838316718043200⟩, ⟨.privateRow 5 27, 272856934075807534939200⟩, ⟨.privateRow 5 28, 473707663494571734228000⟩, ⟨.privateRow 5 29, 718888432878092941944480⟩, ⟨.privateRow 5 30, 1022937148107426776023800⟩, ⟨.privateRow 5 31, 1633203894034434071750400⟩, ⟨.privateRow 5 32, 1509704976156288104793600⟩, ⟨.privateRow 6 19, 32997573355400596800⟩, ⟨.privateRow 6 20, 1159357048467632506800⟩, ⟨.privateRow 6 21, 6149922734112786228600⟩, ⟨.privateRow 6 22, 13816983897725013532800⟩, ⟨.privateRow 6 23, 25679536524506629444680⟩, ⟨.privateRow 6 24, 63847554644920538091600⟩, ⟨.privateRow 6 25, 118732487151902841166950⟩, ⟨.privateRow 6 26, 194636186436830420224800⟩, ⟨.privateRow 6 27, 295860367401191175983400⟩, ⟨.privateRow 6 28, 419499799945875557148240⟩, ⟨.privateRow 6 29, 677761907326589408122800⟩, ⟨.privateRow 6 30, 661670090720272383750000⟩, ⟨.privateRow 7 16, 12030365285823134250⟩, ⟨.privateRow 7 17, 395237600856909370560⟩, ⟨.privateRow 7 18, 1666377454447730138400⟩, ⟨.privateRow 7 19, 3781606515691358138400⟩, ⟨.privateRow 7 20, 6830039384937987418200⟩, ⟨.privateRow 7 21, 16245805281975560491200⟩, ⟨.privateRow 7 22, 33326999129398679424720⟩, ⟨.privateRow 7 23, 57702978739823673256000⟩, ⟨.privateRow 7 24, 91724317085229904775700⟩, ⟨.privateRow 7 25, 137451391811921185970400⟩, ⟨.privateRow 7 26, 194404286824082743808400⟩, ⟨.privateRow 7 27, 315953964716184407733120⟩, ⟨.privateRow 7 28, 125086926095874620677800⟩, ⟨.privateRow 8 13, 5614170466717462650⟩, ⟨.privateRow 8 14, 150591866636656645200⟩, ⟨.privateRow 8 15, 564224131905104996325⟩, ⟨.privateRow 8 16, 1311470221025199275040⟩, ⟨.privateRow 8 17, 2406073057164626850000⟩, ⟨.privateRow 8 18, 5296322046447920149200⟩, ⟨.privateRow 8 19, 10703415994796842542225⟩, ⟨.privateRow 8 20, 20146705909382283695100⟩, ⟨.privateRow 8 21, 33314487549501423365100⟩, ⟨.privateRow 8 22, 51407087573576232998500⟩, ⟨.privateRow 8 23, 75479714839782926597925⟩, ⟨.privateRow 8 24, 105722850131813703789000⟩, ⟨.privateRow 8 25, 70059233254167216409350⟩, ⟨.privateRow 9 10, 3849716891463402960⟩, ⟨.privateRow 9 11, 66863503904364367200⟩, ⟨.privateRow 9 12, 245954134732384078000⟩, ⟨.privateRow 9 13, 588780230459108688000⟩, ⟨.privateRow 9 14, 1123636117695880738950⟩, ⟨.privateRow 9 15, 2415055729911374790240⟩, ⟨.privateRow 9 16, 4583912898621066238800⟩, ⟨.privateRow 9 17, 8555255461105977808800⟩, ⟨.privateRow 9 18, 15001063487069060200800⟩, ⟨.privateRow 9 19, 23941739322273763317600⟩, ⟨.privateRow 9 20, 35887060862221842393120⟩, ⟨.privateRow 9 21, 45691862038457856020800⟩, ⟨.privateRow 10 7, 2624806971452320200⟩, ⟨.privateRow 10 8, 35747371135017313200⟩, ⟨.privateRow 10 9, 138589808092682506560⟩, ⟨.privateRow 10 10, 343435270054235158800⟩, ⟨.privateRow 10 11, 686532845644306861200⟩, ⟨.privateRow 10 12, 1497992778648847681200⟩, ⟨.privateRow 10 13, 2818714586468360354775⟩, ⟨.privateRow 10 14, 4993082808228033639120⟩, ⟨.privateRow 10 16, 31795700202801967370400⟩, ⟨.privateRow 10 17, 7704245929041135173700⟩, ⟨.privateRow 11 5, 25106849292152628000⟩, ⟨.privateRow 11 6, 99742664915188167600⟩, ⟨.privateRow 11 7, 263980586843204774400⟩, ⟨.privateRow 11 8, 548584657033534921800⟩, ⟨.privateRow 11 9, 1233935572053269685600⟩, ⟨.privateRow 11 10, 2399656862345521178400⟩, ⟨.privateRow 11 11, 4246011277349341500000⟩, ⟨.privateRow 11 12, 7124382322264460102850⟩, ⟨.privateRow 11 13, 1732372601158531332000⟩, ⟨.privateRow 12 2, 25408131483658459536⟩, ⟨.privateRow 12 3, 92633812700838133725⟩, ⟨.privateRow 12 4, 262366575102994962600⟩, ⟨.privateRow 12 5, 591893972062498205100⟩, ⟨.privateRow 12 6, 1376273788698166558200⟩, ⟨.privateRow 12 7, 2779014381025144011750⟩, ⟨.privateRow 12 8, 1019668434541556599800⟩, ⟨.privateRow 13 1, 660611418575119947936⟩, ⟨.privateRow 13 2, 688136894349083279100⟩, ⟨.privateRow 13 3, 718055889755565160800⟩, ⟨.privateRow 14 0, 660611418575119947936⟩, ⟨.hall 4 33, 163209879883264928313600⟩, ⟨.hall 3 34, 1309426204675684182516000⟩, ⟨.assumptionRow 21, 242116984684935360⟩]
  caps := #[0, 0, 27223459805088268722000, 1655570490566687511960, 412110061743910780250, 630682992592078907520, 418899482554810533750, 4334590125129785620, 440965512602804870905, 9661797295296939130, 872277855845514393195, 230612502847363692900, 0, 989678850153134373232, 22922204421322941422688, 93616356230554580142720] }

theorem case_53_38_21_checked :
    (Witness.linear .conditional case_53_38_21).check 53 38 21 = true := by
  change case_53_38_21.check 53 38 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_38_22 : Certificate := {
  objectiveScale := 129963406661088000000
  eta := 687800599096267304705170713600
  rows := #[⟨.count 2, 44601444169666653332878214400⟩, ⟨.count 3, 2602331316314079815828563200⟩, ⟨.count 4, 124372803612508159428720000⟩, ⟨.count 5, 2466898584049748616768000⟩, ⟨.path 2, 5875147651097829256968816000⟩, ⟨.path 4, 70651925789194962657244800⟩, ⟨.path 5, 2471664460136987115000000⟩, ⟨.privateRow 2 36, 15330644038018164851763768000⟩, ⟨.privateRow 3 31, 307449570530120170107795840⟩, ⟨.privateRow 3 32, 639276210568291939463620800⟩, ⟨.privateRow 3 34, 4288826533299690457682006400⟩, ⟨.privateRow 4 27, 15263934988807819566252000⟩, ⟨.privateRow 4 28, 66014499787574136050023200⟩, ⟨.privateRow 4 29, 115855151001469721843601600⟩, ⟨.privateRow 4 30, 293678109184662448454688480⟩, ⟨.privateRow 4 33, 4101871596233070238031653200⟩, ⟨.privateRow 5 23, 571871944484259906614400⟩, ⟨.privateRow 5 24, 4477420930050293739433920⟩, ⟨.privateRow 5 25, 11987299786197296982220800⟩, ⟨.privateRow 5 26, 23332749107470539000264000⟩, ⟨.privateRow 5 27, 57243794286068690521478400⟩, ⟨.privateRow 5 28, 106713921248352042247022400⟩, ⟨.privateRow 5 29, 127505764814251340172015360⟩, ⟨.privateRow 5 30, 168334992129094721236706400⟩, ⟨.privateRow 5 31, 226995784708977701886268800⟩, ⟨.privateRow 5 32, 901034707824170682274512000⟩, ⟨.privateRow 6 18, 1370499213360971453760⟩, ⟨.privateRow 6 19, 8810352085891959345600⟩, ⟨.privateRow 6 20, 208737572496517190649600⟩, ⟨.privateRow 6 21, 1091259998638673520056400⟩, ⟨.privateRow 6 22, 2534177636342014488134400⟩, ⟨.privateRow 6 23, 4839232722377590203226560⟩, ⟨.privateRow 6 24, 12498952825852059658291200⟩, ⟨.privateRow 6 25, 24512234992969325057656200⟩, ⟨.privateRow 6 26, 42606862687373515395321600⟩, ⟨.privateRow 6 27, 64067411976592013034645600⟩, ⟨.privateRow 6 28, 90206258223419141086483200⟩, ⟨.privateRow 6 29, 145387695925381955457812400⟩, ⟨.privateRow 6 30, 159204041120077248926030400⟩, ⟨.privateRow 6 31, 245168604278144183363126400⟩, ⟨.privateRow 7 15, 806176007859394972800⟩, ⟨.privateRow 7 16, 4282810041753035793000⟩, ⟨.privateRow 7 17, 72179625237011163231360⟩, ⟨.privateRow 7 18, 296615186891695964635200⟩, ⟨.privateRow 7 19, 677869995531618957513600⟩, ⟨.privateRow 7 20, 1238017622736077546563200⟩, ⟨.privateRow 7 21, 3023819628024616107523200⟩, ⟨.privateRow 7 22, 6450939797290092632848320⟩, ⟨.privateRow 7 23, 11716245497332571516921600⟩, ⟨.privateRow 7 24, 19649532471562928218284000⟩, ⟨.privateRow 7 26, 107563630760635844548353600⟩, ⟨.privateRow 7 27, 48189493340198478257109120⟩, ⟨.privateRow 7 29, 331382141459971694280988800⟩, ⟨.privateRow 8 12, 631150953521500011600⟩, ⟨.privateRow 8 13, 1998644686151416703400⟩, ⟨.privateRow 8 14, 28216160275078824048000⟩, ⟨.privateRow 8 15, 101181387236415470609625⟩, ⟨.privateRow 8 16, 234241157216946037638480⟩, ⟨.privateRow 8 17, 430850690200355400775800⟩, ⟨.privateRow 8 18, 956582095171854979119600⟩, ⟨.privateRow 8 19, 1979657561632978244717700⟩, ⟨.privateRow 8 20, 3855930684500487752686800⟩, ⟨.privateRow 8 21, 6636299815897164021969360⟩, ⟨.privateRow 8 22, 10723394956097734419308800⟩, ⟨.privateRow 8 23, 12709881220408396671096450⟩, ⟨.privateRow 8 25, 99982200424724620587585000⟩, ⟨.privateRow 8 26, 36877392833117019877774080⟩, ⟨.privateRow 8 27, 18092731021385699707528500⟩, ⟨.privateRow 9 9, 652618673029034025600⟩, ⟨.privateRow 9 10, 1370499213360971453760⟩, ⟨.privateRow 9 11, 12983676758156571667200⟩, ⟨.privateRow 9 12, 44921918660165175428800⟩, ⟨.privateRow 9 13, 105609057029580741436800⟩, ⟨.privateRow 9 14, 201292071962392682271000⟩, ⟨.privateRow 9 15, 432164085279826331752320⟩, ⟨.privateRow 9 16, 826215240054757076409600⟩, ⟨.privateRow 9 17, 1573965635036869523433600⟩, ⟨.privateRow 9 18, 2839217537012812528372800⟩, ⟨.privateRow 9 19, 4682123676191391566572800⟩, ⟨.privateRow 9 20, 7286944317440285219641920⟩, ⟨.privateRow 9 21, 10371633491335085079510400⟩, ⟨.privateRow 9 22, 12562338414470004588027600⟩, ⟨.privateRow 9 24, 94893365533113663458342400⟩, ⟨.privateRow 10 7, 934431281837025991200⟩, ⟨.privateRow 10 8, 7831424076348408307200⟩, ⟨.privateRow 10 9, 25696860250518214758000⟩, ⟨.privateRow 10 10, 62754437664423429724800⟩, ⟨.privateRow 10 11, 123344929202487430838400⟩, ⟨.privateRow 10 12, 268456610617178525942400⟩, ⟨.privateRow 10 13, 80945109789132376487700⟩, ⟨.privateRow 10 14, 1747386497035238603544000⟩, ⟨.privateRow 10 15, 1168840043394999939849600⟩, ⟨.privateRow 10 16, 2699356335239051851809600⟩, ⟨.privateRow 10 17, 4289662537819840650268800⟩, ⟨.privateRow 10 18, 6464395607748545807121600⟩, ⟨.privateRow 10 19, 9302263410687593742396000⟩, ⟨.privateRow 10 21, 37278435165426774149430600⟩, ⟨.privateRow 10 23, 35167009814842527503481600⟩, ⟨.privateRow 10 26, 91069672727836553102352000⟩, ⟨.privateRow 11 4, 1713124016701214317200⟩, ⟨.privateRow 11 5, 5362823008803801340800⟩, ⟨.privateRow 11 6, 18688625636740519824000⟩, ⟨.privateRow 11 7, 48946400477177551920000⟩, ⟨.privateRow 11 8, 100731692182031401851360⟩, ⟨.privateRow 11 9, 222886451015021146953600⟩, ⟨.privateRow 11 10, 427138921497502769755200⟩, ⟨.privateRow 11 11, 164459905603316574451200⟩, ⟨.privateRow 11 12, 2122560656692804539010800⟩, ⟨.privateRow 11 14, 7482925704950904137529600⟩, ⟨.privateRow 11 15, 3039345563168985154761600⟩, ⟨.privateRow 11 16, 7698779331055257141496800⟩, ⟨.privateRow 11 17, 10880517845710330641532800⟩, ⟨.privateRow 11 18, 14871286964179901244749760⟩, ⟨.privateRow 11 20, 20557488200414571806400⟩, ⟨.privateRow 11 21, 116590325936636928673440000⟩, ⟨.privateRow 12 3, 37688728367426714978400⟩, ⟨.privateRow 12 4, 39327368731227876499200⟩, ⟨.privateRow 12 5, 107926813052176501983600⟩, ⟨.privateRow 12 6, 253052890467007943426400⟩, ⟨.privateRow 12 8, 1910223443043785606536800⟩, ⟨.privateRow 12 10, 3305523176225484237223200⟩, ⟨.privateRow 12 11, 2119990970667752717535000⟩, ⟨.privateRow 12 13, 28452297865380925043336400⟩, ⟨.privateRow 12 14, 1678597978826159074807200⟩, ⟨.privateRow 12 15, 18109433980548536547121200⟩, ⟨.privateRow 12 16, 24473689702593547735519200⟩, ⟨.privateRow 12 17, 37187468280139939669187280⟩, ⟨.privateRow 12 22, 409548335677479140984281440⟩, ⟨.privateRow 13 2, 471109104592833937230000⟩, ⟨.privateRow 13 3, 216300528021753320745600⟩, ⟨.privateRow 13 4, 842857016216997444062400⟩, ⟨.privateRow 13 5, 86145664839832491379200⟩, ⟨.privateRow 13 9, 3298872224160644228697600⟩, ⟨.privateRow 13 10, 5483709977460587029357200⟩, ⟨.privateRow 13 12, 32304624314937184267200⟩, ⟨.privateRow 13 14, 37688728367426714978400⟩, ⟨.privateRow 13 15, 41114976400829143612800⟩, ⟨.privateRow 13 16, 90452948081824115948160⟩, ⟨.privateRow 13 17, 100503275646471239942400⟩, ⟨.privateRow 13 18, 13285276749517917029886000⟩, ⟨.privateRow 14 4, 17918298286685158206873600⟩, ⟨.privateRow 14 8, 22480217979159228816528000⟩, ⟨.privateRow 14 9, 21864173544153423026844300⟩, ⟨.privateRow 14 17, 52547509526284697358634200⟩, ⟨.privateRow 15 2, 142175588394067178613062400⟩, ⟨.privateRow 15 6, 445857656586658038194472000⟩, ⟨.privateRow 15 8, 218641735441534230268443000⟩, ⟨.hall 14 6, 3363524957276068384800⟩, ⟨.hall 13 7, 195695997514243978752⟩, ⟨.hall 10 8, 15490350990513810560⟩, ⟨.hall 11 8, 56480253720450291424⟩, ⟨.hall 14 12, 2085081082112313885600⟩, ⟨.hall 10 16, 7417027403177441280⟩, ⟨.hall 8 18, 527960817615340032⟩, ⟨.hall 5 21, 2300031933559662960⟩, ⟨.hall 4 24, 14323471990413627888⟩, ⟨.hall 13 24, 2822131980152912417582592⟩, ⟨.hall 6 29, 32867113191388619843700⟩, ⟨.hall 2 33, 2488195066924034300632800⟩, ⟨.hall 3 34, 135834484319447872406722560⟩]
  caps := #[0, 39185129195365482255326400, 2299964737394205492811200, 0, 555078671208484132366800, 12620716314864141213360, 10321328518141855948200, 53417327029907735553720, 10236996523319189408785, 0, 567902047924072211179500, 4018247975932718392800, 121908458753700698336400, 0, 0, 0] }

theorem case_53_38_22_checked :
    (Witness.linear .conditional case_53_38_22).check 53 38 22 = true := by
  change case_53_38_22.check 53 38 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_38_23 : Certificate := {
  objectiveScale := 21
  eta := 610740
  rows := #[⟨.assumptionRow 23, 8⟩]
  caps := #[0, 0, 248170, 141680, 67298, 30877, 17157, 7467, 4029, 2176, 910, 21395520, 21246940, 15155160, 9152528, 4903140] }

theorem case_53_38_23_checked :
    (Witness.linear .conditional case_53_38_23).check 53 38 23 = true := by
  change case_53_38_23.check 53 38 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_38_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900, 534888, 326876] }

theorem case_53_38_24_checked :
    (Witness.linear .negative case_53_38_24).check 53 38 24 = true := by
  change case_53_38_24.check 53 38 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_39_1_checked :
    (Witness.rising).check 53 39 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_39_2_checked :
    (Witness.rising).check 53 39 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_39_3_checked :
    (Witness.rising).check 53 39 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_39_4_checked :
    (Witness.rising).check 53 39 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_39_5_checked :
    (Witness.rising).check 53 39 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_39_6_checked :
    (Witness.rising).check 53 39 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_39_7_checked :
    (Witness.rising).check 53 39 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_39_8_checked :
    (Witness.rising).check 53 39 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_39_9_checked :
    (Witness.rising).check 53 39 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_39_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_53_39_10_checked :
    (Witness.linear .positive case_53_39_10).check 53 39 10 = true := by
  change case_53_39_10.check 53 39 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_39_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_53_39_11_checked :
    (Witness.linear .positive case_53_39_11).check 53 39 11 = true := by
  change case_53_39_11.check 53 39 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_39_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_53_39_12_checked :
    (Witness.linear .positive case_53_39_12).check 53 39 12 = true := by
  change case_53_39_12.check 53 39 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_39_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_53_39_13_checked :
    (Witness.linear .positive case_53_39_13).check 53 39 13 = true := by
  change case_53_39_13.check 53 39 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_39_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_53_39_14_checked :
    (Witness.linear .positive case_53_39_14).check 53 39 14 = true := by
  change case_53_39_14.check 53 39 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_39_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_53_39_15_checked :
    (Witness.linear .positive case_53_39_15).check 53 39 15 = true := by
  change case_53_39_15.check 53 39 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_39_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_53_39_16_checked :
    (Witness.linear .positive case_53_39_16).check 53 39 16 = true := by
  change case_53_39_16.check 53 39 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_39_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_53_39_17_checked :
    (Witness.linear .positive case_53_39_17).check 53 39 17 = true := by
  change case_53_39_17.check 53 39 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_39_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_53_39_18_checked :
    (Witness.linear .positive case_53_39_18).check 53 39 18 = true := by
  change case_53_39_18.check 53 39 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_39_19 : Certificate := {
  objectiveScale := 999
  eta := 40875947760
  rows := #[⟨.assumptionRow 19, 1748⟩]
  caps := #[0, 0, 11625259725, 3333040515, 964321345, 281885976, 83374698, 24996970, 7613892, 2362776, 1430715, 431730585, 295861995, 139683830, 53086990] }

theorem case_53_39_19_checked :
    (Witness.linear .conditional case_53_39_19).check 53 39 19 = true := by
  change case_53_39_19.check 53 39 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_39_20 : Certificate := {
  objectiveScale := 1675483992000000
  eta := 8075927820492076890945600
  rows := #[⟨.count 2, 594416199751588880265600⟩, ⟨.count 3, 36140864108763523309200⟩, ⟨.count 4, 1445984399285852025600⟩, ⟨.count 5, 23322329020739548800⟩, ⟨.count 6, 3887054836789924800⟩, ⟨.path 4, 1345005594011309630400⟩, ⟨.privateRow 2 36, 45087892579344732717600⟩, ⟨.privateRow 2 37, 66188769760858839494400⟩, ⟨.privateRow 3 31, 848025796893001927200⟩, ⟨.privateRow 3 32, 4825195521649173150480⟩, ⟨.privateRow 3 33, 8730568104357470471100⟩, ⟨.privateRow 3 34, 17961756479569843340400⟩, ⟨.privateRow 3 35, 20219001615417392587800⟩, ⟨.privateRow 3 36, 28391048527913610739200⟩, ⟨.privateRow 4 27, 55066610187857268000⟩, ⟨.privateRow 4 28, 494141846126919190200⟩, ⟨.privateRow 4 29, 1185690548607955275600⟩, ⟨.privateRow 4 30, 1915346270828235445200⟩, ⟨.privateRow 4 31, 4231836600813191129760⟩, ⟨.privateRow 4 32, 5892532191646226626500⟩, ⟨.privateRow 4 33, 7606966315597882833600⟩, ⟨.privateRow 4 34, 10075246136959485081600⟩, ⟨.privateRow 5 24, 25760572509271410720⟩, ⟨.privateRow 5 25, 137485129577259640176⟩, ⟨.privateRow 5 26, 268725057716743467840⟩, ⟨.privateRow 5 27, 462365172836161554960⟩, ⟨.privateRow 5 28, 1022684127559429214880⟩, ⟨.privateRow 5 29, 1648888661766286100160⟩, ⟨.privateRow 5 30, 2297249408542845556800⟩, ⟨.privateRow 5 31, 2955230616040460077320⟩, ⟨.privateRow 5 32, 4168088901489836363040⟩, ⟨.privateRow 5 33, 1502541047161145431440⟩, ⟨.privateRow 6 21, 7275769309888833600⟩, ⟨.privateRow 6 22, 36333165349439158200⟩, ⟨.privateRow 6 23, 71498251088832859200⟩, ⟨.privateRow 6 24, 119786073220409515920⟩, ⟨.privateRow 6 25, 274397278478577654400⟩, ⟨.privateRow 6 26, 479160488943458021700⟩, ⟨.privateRow 6 27, 727712194801885207200⟩, ⟨.privateRow 6 28, 1015493076111367854000⟩, ⟨.privateRow 6 29, 1301645096346386151360⟩, ⟨.privateRow 6 30, 1486960435690345816200⟩, ⟨.privateRow 7 18, 2235056531154206760⟩, ⟨.privateRow 7 19, 10793518341443451900⟩, ⟨.privateRow 7 20, 23247577966185896400⟩, ⟨.privateRow 7 21, 38951528676999038100⟩, ⟨.privateRow 7 22, 84057560845582123800⟩, ⟨.privateRow 7 23, 158737601897408554020⟩, ⟨.privateRow 7 24, 257571369810065711400⟩, ⟨.privateRow 7 25, 379777404600740621475⟩, ⟨.privateRow 7 26, 522947698935273097200⟩, ⟨.privateRow 7 27, 562894128552640985100⟩, ⟨.privateRow 8 15, 857438566938954000⟩, ⟨.privateRow 8 16, 3947790068614767375⟩, ⟨.privateRow 8 17, 9426107979215567640⟩, ⟨.privateRow 8 18, 16762923983656550700⟩, ⟨.privateRow 8 19, 34273358512849625400⟩, ⟨.privateRow 8 20, 62881210015987012650⟩, ⟨.privateRow 8 21, 109588443750861402600⟩, ⟨.privateRow 8 22, 169815708182259839700⟩, ⟨.privateRow 8 23, 244074651626767361400⟩, ⟨.privateRow 8 24, 84968589322954762425⟩, ⟨.privateRow 9 12, 409163667030518400⟩, ⟨.privateRow 9 13, 1871544921417371200⟩, ⟨.privateRow 9 14, 4801655974858142400⟩, ⟨.privateRow 9 15, 9353225701025756550⟩, ⟨.privateRow 9 16, 19564842678509288160⟩, ⟨.privateRow 9 17, 25589777675533671600⟩, ⟨.privateRow 9 18, 76993586190261972000⟩, ⟨.privateRow 9 19, 87296773209573727800⟩, ⟨.privateRow 9 20, 32686597491188004000⟩, ⟨.privateRow 10 9, 277646774056423200⟩, ⟨.privateRow 10 10, 1166116451036977440⟩, ⟨.privateRow 10 11, 3191476602838043520⟩, ⟨.privateRow 10 12, 6737561717102536320⟩, ⟨.privateRow 10 13, 14953728607415357760⟩, ⟨.privateRow 10 14, 27403736599368969840⟩, ⟨.privateRow 10 15, 34672529144166129216⟩, ⟨.privateRow 11 6, 253503576312386400⟩, ⟨.privateRow 11 7, 927592631506686600⟩, ⟨.privateRow 11 8, 2915291127592443600⟩, ⟨.privateRow 11 9, 6413640480703375920⟩, ⟨.privateRow 11 10, 15190201138507995600⟩, ⟨.privateRow 11 11, 4210976073189085200⟩, ⟨.privateRow 12 4, 890783400097691100⟩, ⟨.privateRow 12 5, 3718052452581667200⟩, ⟨.privateRow 12 6, 4858818545987406000⟩, ⟨.privateRow 13 1, 2466784800270529200⟩, ⟨.hall 3 35, 1772658966194405289000⟩, ⟨.assumptionRow 20, 1325299460252040⟩]
  caps := #[0, 104448215306220786000, 0, 0, 14311406980848751020, 2043402717570963840, 8021461469347421300, 313061251808214000, 12902810070772440, 7121338495656019880, 12278759526228638664, 0, 34602433452622935900, 144603248556042738000, 344379565883754601200] }

theorem case_53_39_20_checked :
    (Witness.linear .conditional case_53_39_20).check 53 39 20 = true := by
  change case_53_39_20.check 53 39 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_39_21 : Certificate := {
  objectiveScale := 2998234512000000
  eta := 17764373130642596555697600
  rows := #[⟨.count 2, 1300942835105872771612800⟩, ⟨.count 3, 77925731840546017428000⟩, ⟨.count 4, 2973596950144292472000⟩, ⟨.path 4, 2965256778543369710400⟩, ⟨.privateRow 2 36, 102169292857604778405600⟩, ⟨.privateRow 2 37, 153478416703231785765600⟩, ⟨.privateRow 3 31, 1722775095788934587400⟩, ⟨.privateRow 3 32, 10343064215214310900320⟩, ⟨.privateRow 3 33, 19176785037303094000800⟩, ⟨.privateRow 3 34, 40658917514059012568400⟩, ⟨.privateRow 3 35, 47305943245587983556600⟩, ⟨.privateRow 3 36, 68401475726701504186800⟩, ⟨.privateRow 4 27, 165523751799970964400⟩, ⟨.privateRow 4 28, 1013063666838374151000⟩, ⟨.privateRow 4 29, 2483411570547677312400⟩, ⟨.privateRow 4 30, 4055655840335687788200⟩, ⟨.privateRow 4 31, 9244971223821157144320⟩, ⟨.privateRow 4 32, 13333812794825938915500⟩, ⟨.privateRow 4 33, 17843525228284149794400⟩, ⟨.privateRow 4 34, 24689600559580404848400⟩, ⟨.privateRow 5 22, 986713920108211680⟩, ⟨.privateRow 5 23, 7871286044499597720⟩, ⟨.privateRow 5 24, 77281717527814232160⟩, ⟨.privateRow 5 25, 282433404441155935968⟩, ⟨.privateRow 5 26, 550406964889453351680⟩, ⟨.privateRow 5 27, 949510320256858880520⟩, ⟨.privateRow 5 28, 2144488153457001512160⟩, ⟨.privateRow 5 29, 3578617035490644267120⟩, ⟨.privateRow 5 30, 5164496538352565686272⟩, ⟨.privateRow 5 31, 6933728417865867858240⟩, ⟨.privateRow 5 32, 10314688714905744449280⟩, ⟨.privateRow 5 33, 5673739592520413734320⟩, ⟨.privateRow 6 19, 215947490932773600⟩, ⟨.privateRow 6 20, 3655682525076238800⟩, ⟨.privateRow 6 21, 27458554039374981600⟩, ⟨.privateRow 6 22, 78388939208596816800⟩, ⟨.privateRow 6 23, 145941240690385358400⟩, ⟨.privateRow 6 24, 241386105364654330080⟩, ⟨.privateRow 6 25, 556424701636779976000⟩, ⟨.privateRow 6 26, 995005057909120958700⟩, ⟨.privateRow 6 27, 1561115261594582179200⟩, ⟨.privateRow 6 28, 2259998466356942110800⟩, ⟨.privateRow 6 29, 3029440971299507724960⟩, ⟨.privateRow 6 30, 4593203132140094472000⟩, ⟨.privateRow 6 31, 484370222162211184800⟩, ⟨.privateRow 7 16, 85743856693895400⟩, ⟨.privateRow 7 17, 1761321722920434675⟩, ⟨.privateRow 7 18, 10721792924812209240⟩, ⟨.privateRow 7 19, 26792913696444838800⟩, ⟨.privateRow 7 20, 49373071532687410200⟩, ⟨.privateRow 7 21, 78996291526845242550⟩, ⟨.privateRow 7 22, 167673410914256301600⟩, ⟨.privateRow 7 23, 318592732060394211420⟩, ⟨.privateRow 7 24, 528693444676162966200⟩, ⟨.privateRow 7 25, 803041235188068526650⟩, ⟨.privateRow 7 26, 1146334118385457287000⟩, ⟨.privateRow 7 27, 1538706853205111690100⟩, ⟨.privateRow 7 28, 739900888182962185680⟩, ⟨.privateRow 8 13, 76718187568222200⟩, ⟨.privateRow 8 14, 1025750581930674600⟩, ⟨.privateRow 8 15, 5087468830504460400⟩, ⟨.privateRow 8 16, 12207781596793357575⟩, ⟨.privateRow 8 17, 22382957435181983640⟩, ⟨.privateRow 8 18, 35642904619493328300⟩, ⟨.privateRow 8 19, 69331603098512601000⟩, ⟨.privateRow 8 20, 124709676013676754000⟩, ⟨.privateRow 8 21, 218337637025597707800⟩, ⟨.privateRow 8 22, 344587411281426833520⟩, ⟨.privateRow 8 23, 508124446164816280800⟩, ⟨.privateRow 8 24, 652053448871509885200⟩, ⟨.privateRow 9 10, 61699283123649600⟩, ⟨.privateRow 9 11, 712626720078152880⟩, ⟨.privateRow 9 12, 3034630530476344800⟩, ⟨.privateRow 9 13, 7450188437180689200⟩, ⟨.privateRow 9 14, 13909558974787476000⟩, ⟨.privateRow 9 15, 22350565311542067600⟩, ⟨.privateRow 9 16, 41677865750025304800⟩, ⟨.privateRow 9 17, 69735614750504960400⟩, ⟨.privateRow 9 18, 116910649321912353600⟩, ⟨.privateRow 9 19, 190951568857305055800⟩, ⟨.privateRow 9 20, 255132144742029609600⟩, ⟨.privateRow 10 7, 50700715262477280⟩, ⟨.privateRow 10 8, 583058225518488720⟩, ⟨.privateRow 10 9, 2387762256885239520⟩, ⟨.privateRow 10 10, 6005499722840433816⟩, ⟨.privateRow 10 11, 11722539060424352160⟩, ⟨.privateRow 10 12, 18463510474752142800⟩, ⟨.privateRow 10 13, 37727296945313976000⟩, ⟨.privateRow 10 14, 57358352935381327830⟩, ⟨.privateRow 10 15, 92123199631921217760⟩, ⟨.privateRow 10 16, 28236676921538239440⟩, ⟨.privateRow 11 4, 116611645103697744⟩, ⟨.privateRow 11 5, 607352318248425750⟩, ⟨.privateRow 11 6, 2535035763123864000⟩, ⟨.privateRow 11 7, 6625661653619190000⟩, ⟨.privateRow 11 8, 13465868541736525200⟩, ⟨.privateRow 11 9, 23468093577119170980⟩, ⟨.privateRow 11 10, 41581257661976432400⟩, ⟨.privateRow 12 2, 1233392400135264600⟩, ⟨.privateRow 12 3, 855152064093783456⟩, ⟨.privateRow 12 4, 16034101201758439800⟩, ⟨.privateRow 12 5, 12548427027463126800⟩, ⟨.privateRow 13 0, 9501689601042038400⟩, ⟨.hall 3 35, 4941175520341892531700⟩, ⟨.assumptionRow 21, 1403184333620160⟩]
  caps := #[0, 304394138842270276800, 253114803616618944000, 3453435344664559800, 8036496723531765060, 1720633364816798880, 100957653016496640, 6633548394306213690, 0, 0, 15977307417848677134, 0, 0, 193848897330454766400, 1375557398710919424000] }

theorem case_53_39_21_checked :
    (Witness.linear .conditional case_53_39_21).check 53 39 21 = true := by
  change case_53_39_21.check 53 39 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_39_22 : Certificate := {
  objectiveScale := 171949177582416000000
  eta := 1418739245194892476396020480000
  rows := #[⟨.count 2, 111726618984495894393718704000⟩, ⟨.count 3, 7539084947243618005301064000⟩, ⟨.count 4, 381081258839919249900288000⟩, ⟨.count 5, 9855549797584118531904000⟩, ⟨.path 4, 160942797757929181058064000⟩, ⟨.path 5, 9748353463085089716864000⟩, ⟨.privateRow 3 31, 15308041468006813738212000⟩, ⟨.privateRow 3 32, 894692285930129382614318400⟩, ⟨.privateRow 3 33, 1738341036866937684665484000⟩, ⟨.privateRow 3 36, 28003175923474497236386896000⟩, ⟨.privateRow 4 28, 60519235475789977859973000⟩, ⟨.privateRow 4 29, 210985028851257632738052000⟩, ⟨.privateRow 4 30, 350864416925798497595874000⟩, ⟨.privateRow 4 31, 835175715763607511257764800⟩, ⟨.privateRow 4 32, 920261962349417067916536000⟩, ⟨.privateRow 4 34, 4971611562995896959838698000⟩, ⟨.privateRow 4 35, 3098543791569623599270068000⟩, ⟨.privateRow 5 23, 184791558704702222473200⟩, ⟨.privateRow 5 24, 2478820100604490418630400⟩, ⟨.privateRow 5 25, 18799461238891706099606880⟩, ⟨.privateRow 5 26, 43683811926884421677985600⟩, ⟨.privateRow 5 27, 79809420965019726528147600⟩, ⟨.privateRow 5 28, 184380910796469550867704000⟩, ⟨.privateRow 5 29, 320893963756617348254757600⟩, ⟨.privateRow 5 30, 450119385171996000216275520⟩, ⟨.privateRow 5 31, 625334634656712320849308800⟩, ⟨.privateRow 5 32, 607977916402078067657011200⟩, ⟨.privateRow 5 33, 213044134791110028931324800⟩, ⟨.privateRow 5 34, 3585531145942748856227774400⟩, ⟨.privateRow 6 18, 2851721584949108371500⟩, ⟨.privateRow 6 19, 12167345429116195718400⟩, ⟨.privateRow 6 20, 136882636077557201832000⟩, ⟨.privateRow 6 21, 1031884487353892752272000⟩, ⟨.privateRow 6 22, 5098878193889005768242000⟩, ⟨.privateRow 6 23, 10863503754155221563576000⟩, ⟨.privateRow 6 24, 19245698632504542577579200⟩, ⟨.privateRow 6 25, 46398143903029759672832000⟩, ⟨.privateRow 6 26, 84878641254425261569326000⟩, ⟨.privateRow 6 27, 137925551400052875750720000⟩, ⟨.privateRow 6 28, 204350566482006507090528000⟩, ⟨.privateRow 6 30, 1031479104162432294405036000⟩, ⟨.privateRow 6 31, 103711410601429173254712000⟩, ⟨.privateRow 7 15, 1901147723299405581000⟩, ⟨.privateRow 7 16, 8051919769268070696000⟩, ⟨.privateRow 7 17, 70580109227490432194625⟩, ⟨.privateRow 7 18, 415210662768590178890400⟩, ⟨.privateRow 7 19, 1581483313253205528309000⟩, ⟨.privateRow 7 20, 3437860052255571261396000⟩, ⟨.privateRow 7 21, 5931580896694145412720000⟩, ⟨.privateRow 7 22, 13361611862570640497010000⟩, ⟨.privateRow 7 23, 26408082565262723163438600⟩, ⟨.privateRow 7 24, 44654157724856438286528000⟩, ⟨.privateRow 7 25, 63744532588367419428139500⟩, ⟨.privateRow 7 26, 114834754337922095394060000⟩, ⟨.privateRow 7 28, 332850662017991969834782800⟩, ⟨.privateRow 7 29, 280198756050759592150104000⟩, ⟨.privateRow 8 12, 1711032950969465022900⟩, ⟨.privateRow 8 13, 5403261950429889546000⟩, ⟨.privateRow 8 14, 41825249912586922782000⟩, ⟨.privateRow 8 15, 197272034347067732052000⟩, ⟨.privateRow 8 16, 630943400669990227194375⟩, ⟨.privateRow 8 17, 1403047019794961318778000⟩, ⟨.privateRow 8 18, 2488330777267021990446000⟩, ⟨.privateRow 8 19, 5191010737402746192552000⟩, ⟨.privateRow 8 20, 9849846354414220315161000⟩, ⟨.privateRow 8 21, 17763633000064809601380000⟩, ⟨.privateRow 8 22, 28389458722485363659956800⟩, ⟨.privateRow 8 23, 40756804892092656845478000⟩, ⟨.privateRow 8 24, 58855255930972173125202750⟩, ⟨.privateRow 8 26, 192867634233278097381288000⟩, ⟨.privateRow 9 10, 4345480510398641328000⟩, ⟨.privateRow 9 11, 29657904483470727063600⟩, ⟨.privateRow 9 12, 120072487787330878800000⟩, ⟨.privateRow 9 13, 342206590193893004580000⟩, ⟨.privateRow 9 14, 759564431567621335656000⟩, ⟨.privateRow 9 15, 1405898741379910427149500⟩, ⟨.privateRow 9 16, 2914079230273328874556800⟩, ⟨.privateRow 9 17, 5230872164392364498580000⟩, ⟨.privateRow 9 18, 9195705295466663302560000⟩, ⟨.privateRow 9 19, 15448726399530969751206000⟩, ⟨.privateRow 9 21, 81833002601699613828564000⟩, ⟨.privateRow 9 24, 206757962684767354386240000⟩, ⟨.privateRow 10 7, 7141702751872549660800⟩, ⟨.privateRow 10 8, 26132139614806374895200⟩, ⟨.privateRow 10 9, 93862379024610652684800⟩, ⟨.privateRow 10 10, 258708182186583111462480⟩, ⟨.privateRow 10 11, 561939242844708512784000⟩, ⟨.privateRow 10 12, 1063121806869027600895200⟩, ⟨.privateRow 10 13, 2246485615625791724184000⟩, ⟨.privateRow 10 14, 4080813588062174079616500⟩, ⟨.privateRow 10 15, 6871508331093371531966400⟩, ⟨.privateRow 10 16, 11316283071154621814311200⟩, ⟨.privateRow 10 17, 17961107740084390375771200⟩, ⟨.privateRow 10 19, 58334401945852059158913600⟩, ⟨.privateRow 10 20, 86498875390129946981677440⟩, ⟨.privateRow 10 21, 1441830433350269192630400⟩, ⟨.privateRow 10 23, 120577958654490459705211200⟩, ⟨.privateRow 11 5, 59886153283931275801500⟩, ⟨.privateRow 11 6, 89271284398406870760000⟩, ⟨.privateRow 11 7, 270654303153351739986000⟩, ⟨.privateRow 11 8, 586639868903816579280000⟩, ⟨.privateRow 11 11, 12661643837174041169460000⟩, ⟨.privateRow 11 13, 18466323123337951259648250⟩, ⟨.privateRow 11 14, 16247968902406039857458400⟩, ⟨.privateRow 11 15, 29302661451745638135036000⟩, ⟨.privateRow 11 16, 22522458351530373439896000⟩, ⟨.privateRow 11 17, 29327104779616630492506000⟩, ⟨.privateRow 11 20, 512625472110451720860840000⟩, ⟨.privateRow 12 3, 361370159244751012836480⟩, ⟨.privateRow 12 4, 313689374344401920865000⟩, ⟨.privateRow 12 5, 916518519823643873136000⟩, ⟨.privateRow 12 6, 1779474269008243623816000⟩, ⟨.privateRow 12 10, 3262369493181779976996000⟩, ⟨.privateRow 12 12, 7575598390417306388889750⟩, ⟨.privateRow 12 18, 2076673848459835820433638400⟩, ⟨.privateRow 13 2, 7046718105272644750311360⟩, ⟨.privateRow 13 3, 564640873819923457557000⟩, ⟨.privateRow 13 6, 22370533667532205556544000⟩, ⟨.privateRow 13 9, 6524738986363559953992000⟩, ⟨.privateRow 13 10, 18865648019395089640728000⟩, ⟨.privateRow 13 11, 22585634952796938302280000⟩, ⟨.privateRow 13 17, 10383068100499808476324161600⟩, ⟨.privateRow 14 0, 92601103306467447039348000⟩, ⟨.privateRow 14 4, 200190855263427407679300000⟩, ⟨.privateRow 14 7, 241071935180379951984336000⟩, ⟨.privateRow 14 9, 224527782766040151357960000⟩, ⟨.privateRow 14 10, 179838118311645621231904500⟩, ⟨.hall 13 5, 2678138531952206122800⟩, ⟨.hall 12 7, 86473608818969618400⟩, ⟨.hall 13 8, 488642819864963924160⟩, ⟨.hall 7 14, 1480436226497202975⟩, ⟨.hall 12 18, 1894816141724889694080⟩, ⟨.hall 9 22, 88290782424171495168⟩, ⟨.hall 1 37, 12268398034596387428228484000⟩]
  caps := #[0, 0, 0, 0, 1917618949328740786385400, 0, 672586243593640872509500, 570344316989821674300, 0, 59267537602451439159600, 820122362613278701477380, 106085588783213297339640, 3763878093701289330657930, 31843473963330661276908120, 0] }

theorem case_53_39_22_checked :
    (Witness.linear .conditional case_53_39_22).check 53 39 22 = true := by
  change case_53_39_22.check 53 39 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_39_23 : Certificate := {
  objectiveScale := 19
  eta := 32957340
  rows := #[⟨.assumptionRow 23, 11⟩]
  caps := #[0, 0, 12486240, 5229510, 1825395, 841225, 307648, 137940, 53295, 23256, 8554275, 34964370, 31955625, 21815040, 12714515] }

theorem case_53_39_23_checked :
    (Witness.linear .conditional case_53_39_23).check 53 39 23 = true := by
  change case_53_39_23.check 53 39 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_39_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440, 2674440, 1931540, 1188640] }

theorem case_53_39_24_checked :
    (Witness.linear .negative case_53_39_24).check 53 39 24 = true := by
  change case_53_39_24.check 53 39 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_39_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900] }

theorem case_53_39_25_checked :
    (Witness.linear .negative case_53_39_25).check 53 39 25 = true := by
  change case_53_39_25.check 53 39 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_40_1_checked :
    (Witness.rising).check 53 40 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_40_2_checked :
    (Witness.rising).check 53 40 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_40_3_checked :
    (Witness.rising).check 53 40 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_40_4_checked :
    (Witness.rising).check 53 40 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_40_5_checked :
    (Witness.rising).check 53 40 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_40_6_checked :
    (Witness.rising).check 53 40 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_40_7_checked :
    (Witness.rising).check 53 40 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_40_8_checked :
    (Witness.rising).check 53 40 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_40_9_checked :
    (Witness.rising).check 53 40 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_40_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_53_40_10_checked :
    (Witness.linear .positive case_53_40_10).check 53 40 10 = true := by
  change case_53_40_10.check 53 40 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_40_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_53_40_11_checked :
    (Witness.linear .positive case_53_40_11).check 53 40 11 = true := by
  change case_53_40_11.check 53 40 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_40_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_53_40_12_checked :
    (Witness.linear .positive case_53_40_12).check 53 40 12 = true := by
  change case_53_40_12.check 53 40 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_40_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_53_40_13_checked :
    (Witness.linear .positive case_53_40_13).check 53 40 13 = true := by
  change case_53_40_13.check 53 40 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_40_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_53_40_14_checked :
    (Witness.linear .positive case_53_40_14).check 53 40 14 = true := by
  change case_53_40_14.check 53 40 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_40_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_53_40_15_checked :
    (Witness.linear .positive case_53_40_15).check 53 40 15 = true := by
  change case_53_40_15.check 53 40 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_40_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_53_40_16_checked :
    (Witness.linear .positive case_53_40_16).check 53 40 16 = true := by
  change case_53_40_16.check 53 40 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_40_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_53_40_17_checked :
    (Witness.linear .positive case_53_40_17).check 53 40 17 = true := by
  change case_53_40_17.check 53 40 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_40_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_53_40_18_checked :
    (Witness.linear .positive case_53_40_18).check 53 40 18 = true := by
  change case_53_40_18.check 53 40 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_40_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_53_40_19_checked :
    (Witness.linear .positive case_53_40_19).check 53 40 19 = true := by
  change case_53_40_19.check 53 40 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_40_20 : Certificate := {
  objectiveScale := 5
  eta := 300230040
  rows := #[⟨.assumptionRow 20, 7⟩]
  caps := #[0, 0, 86843400, 25282635, 7413705, 2191555, 653752, 197030, 60078, 18564, 12746370, 10015005, 5525520, 2516085] }

theorem case_53_40_20_checked :
    (Witness.linear .conditional case_53_40_20).check 53 40 20 = true := by
  change case_53_40_20.check 53 40 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_40_21 : Certificate := {
  objectiveScale := 748
  eta := 53359066200
  rows := #[⟨.assumptionRow 21, 863⟩]
  caps := #[0, 0, 16123097520, 4873385475, 1475156865, 447634395, 136307292, 41690902, 12819870, 4346934, 2621199945, 2253376125, 1371364995, 695574165] }

theorem case_53_40_21_checked :
    (Witness.linear .conditional case_53_40_21).check 53 40 21 = true := by
  change case_53_40_21.check 53 40 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_40_22 : Certificate := {
  objectiveScale := 556
  eta := 22313791320
  rows := #[⟨.assumptionRow 22, 503⟩]
  caps := #[0, 0, 7351914120, 2360809815, 744375450, 231529155, 82031455, 28111336, 9385734, 3101550, 2467683225, 2290704780, 1516441290, 843924510] }

theorem case_53_40_22_checked :
    (Witness.linear .conditional case_53_40_22).check 53 40 22 = true := by
  change case_53_40_22.check 53 40 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_40_23 : Certificate := {
  objectiveScale := 5
  eta := 11219520
  rows := #[⟨.assumptionRow 23, 3⟩]
  caps := #[0, 0, 4942470, 1776060, 740025, 284625, 110561, 46398, 16473, 7752, 28514250, 27943965, 19684665, 11759670] }

theorem case_53_40_23_checked :
    (Witness.linear .conditional case_53_40_23).check 53 40 23 = true := by
  change case_53_40_23.check 53 40 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_40_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9694845, 9694845, 7020405, 4345965] }

theorem case_53_40_24_checked :
    (Witness.linear .negative case_53_40_24).check 53 40 24 = true := by
  change case_53_40_24.check 53 40 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_40_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440, 2674440] }

theorem case_53_40_25_checked :
    (Witness.linear .negative case_53_40_25).check 53 40 25 = true := by
  change case_53_40_25.check 53 40 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_40_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_40_26_checked :
    (Witness.linear .negative case_53_40_26).check 53 40 26 = true := by
  change case_53_40_26.check 53 40 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_41_1_checked :
    (Witness.rising).check 53 41 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_41_2_checked :
    (Witness.rising).check 53 41 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_41_3_checked :
    (Witness.rising).check 53 41 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_41_4_checked :
    (Witness.rising).check 53 41 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_41_5_checked :
    (Witness.rising).check 53 41 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_41_6_checked :
    (Witness.rising).check 53 41 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_41_7_checked :
    (Witness.rising).check 53 41 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_41_8_checked :
    (Witness.rising).check 53 41 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_41_9_checked :
    (Witness.rising).check 53 41 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_41_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_53_41_10_checked :
    (Witness.linear .positive case_53_41_10).check 53 41 10 = true := by
  change case_53_41_10.check 53 41 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_41_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_53_41_11_checked :
    (Witness.linear .positive case_53_41_11).check 53 41 11 = true := by
  change case_53_41_11.check 53 41 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_41_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_53_41_12_checked :
    (Witness.linear .positive case_53_41_12).check 53 41 12 = true := by
  change case_53_41_12.check 53 41 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_41_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_53_41_13_checked :
    (Witness.linear .positive case_53_41_13).check 53 41 13 = true := by
  change case_53_41_13.check 53 41 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_41_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_53_41_14_checked :
    (Witness.linear .positive case_53_41_14).check 53 41 14 = true := by
  change case_53_41_14.check 53 41 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_41_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_53_41_15_checked :
    (Witness.linear .positive case_53_41_15).check 53 41 15 = true := by
  change case_53_41_15.check 53 41 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_41_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_53_41_16_checked :
    (Witness.linear .positive case_53_41_16).check 53 41 16 = true := by
  change case_53_41_16.check 53 41 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_41_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_53_41_17_checked :
    (Witness.linear .positive case_53_41_17).check 53 41 17 = true := by
  change case_53_41_17.check 53 41 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_41_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_53_41_18_checked :
    (Witness.linear .positive case_53_41_18).check 53 41 18 = true := by
  change case_53_41_18.check 53 41 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_41_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_53_41_19_checked :
    (Witness.linear .positive case_53_41_19).check 53 41 19 = true := by
  change case_53_41_19.check 53 41 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_41_20 : Certificate := {
  objectiveScale := 17
  eta := 7771863990
  rows := #[⟨.assumptionRow 20, 45⟩]
  caps := #[0, 0, 2133866400, 589294500, 164812365, 46468395, 13223620, 3803648, 1107890, 327522, 98566, 30316, 9581] }

theorem case_53_41_20_checked :
    (Witness.linear .conditional case_53_41_20).check 53 41 20 = true := by
  change case_53_41_20.check 53 41 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_41_21 : Certificate := {
  objectiveScale := 993
  eta := 57562286760
  rows := #[⟨.assumptionRow 21, 1117⟩]
  caps := #[0, 0, 17847559320, 5515956600, 1701828765, 525038020, 162212215, 50253632, 27293640, 12639436560, 11015464980, 6831013800, 3552465345] }

theorem case_53_41_21_checked :
    (Witness.linear .conditional case_53_41_21).check 53 41 21 = true := by
  change case_53_41_21.check 53 41 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_41_22 : Certificate := {
  objectiveScale := 998
  eta := 32717630640
  rows := #[⟨.assumptionRow 22, 887⟩]
  caps := #[0, 0, 11267310840, 3731955045, 1203621510, 380882645, 127794095, 45272326, 27293640, 15971741880, 14932722630, 9997706355, 5654836005] }

theorem case_53_41_22_checked :
    (Witness.linear .conditional case_53_41_22).check 53 41 22 = true := by
  change case_53_41_22.check 53 41 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_41_23 : Certificate := {
  objectiveScale := 32
  eta := 66966510
  rows := #[⟨.assumptionRow 23, 19⟩]
  caps := #[0, 0, 28484235, 10607025, 4242810, 1701425, 629717, 277761, 100776, 660009840, 648223950, 459079425, 276778320] }

theorem case_53_41_23_checked :
    (Witness.linear .conditional case_53_41_23).check 53 41 23 = true := by
  change case_53_41_23.check 53 41 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_41_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 35357670, 35357670, 25662825, 15967980] }

theorem case_53_41_24_checked :
    (Witness.linear .negative case_53_41_24).check 53 41 24 = true := by
  change case_53_41_24.check 53 41 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_41_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9694845, 9694845] }

theorem case_53_41_25_checked :
    (Witness.linear .negative case_53_41_25).check 53 41 25 = true := by
  change case_53_41_25.check 53 41 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_41_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_41_26_checked :
    (Witness.linear .negative case_53_41_26).check 53 41 26 = true := by
  change case_53_41_26.check 53 41 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_42_1_checked :
    (Witness.rising).check 53 42 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_42_2_checked :
    (Witness.rising).check 53 42 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_42_3_checked :
    (Witness.rising).check 53 42 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_42_4_checked :
    (Witness.rising).check 53 42 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_42_5_checked :
    (Witness.rising).check 53 42 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_42_6_checked :
    (Witness.rising).check 53 42 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_42_7_checked :
    (Witness.rising).check 53 42 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_42_8_checked :
    (Witness.rising).check 53 42 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_42_9_checked :
    (Witness.rising).check 53 42 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_42_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_53_42_10_checked :
    (Witness.linear .positive case_53_42_10).check 53 42 10 = true := by
  change case_53_42_10.check 53 42 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_42_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_53_42_11_checked :
    (Witness.linear .positive case_53_42_11).check 53 42 11 = true := by
  change case_53_42_11.check 53 42 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_42_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_53_42_12_checked :
    (Witness.linear .positive case_53_42_12).check 53 42 12 = true := by
  change case_53_42_12.check 53 42 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_42_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_53_42_13_checked :
    (Witness.linear .positive case_53_42_13).check 53 42 13 = true := by
  change case_53_42_13.check 53 42 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_42_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_53_42_14_checked :
    (Witness.linear .positive case_53_42_14).check 53 42 14 = true := by
  change case_53_42_14.check 53 42 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_42_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_53_42_15_checked :
    (Witness.linear .positive case_53_42_15).check 53 42 15 = true := by
  change case_53_42_15.check 53 42 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_42_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_53_42_16_checked :
    (Witness.linear .positive case_53_42_16).check 53 42 16 = true := by
  change case_53_42_16.check 53 42 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_42_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_53_42_17_checked :
    (Witness.linear .positive case_53_42_17).check 53 42 17 = true := by
  change case_53_42_17.check 53 42 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_42_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_53_42_18_checked :
    (Witness.linear .positive case_53_42_18).check 53 42 18 = true := by
  change case_53_42_18.check 53 42 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_42_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_53_42_19_checked :
    (Witness.linear .positive case_53_42_19).check 53 42 19 = true := by
  change case_53_42_19.check 53 42 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_42_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_53_42_20_checked :
    (Witness.linear .positive case_53_42_20).check 53 42 20 = true := by
  change case_53_42_20.check 53 42 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_42_21 : Certificate := {
  objectiveScale := 19
  eta := 2783951280
  rows := #[⟨.assumptionRow 21, 25⟩]
  caps := #[0, 0, 791515560, 235717800, 70525245, 21218535, 6426085, 1961256, 604010, 116618280, 225792840, 161280600] }

theorem case_53_42_21_checked :
    (Witness.linear .conditional case_53_42_21).check 53 42 21 = true := by
  change case_53_42_21.check 53 42 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_42_22 : Certificate := {
  objectiveScale := 1
  eta := 84362160
  rows := #[⟨.assumptionRow 22, 1⟩]
  caps := #[0, 0, 27293640, 8684340, 2731365, 852150, 264385, 81719, 28424, 27293640, 24812400, 16128060] }

theorem case_53_42_22_checked :
    (Witness.linear .conditional case_53_42_22).check 53 42 22 = true := by
  change case_53_42_22.check 53 42 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_42_23 : Certificate := {
  objectiveScale := 4
  eta := 89864040
  rows := #[⟨.assumptionRow 23, 3⟩]
  caps := #[0, 0, 32256120, 10795395, 3641820, 1381380, 480700, 158631, 63954, 136468200, 131505720, 91185570] }

theorem case_53_42_23_checked :
    (Witness.linear .conditional case_53_42_23).check 53 42 23 = true := by
  change case_53_42_23.check 53 42 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_42_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 129644790, 129644790, 94287120, 58929450] }

theorem case_53_42_24_checked :
    (Witness.linear .negative case_53_42_24).check 53 42 24 = true := by
  change case_53_42_24.check 53 42 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_42_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35357670, 35357670] }

theorem case_53_42_25_checked :
    (Witness.linear .negative case_53_42_25).check 53 42 25 = true := by
  change case_53_42_25.check 53 42 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_42_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_42_26_checked :
    (Witness.linear .negative case_53_42_26).check 53 42 26 = true := by
  change case_53_42_26.check 53 42 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_42_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_42_27_checked :
    (Witness.linear .negative case_53_42_27).check 53 42 27 = true := by
  change case_53_42_27.check 53 42 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_43_1_checked :
    (Witness.rising).check 53 43 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_43_2_checked :
    (Witness.rising).check 53 43 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_43_3_checked :
    (Witness.rising).check 53 43 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_43_4_checked :
    (Witness.rising).check 53 43 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_43_5_checked :
    (Witness.rising).check 53 43 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_43_6_checked :
    (Witness.rising).check 53 43 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_43_7_checked :
    (Witness.rising).check 53 43 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_43_8_checked :
    (Witness.rising).check 53 43 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_43_9_checked :
    (Witness.rising).check 53 43 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_43_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_53_43_10_checked :
    (Witness.linear .positive case_53_43_10).check 53 43 10 = true := by
  change case_53_43_10.check 53 43 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_43_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_53_43_11_checked :
    (Witness.linear .positive case_53_43_11).check 53 43 11 = true := by
  change case_53_43_11.check 53 43 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_43_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_53_43_12_checked :
    (Witness.linear .positive case_53_43_12).check 53 43 12 = true := by
  change case_53_43_12.check 53 43 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_43_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_53_43_13_checked :
    (Witness.linear .positive case_53_43_13).check 53 43 13 = true := by
  change case_53_43_13.check 53 43 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_43_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_53_43_14_checked :
    (Witness.linear .positive case_53_43_14).check 53 43 14 = true := by
  change case_53_43_14.check 53 43 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_43_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_53_43_15_checked :
    (Witness.linear .positive case_53_43_15).check 53 43 15 = true := by
  change case_53_43_15.check 53 43 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_43_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_53_43_16_checked :
    (Witness.linear .positive case_53_43_16).check 53 43 16 = true := by
  change case_53_43_16.check 53 43 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_43_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_53_43_17_checked :
    (Witness.linear .positive case_53_43_17).check 53 43 17 = true := by
  change case_53_43_17.check 53 43 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_43_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_53_43_18_checked :
    (Witness.linear .positive case_53_43_18).check 53 43 18 = true := by
  change case_53_43_18.check 53 43 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_43_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_53_43_19_checked :
    (Witness.linear .positive case_53_43_19).check 53 43 19 = true := by
  change case_53_43_19.check 53 43 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_43_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_53_43_20_checked :
    (Witness.linear .positive case_53_43_20).check 53 43 20 = true := by
  change case_53_43_20.check 53 43 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_43_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_53_43_21_checked :
    (Witness.linear .positive case_53_43_21).check 53 43 21 = true := by
  change case_53_43_21.check 53 43 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_43_22 : Certificate := {
  objectiveScale := 991
  eta := 175473292800
  rows := #[⟨.assumptionRow 22, 1090⟩]
  caps := #[0, 0, 51366630480, 15054303390, 4681489575, 1476946380, 464222915, 145704977, 84362160, 46019558280, 40588123920] }

theorem case_53_43_22_checked :
    (Witness.linear .conditional case_53_43_22).check 53 43 22 = true := by
  change case_53_43_22.check 53 43 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_43_23 : Certificate := {
  objectiveScale := 537
  eta := 10261006200
  rows := #[⟨.assumptionRow 23, 398⟩]
  caps := #[0, 0, 3870734400, 1332515925, 434098665, 167640330, 59967325, 20470230, 66698832750, 64494871320, 45007212360] }

theorem case_53_43_23_checked :
    (Witness.linear .conditional case_53_43_23).check 53 43 23 = true := by
  change case_53_43_23.check 53 43 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_43_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 477638700, 477638700, 347993910, 218349120] }

theorem case_53_43_24_checked :
    (Witness.linear .negative case_53_43_24).check 53 43 24 = true := by
  change case_53_43_24.check 53 43 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_43_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 129644790, 129644790] }

theorem case_53_43_25_checked :
    (Witness.linear .negative case_53_43_25).check 53 43 25 = true := by
  change case_53_43_25.check 53 43 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_43_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_43_26_checked :
    (Witness.linear .negative case_53_43_26).check 53 43 26 = true := by
  change case_53_43_26.check 53 43 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_43_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_43_27_checked :
    (Witness.linear .negative case_53_43_27).check 53 43 27 = true := by
  change case_53_43_27.check 53 43 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_43_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_43_28_checked :
    (Witness.linear .negative case_53_43_28).check 53 43 28 = true := by
  change case_53_43_28.check 53 43 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_44_1_checked :
    (Witness.rising).check 53 44 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_44_2_checked :
    (Witness.rising).check 53 44 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_44_3_checked :
    (Witness.rising).check 53 44 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_44_4_checked :
    (Witness.rising).check 53 44 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_44_5_checked :
    (Witness.rising).check 53 44 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_44_6_checked :
    (Witness.rising).check 53 44 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_44_7_checked :
    (Witness.rising).check 53 44 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_44_8_checked :
    (Witness.rising).check 53 44 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_44_9_checked :
    (Witness.rising).check 53 44 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_44_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_53_44_10_checked :
    (Witness.linear .positive case_53_44_10).check 53 44 10 = true := by
  change case_53_44_10.check 53 44 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_44_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_53_44_11_checked :
    (Witness.linear .positive case_53_44_11).check 53 44 11 = true := by
  change case_53_44_11.check 53 44 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_44_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_53_44_12_checked :
    (Witness.linear .positive case_53_44_12).check 53 44 12 = true := by
  change case_53_44_12.check 53 44 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_44_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_53_44_13_checked :
    (Witness.linear .positive case_53_44_13).check 53 44 13 = true := by
  change case_53_44_13.check 53 44 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_44_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_53_44_14_checked :
    (Witness.linear .positive case_53_44_14).check 53 44 14 = true := by
  change case_53_44_14.check 53 44 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_44_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_53_44_15_checked :
    (Witness.linear .positive case_53_44_15).check 53 44 15 = true := by
  change case_53_44_15.check 53 44 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_44_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_53_44_16_checked :
    (Witness.linear .positive case_53_44_16).check 53 44 16 = true := by
  change case_53_44_16.check 53 44 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_44_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_53_44_17_checked :
    (Witness.linear .positive case_53_44_17).check 53 44 17 = true := by
  change case_53_44_17.check 53 44 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_44_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_53_44_18_checked :
    (Witness.linear .positive case_53_44_18).check 53 44 18 = true := by
  change case_53_44_18.check 53 44 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_44_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_53_44_19_checked :
    (Witness.linear .positive case_53_44_19).check 53 44 19 = true := by
  change case_53_44_19.check 53 44 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_44_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_53_44_20_checked :
    (Witness.linear .positive case_53_44_20).check 53 44 20 = true := by
  change case_53_44_20.check 53 44 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_44_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_53_44_21_checked :
    (Witness.linear .positive case_53_44_21).check 53 44 21 = true := by
  change case_53_44_21.check 53 44 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_44_22 : Certificate := {
  objectiveScale := 19
  eta := 30227085990
  rows := #[⟨.assumptionRow 22, 32⟩]
  caps := #[0, 0, 8351853840, 2319959400, 660009840, 189144525, 54649035, 15935205, 4695128, 1399882] }

theorem case_53_44_22_checked :
    (Witness.linear .conditional case_53_44_22).check 53 44 22 = true := by
  change case_53_44_22.check 53 44 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_44_23 : Certificate := {
  objectiveScale := 641
  eta := 55073818800
  rows := #[⟨.assumptionRow 23, 553⟩]
  caps := #[0, 0, 17366198760, 5370643980, 1864611840, 633551100, 208095030, 68854410, 135622717470, 128314845360] }

theorem case_53_44_23_checked :
    (Witness.linear .conditional case_53_44_23).check 53 44 23 = true := by
  change case_53_44_23.check 53 44 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_44_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 1767263190, 1767263190, 1289624490, 811985790] }

theorem case_53_44_24_checked :
    (Witness.linear .negative case_53_44_24).check 53 44 24 = true := by
  change case_53_44_24.check 53 44 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_44_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 477638700, 477638700] }

theorem case_53_44_25_checked :
    (Witness.linear .negative case_53_44_25).check 53 44 25 = true := by
  change case_53_44_25.check 53 44 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_44_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_44_26_checked :
    (Witness.linear .negative case_53_44_26).check 53 44 26 = true := by
  change case_53_44_26.check 53 44 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_44_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_44_27_checked :
    (Witness.linear .negative case_53_44_27).check 53 44 27 = true := by
  change case_53_44_27.check 53 44 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_44_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_44_28_checked :
    (Witness.linear .negative case_53_44_28).check 53 44 28 = true := by
  change case_53_44_28.check 53 44 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_45_1_checked :
    (Witness.rising).check 53 45 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_45_2_checked :
    (Witness.rising).check 53 45 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_45_3_checked :
    (Witness.rising).check 53 45 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_45_4_checked :
    (Witness.rising).check 53 45 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_45_5_checked :
    (Witness.rising).check 53 45 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_45_6_checked :
    (Witness.rising).check 53 45 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_45_7_checked :
    (Witness.rising).check 53 45 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_45_8_checked :
    (Witness.rising).check 53 45 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_45_9_checked :
    (Witness.rising).check 53 45 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_45_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_53_45_10_checked :
    (Witness.linear .positive case_53_45_10).check 53 45 10 = true := by
  change case_53_45_10.check 53 45 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_45_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_53_45_11_checked :
    (Witness.linear .positive case_53_45_11).check 53 45 11 = true := by
  change case_53_45_11.check 53 45 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_45_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_53_45_12_checked :
    (Witness.linear .positive case_53_45_12).check 53 45 12 = true := by
  change case_53_45_12.check 53 45 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_45_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_53_45_13_checked :
    (Witness.linear .positive case_53_45_13).check 53 45 13 = true := by
  change case_53_45_13.check 53 45 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_45_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_53_45_14_checked :
    (Witness.linear .positive case_53_45_14).check 53 45 14 = true := by
  change case_53_45_14.check 53 45 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_45_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_53_45_15_checked :
    (Witness.linear .positive case_53_45_15).check 53 45 15 = true := by
  change case_53_45_15.check 53 45 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_45_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_53_45_16_checked :
    (Witness.linear .positive case_53_45_16).check 53 45 16 = true := by
  change case_53_45_16.check 53 45 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_45_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_53_45_17_checked :
    (Witness.linear .positive case_53_45_17).check 53 45 17 = true := by
  change case_53_45_17.check 53 45 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_45_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_53_45_18_checked :
    (Witness.linear .positive case_53_45_18).check 53 45 18 = true := by
  change case_53_45_18.check 53 45 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_45_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_53_45_19_checked :
    (Witness.linear .positive case_53_45_19).check 53 45 19 = true := by
  change case_53_45_19.check 53 45 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_45_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_53_45_20_checked :
    (Witness.linear .positive case_53_45_20).check 53 45 20 = true := by
  change case_53_45_20.check 53 45 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_45_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_53_45_21_checked :
    (Witness.linear .positive case_53_45_21).check 53 45 21 = true := by
  change case_53_45_21.check 53 45 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_45_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_53_45_22_checked :
    (Witness.linear .positive case_53_45_22).check 53 45 22 = true := by
  change case_53_45_22.check 53 45 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_45_23 : Certificate := {
  objectiveScale := 743
  eta := 168280501680
  rows := #[⟨.assumptionRow 23, 718⟩]
  caps := #[0, 0, 51081287880, 15396094200, 4824150870, 1596938070, 518107200, 170639190, 270493052850] }

theorem case_53_45_23_checked :
    (Witness.linear .conditional case_53_45_23).check 53 45 23 = true := by
  change case_53_45_23.check 53 45 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_45_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 6564120420, 6564120420, 4796857230, 3029594040] }

theorem case_53_45_24_checked :
    (Witness.linear .negative case_53_45_24).check 53 45 24 = true := by
  change case_53_45_24.check 53 45 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_45_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 1767263190, 1767263190] }

theorem case_53_45_25_checked :
    (Witness.linear .negative case_53_45_25).check 53 45 25 = true := by
  change case_53_45_25.check 53 45 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_45_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_45_26_checked :
    (Witness.linear .negative case_53_45_26).check 53 45 26 = true := by
  change case_53_45_26.check 53 45 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_45_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_45_27_checked :
    (Witness.linear .negative case_53_45_27).check 53 45 27 = true := by
  change case_53_45_27.check 53 45 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_45_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_45_28_checked :
    (Witness.linear .negative case_53_45_28).check 53 45 28 = true := by
  change case_53_45_28.check 53 45 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_45_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_45_29_checked :
    (Witness.linear .negative case_53_45_29).check 53 45 29 = true := by
  change case_53_45_29.check 53 45 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_46_1_checked :
    (Witness.rising).check 53 46 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_46_2_checked :
    (Witness.rising).check 53 46 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_46_3_checked :
    (Witness.rising).check 53 46 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_46_4_checked :
    (Witness.rising).check 53 46 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_46_5_checked :
    (Witness.rising).check 53 46 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_46_6_checked :
    (Witness.rising).check 53 46 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_46_7_checked :
    (Witness.rising).check 53 46 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_46_8_checked :
    (Witness.rising).check 53 46 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_46_9_checked :
    (Witness.rising).check 53 46 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_46_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_53_46_10_checked :
    (Witness.linear .positive case_53_46_10).check 53 46 10 = true := by
  change case_53_46_10.check 53 46 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_46_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_53_46_11_checked :
    (Witness.linear .positive case_53_46_11).check 53 46 11 = true := by
  change case_53_46_11.check 53 46 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_46_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_53_46_12_checked :
    (Witness.linear .positive case_53_46_12).check 53 46 12 = true := by
  change case_53_46_12.check 53 46 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_46_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42] }

theorem case_53_46_13_checked :
    (Witness.linear .positive case_53_46_13).check 53 46 13 = true := by
  change case_53_46_13.check 53 46 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_46_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_53_46_14_checked :
    (Witness.linear .positive case_53_46_14).check 53 46 14 = true := by
  change case_53_46_14.check 53 46 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_46_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_53_46_15_checked :
    (Witness.linear .positive case_53_46_15).check 53 46 15 = true := by
  change case_53_46_15.check 53 46 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_46_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_53_46_16_checked :
    (Witness.linear .positive case_53_46_16).check 53 46 16 = true := by
  change case_53_46_16.check 53 46 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_46_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_53_46_17_checked :
    (Witness.linear .positive case_53_46_17).check 53 46 17 = true := by
  change case_53_46_17.check 53 46 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_46_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_53_46_18_checked :
    (Witness.linear .positive case_53_46_18).check 53 46 18 = true := by
  change case_53_46_18.check 53 46 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_46_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_53_46_19_checked :
    (Witness.linear .positive case_53_46_19).check 53 46 19 = true := by
  change case_53_46_19.check 53 46 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_46_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_53_46_20_checked :
    (Witness.linear .positive case_53_46_20).check 53 46 20 = true := by
  change case_53_46_20.check 53 46 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_46_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_53_46_21_checked :
    (Witness.linear .positive case_53_46_21).check 53 46 21 = true := by
  change case_53_46_21.check 53 46 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_46_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845, 2674440] }

theorem case_53_46_22_checked :
    (Witness.linear .positive case_53_46_22).check 53 46 22 = true := by
  change case_53_46_22.check 53 46 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_46_23 : Certificate := {
  objectiveScale := 7
  eta := 167605604400
  rows := #[⟨.assumptionRow 23, 19⟩]
  caps := #[0, 0, 45352104720, 12370842330, 3391234770, 934807170, 259289580, 72426195] }

theorem case_53_46_23_checked :
    (Witness.linear .conditional case_53_46_23).check 53 46 23 = true := by
  change case_53_46_23.check 53 46 23 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_46_24 : Certificate := {
  objectiveScale := 40
  eta := 162683040
  rows := #[⟨.assumptionRow 24, 23⟩]
  caps := #[0, 0, 65564070, 23801895, 10409685, 3700125, 149184555000, 147394340340] }

theorem case_53_46_24_checked :
    (Witness.linear .conditional case_53_46_24).check 53 46 24 = true := by
  change case_53_46_24.check 53 46 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_46_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 6564120420, 6564120420] }

theorem case_53_46_25_checked :
    (Witness.linear .negative case_53_46_25).check 53 46 25 = true := by
  change case_53_46_25.check 53 46 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_46_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_46_26_checked :
    (Witness.linear .negative case_53_46_26).check 53 46 26 = true := by
  change case_53_46_26.check 53 46 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_46_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_46_27_checked :
    (Witness.linear .negative case_53_46_27).check 53 46 27 = true := by
  change case_53_46_27.check 53 46 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_46_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_46_28_checked :
    (Witness.linear .negative case_53_46_28).check 53 46 28 = true := by
  change case_53_46_28.check 53 46 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_46_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_46_29_checked :
    (Witness.linear .negative case_53_46_29).check 53 46 29 = true := by
  change case_53_46_29.check 53 46 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_46_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_53_46_30_checked :
    (Witness.linear .negative case_53_46_30).check 53 46 30 = true := by
  change case_53_46_30.check 53 46 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_47_1_checked :
    (Witness.rising).check 53 47 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_47_2_checked :
    (Witness.rising).check 53 47 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_47_3_checked :
    (Witness.rising).check 53 47 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_47_4_checked :
    (Witness.rising).check 53 47 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_47_5_checked :
    (Witness.rising).check 53 47 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_47_6_checked :
    (Witness.rising).check 53 47 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_47_7_checked :
    (Witness.rising).check 53 47 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_47_8_checked :
    (Witness.rising).check 53 47 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_47_9_checked :
    (Witness.rising).check 53 47 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_47_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_53_47_10_checked :
    (Witness.linear .positive case_53_47_10).check 53 47 10 = true := by
  change case_53_47_10.check 53 47 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_47_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_53_47_11_checked :
    (Witness.linear .positive case_53_47_11).check 53 47 11 = true := by
  change case_53_47_11.check 53 47 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_47_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_53_47_12_checked :
    (Witness.linear .positive case_53_47_12).check 53 47 12 = true := by
  change case_53_47_12.check 53 47 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_47_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_53_47_13_checked :
    (Witness.linear .positive case_53_47_13).check 53 47 13 = true := by
  change case_53_47_13.check 53 47 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_47_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429] }

theorem case_53_47_14_checked :
    (Witness.linear .positive case_53_47_14).check 53 47 14 = true := by
  change case_53_47_14.check 53 47 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_47_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430] }

theorem case_53_47_15_checked :
    (Witness.linear .positive case_53_47_15).check 53 47 15 = true := by
  change case_53_47_15.check 53 47 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_47_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862] }

theorem case_53_47_16_checked :
    (Witness.linear .positive case_53_47_16).check 53 47 16 = true := by
  change case_53_47_16.check 53 47 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_47_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796] }

theorem case_53_47_17_checked :
    (Witness.linear .positive case_53_47_17).check 53 47 17 = true := by
  change case_53_47_17.check 53 47 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_47_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_53_47_18_checked :
    (Witness.linear .positive case_53_47_18).check 53 47 18 = true := by
  change case_53_47_18.check 53 47 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_47_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_53_47_19_checked :
    (Witness.linear .positive case_53_47_19).check 53 47 19 = true := by
  change case_53_47_19.check 53 47 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_47_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_53_47_20_checked :
    (Witness.linear .positive case_53_47_20).check 53 47 20 = true := by
  change case_53_47_20.check 53 47 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_47_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440] }

theorem case_53_47_21_checked :
    (Witness.linear .positive case_53_47_21).check 53 47 21 = true := by
  change case_53_47_21.check 53 47 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_47_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670, 9694845] }

theorem case_53_47_22_checked :
    (Witness.linear .positive case_53_47_22).check 53 47 22 = true := by
  change case_53_47_22.check 53 47 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_47_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700, 129644790, 35357670] }

theorem case_53_47_23_checked :
    (Witness.linear .positive case_53_47_23).check 53 47 23 = true := by
  change case_53_47_23.check 53 47 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_47_24 : Certificate := {
  objectiveScale := 19
  eta := 3766036860
  rows := #[⟨.assumptionRow 24, 16⟩]
  caps := #[0, 0, 1302111600, 429254520, 137088510, 42791385, 15509130] }

theorem case_53_47_24_checked :
    (Witness.linear .conditional case_53_47_24).check 53 47 24 = true := by
  change case_53_47_24.check 53 47 24 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_47_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 24466267020, 24466267020] }

theorem case_53_47_25_checked :
    (Witness.linear .negative case_53_47_25).check 53 47 25 = true := by
  change case_53_47_25.check 53 47 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_47_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_53_47_26_checked :
    (Witness.linear .negative case_53_47_26).check 53 47 26 = true := by
  change case_53_47_26.check 53 47 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_47_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_53_47_27_checked :
    (Witness.linear .negative case_53_47_27).check 53 47 27 = true := by
  change case_53_47_27.check 53 47 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_47_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_53_47_28_checked :
    (Witness.linear .negative case_53_47_28).check 53 47 28 = true := by
  change case_53_47_28.check 53 47 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_47_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_53_47_29_checked :
    (Witness.linear .negative case_53_47_29).check 53 47 29 = true := by
  change case_53_47_29.check 53 47 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_47_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_53_47_30_checked :
    (Witness.linear .negative case_53_47_30).check 53 47 30 = true := by
  change case_53_47_30.check 53 47 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_48_1_checked :
    (Witness.rising).check 53 48 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_48_2_checked :
    (Witness.rising).check 53 48 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_48_3_checked :
    (Witness.rising).check 53 48 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_48_4_checked :
    (Witness.rising).check 53 48 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_48_5_checked :
    (Witness.rising).check 53 48 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_48_6_checked :
    (Witness.rising).check 53 48 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_48_7_checked :
    (Witness.rising).check 53 48 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_48_8_checked :
    (Witness.rising).check 53 48 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_48_9_checked :
    (Witness.rising).check 53 48 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_48_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_53_48_10_checked :
    (Witness.linear .positive case_53_48_10).check 53 48 10 = true := by
  change case_53_48_10.check 53 48 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_48_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_53_48_11_checked :
    (Witness.linear .positive case_53_48_11).check 53 48 11 = true := by
  change case_53_48_11.check 53 48 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_48_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_53_48_12_checked :
    (Witness.linear .positive case_53_48_12).check 53 48 12 = true := by
  change case_53_48_12.check 53 48 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_48_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_53_48_13_checked :
    (Witness.linear .positive case_53_48_13).check 53 48 13 = true := by
  change case_53_48_13.check 53 48 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_48_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_53_48_14_checked :
    (Witness.linear .positive case_53_48_14).check 53 48 14 = true := by
  change case_53_48_14.check 53 48 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_48_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862] }

theorem case_53_48_15_checked :
    (Witness.linear .positive case_53_48_15).check 53 48 15 = true := by
  change case_53_48_15.check 53 48 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_48_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796] }

theorem case_53_48_16_checked :
    (Witness.linear .positive case_53_48_16).check 53 48 16 = true := by
  change case_53_48_16.check 53 48 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_48_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786] }

theorem case_53_48_17_checked :
    (Witness.linear .positive case_53_48_17).check 53 48 17 = true := by
  change case_53_48_17.check 53 48 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_48_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012] }

theorem case_53_48_18_checked :
    (Witness.linear .positive case_53_48_18).check 53 48 18 = true := by
  change case_53_48_18.check 53 48 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_48_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900] }

theorem case_53_48_19_checked :
    (Witness.linear .positive case_53_48_19).check 53 48 19 = true := by
  change case_53_48_19.check 53 48 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_48_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440] }

theorem case_53_48_20_checked :
    (Witness.linear .positive case_53_48_20).check 53 48 20 = true := by
  change case_53_48_20.check 53 48 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_48_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845] }

theorem case_53_48_21_checked :
    (Witness.linear .positive case_53_48_21).check 53 48 21 = true := by
  change case_53_48_21.check 53 48 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_48_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670] }

theorem case_53_48_22_checked :
    (Witness.linear .positive case_53_48_22).check 53 48 22 = true := by
  change case_53_48_22.check 53 48 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_48_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700, 129644790] }

theorem case_53_48_23_checked :
    (Witness.linear .positive case_53_48_23).check 53 48 23 = true := by
  change case_53_48_23.check 53 48 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_48_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420, 1767263190, 477638700] }

theorem case_53_48_24_checked :
    (Witness.linear .positive case_53_48_24).check 53 48 24 = true := by
  change case_53_48_24.check 53 48 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_48_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 91482563640, 91482563640] }

theorem case_53_48_25_checked :
    (Witness.linear .negative case_53_48_25).check 53 48 25 = true := by
  change case_53_48_25.check 53 48 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_48_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_53_48_26_checked :
    (Witness.linear .negative case_53_48_26).check 53 48 26 = true := by
  change case_53_48_26.check 53 48 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_48_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_53_48_27_checked :
    (Witness.linear .negative case_53_48_27).check 53 48 27 = true := by
  change case_53_48_27.check 53 48 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_48_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_53_48_28_checked :
    (Witness.linear .negative case_53_48_28).check 53 48 28 = true := by
  change case_53_48_28.check 53 48 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_48_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_53_48_29_checked :
    (Witness.linear .negative case_53_48_29).check 53 48 29 = true := by
  change case_53_48_29.check 53 48 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_48_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_53_48_30_checked :
    (Witness.linear .negative case_53_48_30).check 53 48 30 = true := by
  change case_53_48_30.check 53 48 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_48_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_53_48_31_checked :
    (Witness.linear .negative case_53_48_31).check 53 48 31 = true := by
  change case_53_48_31.check 53 48 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_49_1_checked :
    (Witness.rising).check 53 49 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_49_2_checked :
    (Witness.rising).check 53 49 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_49_3_checked :
    (Witness.rising).check 53 49 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_49_4_checked :
    (Witness.rising).check 53 49 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_49_5_checked :
    (Witness.rising).check 53 49 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_49_6_checked :
    (Witness.rising).check 53 49 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_49_7_checked :
    (Witness.rising).check 53 49 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_49_8_checked :
    (Witness.rising).check 53 49 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_49_9_checked :
    (Witness.rising).check 53 49 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_49_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_53_49_10_checked :
    (Witness.linear .positive case_53_49_10).check 53 49 10 = true := by
  change case_53_49_10.check 53 49 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_49_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_53_49_11_checked :
    (Witness.linear .positive case_53_49_11).check 53 49 11 = true := by
  change case_53_49_11.check 53 49 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_49_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_53_49_12_checked :
    (Witness.linear .positive case_53_49_12).check 53 49 12 = true := by
  change case_53_49_12.check 53 49 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_49_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_53_49_13_checked :
    (Witness.linear .positive case_53_49_13).check 53 49 13 = true := by
  change case_53_49_13.check 53 49 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_49_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_53_49_14_checked :
    (Witness.linear .positive case_53_49_14).check 53 49 14 = true := by
  change case_53_49_14.check 53 49 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_49_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796] }

theorem case_53_49_15_checked :
    (Witness.linear .positive case_53_49_15).check 53 49 15 = true := by
  change case_53_49_15.check 53 49 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_49_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786] }

theorem case_53_49_16_checked :
    (Witness.linear .positive case_53_49_16).check 53 49 16 = true := by
  change case_53_49_16.check 53 49 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_49_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012] }

theorem case_53_49_17_checked :
    (Witness.linear .positive case_53_49_17).check 53 49 17 = true := by
  change case_53_49_17.check 53 49 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_49_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900] }

theorem case_53_49_18_checked :
    (Witness.linear .positive case_53_49_18).check 53 49 18 = true := by
  change case_53_49_18.check 53 49 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_49_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440] }

theorem case_53_49_19_checked :
    (Witness.linear .positive case_53_49_19).check 53 49 19 = true := by
  change case_53_49_19.check 53 49 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_49_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845] }

theorem case_53_49_20_checked :
    (Witness.linear .positive case_53_49_20).check 53 49 20 = true := by
  change case_53_49_20.check 53 49 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_49_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670] }

theorem case_53_49_21_checked :
    (Witness.linear .positive case_53_49_21).check 53 49 21 = true := by
  change case_53_49_21.check 53 49 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_49_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790] }

theorem case_53_49_22_checked :
    (Witness.linear .positive case_53_49_22).check 53 49 22 = true := by
  change case_53_49_22.check 53 49 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_49_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190, 477638700] }

theorem case_53_49_23_checked :
    (Witness.linear .positive case_53_49_23).check 53 49 23 = true := by
  change case_53_49_23.check 53 49 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_49_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420, 1767263190] }

theorem case_53_49_24_checked :
    (Witness.linear .positive case_53_49_24).check 53 49 24 = true := by
  change case_53_49_24.check 53 49 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_49_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 343059613650, 343059613650] }

theorem case_53_49_25_checked :
    (Witness.linear .negative case_53_49_25).check 53 49 25 = true := by
  change case_53_49_25.check 53 49 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_49_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_53_49_26_checked :
    (Witness.linear .negative case_53_49_26).check 53 49 26 = true := by
  change case_53_49_26.check 53 49 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_49_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_53_49_27_checked :
    (Witness.linear .negative case_53_49_27).check 53 49 27 = true := by
  change case_53_49_27.check 53 49 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_49_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_53_49_28_checked :
    (Witness.linear .negative case_53_49_28).check 53 49 28 = true := by
  change case_53_49_28.check 53 49 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_49_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_53_49_29_checked :
    (Witness.linear .negative case_53_49_29).check 53 49 29 = true := by
  change case_53_49_29.check 53 49 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_49_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_53_49_30_checked :
    (Witness.linear .negative case_53_49_30).check 53 49 30 = true := by
  change case_53_49_30.check 53 49 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_49_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_53_49_31_checked :
    (Witness.linear .negative case_53_49_31).check 53 49 31 = true := by
  change case_53_49_31.check 53 49 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_49_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_53_49_32_checked :
    (Witness.linear .negative case_53_49_32).check 53 49 32 = true := by
  change case_53_49_32.check 53 49 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_50_1_checked :
    (Witness.rising).check 53 50 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_50_2_checked :
    (Witness.rising).check 53 50 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_50_3_checked :
    (Witness.rising).check 53 50 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_50_4_checked :
    (Witness.rising).check 53 50 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_50_5_checked :
    (Witness.rising).check 53 50 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_50_6_checked :
    (Witness.rising).check 53 50 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_50_7_checked :
    (Witness.rising).check 53 50 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_50_8_checked :
    (Witness.rising).check 53 50 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_50_9_checked :
    (Witness.rising).check 53 50 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_50_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_53_50_10_checked :
    (Witness.linear .positive case_53_50_10).check 53 50 10 = true := by
  change case_53_50_10.check 53 50 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_50_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_53_50_11_checked :
    (Witness.linear .positive case_53_50_11).check 53 50 11 = true := by
  change case_53_50_11.check 53 50 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_50_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_53_50_12_checked :
    (Witness.linear .positive case_53_50_12).check 53 50 12 = true := by
  change case_53_50_12.check 53 50 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_50_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_53_50_13_checked :
    (Witness.linear .positive case_53_50_13).check 53 50 13 = true := by
  change case_53_50_13.check 53 50 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_50_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_53_50_14_checked :
    (Witness.linear .positive case_53_50_14).check 53 50 14 = true := by
  change case_53_50_14.check 53 50 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_50_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_53_50_15_checked :
    (Witness.linear .positive case_53_50_15).check 53 50 15 = true := by
  change case_53_50_15.check 53 50 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_50_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012] }

theorem case_53_50_16_checked :
    (Witness.linear .positive case_53_50_16).check 53 50 16 = true := by
  change case_53_50_16.check 53 50 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_50_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900] }

theorem case_53_50_17_checked :
    (Witness.linear .positive case_53_50_17).check 53 50 17 = true := by
  change case_53_50_17.check 53 50 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_50_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440] }

theorem case_53_50_18_checked :
    (Witness.linear .positive case_53_50_18).check 53 50 18 = true := by
  change case_53_50_18.check 53 50 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_50_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845] }

theorem case_53_50_19_checked :
    (Witness.linear .positive case_53_50_19).check 53 50 19 = true := by
  change case_53_50_19.check 53 50 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_50_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670] }

theorem case_53_50_20_checked :
    (Witness.linear .positive case_53_50_20).check 53 50 20 = true := by
  change case_53_50_20.check 53 50 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_50_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790] }

theorem case_53_50_21_checked :
    (Witness.linear .positive case_53_50_21).check 53 50 21 = true := by
  change case_53_50_21.check 53 50 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_50_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700] }

theorem case_53_50_22_checked :
    (Witness.linear .positive case_53_50_22).check 53 50 22 = true := by
  change case_53_50_22.check 53 50 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_50_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190] }

theorem case_53_50_23_checked :
    (Witness.linear .positive case_53_50_23).check 53 50 23 = true := by
  change case_53_50_23.check 53 50 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_50_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020, 6564120420] }

theorem case_53_50_24_checked :
    (Witness.linear .positive case_53_50_24).check 53 50 24 = true := by
  change case_53_50_24.check 53 50 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_50_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0, 91482563640, 24466267020] }

theorem case_53_50_25_checked :
    (Witness.linear .positive case_53_50_25).check 53 50 25 = true := by
  change case_53_50_25.check 53 50 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_50_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_53_50_26_checked :
    (Witness.linear .negative case_53_50_26).check 53 50 26 = true := by
  change case_53_50_26.check 53 50 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_50_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_53_50_27_checked :
    (Witness.linear .negative case_53_50_27).check 53 50 27 = true := by
  change case_53_50_27.check 53 50 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_50_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_53_50_28_checked :
    (Witness.linear .negative case_53_50_28).check 53 50 28 = true := by
  change case_53_50_28.check 53 50 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_50_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_53_50_29_checked :
    (Witness.linear .negative case_53_50_29).check 53 50 29 = true := by
  change case_53_50_29.check 53 50 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_50_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_53_50_30_checked :
    (Witness.linear .negative case_53_50_30).check 53 50 30 = true := by
  change case_53_50_30.check 53 50 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_50_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_53_50_31_checked :
    (Witness.linear .negative case_53_50_31).check 53 50 31 = true := by
  change case_53_50_31.check 53 50 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_50_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_53_50_32_checked :
    (Witness.linear .negative case_53_50_32).check 53 50 32 = true := by
  change case_53_50_32.check 53 50 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_51_1_checked :
    (Witness.rising).check 53 51 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_51_2_checked :
    (Witness.rising).check 53 51 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_51_3_checked :
    (Witness.rising).check 53 51 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_51_4_checked :
    (Witness.rising).check 53 51 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_51_5_checked :
    (Witness.rising).check 53 51 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_51_6_checked :
    (Witness.rising).check 53 51 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_51_7_checked :
    (Witness.rising).check 53 51 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_51_8_checked :
    (Witness.rising).check 53 51 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_51_9_checked :
    (Witness.rising).check 53 51 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_51_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_53_51_10_checked :
    (Witness.linear .positive case_53_51_10).check 53 51 10 = true := by
  change case_53_51_10.check 53 51 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_51_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_53_51_11_checked :
    (Witness.linear .positive case_53_51_11).check 53 51 11 = true := by
  change case_53_51_11.check 53 51 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_51_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_53_51_12_checked :
    (Witness.linear .positive case_53_51_12).check 53 51 12 = true := by
  change case_53_51_12.check 53 51 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_51_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_53_51_13_checked :
    (Witness.linear .positive case_53_51_13).check 53 51 13 = true := by
  change case_53_51_13.check 53 51 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_51_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_53_51_14_checked :
    (Witness.linear .positive case_53_51_14).check 53 51 14 = true := by
  change case_53_51_14.check 53 51 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_51_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_53_51_15_checked :
    (Witness.linear .positive case_53_51_15).check 53 51 15 = true := by
  change case_53_51_15.check 53 51 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_51_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900] }

theorem case_53_51_16_checked :
    (Witness.linear .positive case_53_51_16).check 53 51 16 = true := by
  change case_53_51_16.check 53 51 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_51_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440] }

theorem case_53_51_17_checked :
    (Witness.linear .positive case_53_51_17).check 53 51 17 = true := by
  change case_53_51_17.check 53 51 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_51_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845] }

theorem case_53_51_18_checked :
    (Witness.linear .positive case_53_51_18).check 53 51 18 = true := by
  change case_53_51_18.check 53 51 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_51_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670] }

theorem case_53_51_19_checked :
    (Witness.linear .positive case_53_51_19).check 53 51 19 = true := by
  change case_53_51_19.check 53 51 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_51_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790] }

theorem case_53_51_20_checked :
    (Witness.linear .positive case_53_51_20).check 53 51 20 = true := by
  change case_53_51_20.check 53 51 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_51_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700] }

theorem case_53_51_21_checked :
    (Witness.linear .positive case_53_51_21).check 53 51 21 = true := by
  change case_53_51_21.check 53 51 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_51_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190] }

theorem case_53_51_22_checked :
    (Witness.linear .positive case_53_51_22).check 53 51 22 = true := by
  change case_53_51_22.check 53 51 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_51_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420] }

theorem case_53_51_23_checked :
    (Witness.linear .positive case_53_51_23).check 53 51 23 = true := by
  change case_53_51_23.check 53 51 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_51_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0, 24466267020] }

theorem case_53_51_24_checked :
    (Witness.linear .positive case_53_51_24).check 53 51 24 = true := by
  change case_53_51_24.check 53 51 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_51_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0, 91482563640] }

theorem case_53_51_25_checked :
    (Witness.linear .positive case_53_51_25).check 53 51 25 = true := by
  change case_53_51_25.check 53 51 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_51_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_53_51_26_checked :
    (Witness.linear .negative case_53_51_26).check 53 51 26 = true := by
  change case_53_51_26.check 53 51 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_51_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_53_51_27_checked :
    (Witness.linear .negative case_53_51_27).check 53 51 27 = true := by
  change case_53_51_27.check 53 51 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_51_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_53_51_28_checked :
    (Witness.linear .negative case_53_51_28).check 53 51 28 = true := by
  change case_53_51_28.check 53 51 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_51_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_53_51_29_checked :
    (Witness.linear .negative case_53_51_29).check 53 51 29 = true := by
  change case_53_51_29.check 53 51 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_51_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_53_51_30_checked :
    (Witness.linear .negative case_53_51_30).check 53 51 30 = true := by
  change case_53_51_30.check 53 51 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_51_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_53_51_31_checked :
    (Witness.linear .negative case_53_51_31).check 53 51 31 = true := by
  change case_53_51_31.check 53 51 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_51_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_53_51_32_checked :
    (Witness.linear .negative case_53_51_32).check 53 51 32 = true := by
  change case_53_51_32.check 53 51 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_51_33 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_53_51_33_checked :
    (Witness.linear .negative case_53_51_33).check 53 51 33 = true := by
  change case_53_51_33.check 53 51 33 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_52_1_checked :
    (Witness.rising).check 53 52 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_52_2_checked :
    (Witness.rising).check 53 52 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_52_3_checked :
    (Witness.rising).check 53 52 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_52_4_checked :
    (Witness.rising).check 53 52 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_52_5_checked :
    (Witness.rising).check 53 52 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_52_6_checked :
    (Witness.rising).check 53 52 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_52_7_checked :
    (Witness.rising).check 53 52 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_52_8_checked :
    (Witness.rising).check 53 52 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_53_52_9_checked :
    (Witness.rising).check 53 52 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_10_checked :
    (Witness.linear .positive case_53_52_10).check 53 52 10 = true := by
  change case_53_52_10.check 53 52 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_11_checked :
    (Witness.linear .positive case_53_52_11).check 53 52 11 = true := by
  change case_53_52_11.check 53 52 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_12_checked :
    (Witness.linear .positive case_53_52_12).check 53 52 12 = true := by
  change case_53_52_12.check 53 52 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_13_checked :
    (Witness.linear .positive case_53_52_13).check 53 52 13 = true := by
  change case_53_52_13.check 53 52 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_14_checked :
    (Witness.linear .positive case_53_52_14).check 53 52 14 = true := by
  change case_53_52_14.check 53 52 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_15_checked :
    (Witness.linear .positive case_53_52_15).check 53 52 15 = true := by
  change case_53_52_15.check 53 52 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_16_checked :
    (Witness.linear .positive case_53_52_16).check 53 52 16 = true := by
  change case_53_52_16.check 53 52 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_17_checked :
    (Witness.linear .positive case_53_52_17).check 53 52 17 = true := by
  change case_53_52_17.check 53 52 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_18_checked :
    (Witness.linear .positive case_53_52_18).check 53 52 18 = true := by
  change case_53_52_18.check 53 52 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_19_checked :
    (Witness.linear .positive case_53_52_19).check 53 52 19 = true := by
  change case_53_52_19.check 53 52 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_20_checked :
    (Witness.linear .positive case_53_52_20).check 53 52 20 = true := by
  change case_53_52_20.check 53 52 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_21_checked :
    (Witness.linear .positive case_53_52_21).check 53 52 21 = true := by
  change case_53_52_21.check 53 52 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_22_checked :
    (Witness.linear .positive case_53_52_22).check 53 52 22 = true := by
  change case_53_52_22.check 53 52 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_23_checked :
    (Witness.linear .positive case_53_52_23).check 53 52 23 = true := by
  change case_53_52_23.check 53 52 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_24_checked :
    (Witness.linear .positive case_53_52_24).check 53 52 24 = true := by
  change case_53_52_24.check 53 52 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_25 : Certificate := {
  objectiveScale := 1
  eta := 343059613650
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_25_checked :
    (Witness.linear .positive case_53_52_25).check 53 52 25 = true := by
  change case_53_52_25.check 53 52 25 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_26 : Certificate := {
  objectiveScale := 1
  eta := 1289904147324
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_26_checked :
    (Witness.linear .positive case_53_52_26).check 53 52 26 = true := by
  change case_53_52_26.check 53 52 26 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_27_checked :
    (Witness.linear .negative case_53_52_27).check 53 52 27 = true := by
  change case_53_52_27.check 53 52 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_28_checked :
    (Witness.linear .negative case_53_52_28).check 53 52 28 = true := by
  change case_53_52_28.check 53 52 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_29_checked :
    (Witness.linear .negative case_53_52_29).check 53 52 29 = true := by
  change case_53_52_29.check 53 52 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_30_checked :
    (Witness.linear .negative case_53_52_30).check 53 52 30 = true := by
  change case_53_52_30.check 53 52 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_31_checked :
    (Witness.linear .negative case_53_52_31).check 53 52 31 = true := by
  change case_53_52_31.check 53 52 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_32 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_32_checked :
    (Witness.linear .negative case_53_52_32).check 53 52 32 = true := by
  change case_53_52_32.check 53 52 32 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_33 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_33_checked :
    (Witness.linear .negative case_53_52_33).check 53 52 33 = true := by
  change case_53_52_33.check 53 52 33 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_53_52_34 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_53_52_34_checked :
    (Witness.linear .negative case_53_52_34).check 53 52 34 = true := by
  change case_53_52_34.check 53 52 34 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_53 (a k : ℕ) (h : Domain 53 a k) :
    ∃ w : Witness, w.check 53 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 27 ≤ a := by omega
  have haHi : a ≤ 52 := by omega
  interval_cases a

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_27_1_checked⟩

    · exact ⟨Witness.rising, case_53_27_2_checked⟩

    · exact ⟨Witness.rising, case_53_27_3_checked⟩

    · exact ⟨Witness.rising, case_53_27_4_checked⟩

    · exact ⟨Witness.rising, case_53_27_5_checked⟩

    · exact ⟨Witness.rising, case_53_27_6_checked⟩

    · exact ⟨Witness.rising, case_53_27_7_checked⟩

    · exact ⟨Witness.rising, case_53_27_8_checked⟩

    · exact ⟨Witness.rising, case_53_27_9_checked⟩

    · exact ⟨Witness.rising, case_53_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_27_11, case_53_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_27_12, case_53_27_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_27_13, case_53_27_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_27_14, case_53_27_14_checked⟩

    · exact ⟨Witness.linear .conditional case_53_27_15, case_53_27_15_checked⟩

    · exact ⟨Witness.linear .conditional case_53_27_16, case_53_27_16_checked⟩

    · exact ⟨Witness.linear .conditional case_53_27_17, case_53_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_28_1_checked⟩

    · exact ⟨Witness.rising, case_53_28_2_checked⟩

    · exact ⟨Witness.rising, case_53_28_3_checked⟩

    · exact ⟨Witness.rising, case_53_28_4_checked⟩

    · exact ⟨Witness.rising, case_53_28_5_checked⟩

    · exact ⟨Witness.rising, case_53_28_6_checked⟩

    · exact ⟨Witness.rising, case_53_28_7_checked⟩

    · exact ⟨Witness.rising, case_53_28_8_checked⟩

    · exact ⟨Witness.rising, case_53_28_9_checked⟩

    · exact ⟨Witness.rising, case_53_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_28_11, case_53_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_28_12, case_53_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_28_13, case_53_28_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_28_14, case_53_28_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_28_15, case_53_28_15_checked⟩

    · exact ⟨Witness.linear .conditional case_53_28_16, case_53_28_16_checked⟩

    · exact ⟨Witness.linear .conditional case_53_28_17, case_53_28_17_checked⟩

    · exact ⟨Witness.linear .conditional case_53_28_18, case_53_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_29_1_checked⟩

    · exact ⟨Witness.rising, case_53_29_2_checked⟩

    · exact ⟨Witness.rising, case_53_29_3_checked⟩

    · exact ⟨Witness.rising, case_53_29_4_checked⟩

    · exact ⟨Witness.rising, case_53_29_5_checked⟩

    · exact ⟨Witness.rising, case_53_29_6_checked⟩

    · exact ⟨Witness.rising, case_53_29_7_checked⟩

    · exact ⟨Witness.rising, case_53_29_8_checked⟩

    · exact ⟨Witness.rising, case_53_29_9_checked⟩

    · exact ⟨Witness.rising, case_53_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_29_11, case_53_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_29_12, case_53_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_29_13, case_53_29_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_29_14, case_53_29_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_29_15, case_53_29_15_checked⟩

    · exact ⟨Witness.linear .conditional case_53_29_16, case_53_29_16_checked⟩

    · exact ⟨Witness.linear .conditional case_53_29_17, case_53_29_17_checked⟩

    · exact ⟨Witness.linear .conditional case_53_29_18, case_53_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_30_1_checked⟩

    · exact ⟨Witness.rising, case_53_30_2_checked⟩

    · exact ⟨Witness.rising, case_53_30_3_checked⟩

    · exact ⟨Witness.rising, case_53_30_4_checked⟩

    · exact ⟨Witness.rising, case_53_30_5_checked⟩

    · exact ⟨Witness.rising, case_53_30_6_checked⟩

    · exact ⟨Witness.rising, case_53_30_7_checked⟩

    · exact ⟨Witness.rising, case_53_30_8_checked⟩

    · exact ⟨Witness.rising, case_53_30_9_checked⟩

    · exact ⟨Witness.rising, case_53_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_30_11, case_53_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_30_12, case_53_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_30_13, case_53_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_30_14, case_53_30_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_30_15, case_53_30_15_checked⟩

    · exact ⟨Witness.linear .conditional case_53_30_16, case_53_30_16_checked⟩

    · exact ⟨Witness.linear .conditional case_53_30_17, case_53_30_17_checked⟩

    · exact ⟨Witness.linear .conditional case_53_30_18, case_53_30_18_checked⟩

    · exact ⟨Witness.linear .conditional case_53_30_19, case_53_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_31_1_checked⟩

    · exact ⟨Witness.rising, case_53_31_2_checked⟩

    · exact ⟨Witness.rising, case_53_31_3_checked⟩

    · exact ⟨Witness.rising, case_53_31_4_checked⟩

    · exact ⟨Witness.rising, case_53_31_5_checked⟩

    · exact ⟨Witness.rising, case_53_31_6_checked⟩

    · exact ⟨Witness.rising, case_53_31_7_checked⟩

    · exact ⟨Witness.rising, case_53_31_8_checked⟩

    · exact ⟨Witness.rising, case_53_31_9_checked⟩

    · exact ⟨Witness.rising, case_53_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_31_11, case_53_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_31_12, case_53_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_31_13, case_53_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_31_14, case_53_31_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_31_15, case_53_31_15_checked⟩

    · exact ⟨Witness.linear .conditional case_53_31_16, case_53_31_16_checked⟩

    · exact ⟨Witness.linear .conditional case_53_31_17, case_53_31_17_checked⟩

    · exact ⟨Witness.linear .conditional case_53_31_18, case_53_31_18_checked⟩

    · exact ⟨Witness.linear .conditional case_53_31_19, case_53_31_19_checked⟩

    · exact ⟨Witness.linear .conditional case_53_31_20, case_53_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_32_1_checked⟩

    · exact ⟨Witness.rising, case_53_32_2_checked⟩

    · exact ⟨Witness.rising, case_53_32_3_checked⟩

    · exact ⟨Witness.rising, case_53_32_4_checked⟩

    · exact ⟨Witness.rising, case_53_32_5_checked⟩

    · exact ⟨Witness.rising, case_53_32_6_checked⟩

    · exact ⟨Witness.rising, case_53_32_7_checked⟩

    · exact ⟨Witness.rising, case_53_32_8_checked⟩

    · exact ⟨Witness.rising, case_53_32_9_checked⟩

    · exact ⟨Witness.rising, case_53_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_32_11, case_53_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_32_12, case_53_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_32_13, case_53_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_32_14, case_53_32_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_32_15, case_53_32_15_checked⟩

    · exact ⟨Witness.linear .conditional case_53_32_16, case_53_32_16_checked⟩

    · exact ⟨Witness.linear .conditional case_53_32_17, case_53_32_17_checked⟩

    · exact ⟨Witness.linear .conditional case_53_32_18, case_53_32_18_checked⟩

    · exact ⟨Witness.linear .conditional case_53_32_19, case_53_32_19_checked⟩

    · exact ⟨Witness.linear .conditional case_53_32_20, case_53_32_20_checked⟩

  · have hkHi : k ≤ 21 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_33_1_checked⟩

    · exact ⟨Witness.rising, case_53_33_2_checked⟩

    · exact ⟨Witness.rising, case_53_33_3_checked⟩

    · exact ⟨Witness.rising, case_53_33_4_checked⟩

    · exact ⟨Witness.rising, case_53_33_5_checked⟩

    · exact ⟨Witness.rising, case_53_33_6_checked⟩

    · exact ⟨Witness.rising, case_53_33_7_checked⟩

    · exact ⟨Witness.rising, case_53_33_8_checked⟩

    · exact ⟨Witness.rising, case_53_33_9_checked⟩

    · exact ⟨Witness.rising, case_53_33_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_33_11, case_53_33_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_33_12, case_53_33_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_33_13, case_53_33_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_33_14, case_53_33_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_33_15, case_53_33_15_checked⟩

    · exact ⟨Witness.linear .positive case_53_33_16, case_53_33_16_checked⟩

    · exact ⟨Witness.linear .conditional case_53_33_17, case_53_33_17_checked⟩

    · exact ⟨Witness.linear .conditional case_53_33_18, case_53_33_18_checked⟩

    · exact ⟨Witness.linear .conditional case_53_33_19, case_53_33_19_checked⟩

    · exact ⟨Witness.linear .conditional case_53_33_20, case_53_33_20_checked⟩

    · exact ⟨Witness.linear .conditional case_53_33_21, case_53_33_21_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_34_1_checked⟩

    · exact ⟨Witness.rising, case_53_34_2_checked⟩

    · exact ⟨Witness.rising, case_53_34_3_checked⟩

    · exact ⟨Witness.rising, case_53_34_4_checked⟩

    · exact ⟨Witness.rising, case_53_34_5_checked⟩

    · exact ⟨Witness.rising, case_53_34_6_checked⟩

    · exact ⟨Witness.rising, case_53_34_7_checked⟩

    · exact ⟨Witness.rising, case_53_34_8_checked⟩

    · exact ⟨Witness.rising, case_53_34_9_checked⟩

    · exact ⟨Witness.linear .positive case_53_34_10, case_53_34_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_34_11, case_53_34_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_34_12, case_53_34_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_34_13, case_53_34_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_34_14, case_53_34_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_34_15, case_53_34_15_checked⟩

    · exact ⟨Witness.linear .positive case_53_34_16, case_53_34_16_checked⟩

    · exact ⟨Witness.linear .conditional case_53_34_17, case_53_34_17_checked⟩

    · exact ⟨Witness.linear .conditional case_53_34_18, case_53_34_18_checked⟩

    · exact ⟨Witness.linear .conditional case_53_34_19, case_53_34_19_checked⟩

    · exact ⟨Witness.linear .conditional case_53_34_20, case_53_34_20_checked⟩

    · exact ⟨Witness.linear .conditional case_53_34_21, case_53_34_21_checked⟩

    · exact ⟨Witness.linear .conditional case_53_34_22, case_53_34_22_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_35_1_checked⟩

    · exact ⟨Witness.rising, case_53_35_2_checked⟩

    · exact ⟨Witness.rising, case_53_35_3_checked⟩

    · exact ⟨Witness.rising, case_53_35_4_checked⟩

    · exact ⟨Witness.rising, case_53_35_5_checked⟩

    · exact ⟨Witness.rising, case_53_35_6_checked⟩

    · exact ⟨Witness.rising, case_53_35_7_checked⟩

    · exact ⟨Witness.rising, case_53_35_8_checked⟩

    · exact ⟨Witness.rising, case_53_35_9_checked⟩

    · exact ⟨Witness.linear .positive case_53_35_10, case_53_35_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_35_11, case_53_35_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_35_12, case_53_35_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_35_13, case_53_35_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_35_14, case_53_35_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_35_15, case_53_35_15_checked⟩

    · exact ⟨Witness.linear .conditional case_53_35_16, case_53_35_16_checked⟩

    · exact ⟨Witness.linear .conditional case_53_35_17, case_53_35_17_checked⟩

    · exact ⟨Witness.linear .conditional case_53_35_18, case_53_35_18_checked⟩

    · exact ⟨Witness.linear .conditional case_53_35_19, case_53_35_19_checked⟩

    · exact ⟨Witness.linear .conditional case_53_35_20, case_53_35_20_checked⟩

    · exact ⟨Witness.linear .conditional case_53_35_21, case_53_35_21_checked⟩

    · exact ⟨Witness.linear .conditional case_53_35_22, case_53_35_22_checked⟩

  · have hkHi : k ≤ 23 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_36_1_checked⟩

    · exact ⟨Witness.rising, case_53_36_2_checked⟩

    · exact ⟨Witness.rising, case_53_36_3_checked⟩

    · exact ⟨Witness.rising, case_53_36_4_checked⟩

    · exact ⟨Witness.rising, case_53_36_5_checked⟩

    · exact ⟨Witness.rising, case_53_36_6_checked⟩

    · exact ⟨Witness.rising, case_53_36_7_checked⟩

    · exact ⟨Witness.rising, case_53_36_8_checked⟩

    · exact ⟨Witness.rising, case_53_36_9_checked⟩

    · exact ⟨Witness.linear .positive case_53_36_10, case_53_36_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_36_11, case_53_36_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_36_12, case_53_36_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_36_13, case_53_36_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_36_14, case_53_36_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_36_15, case_53_36_15_checked⟩

    · exact ⟨Witness.linear .positive case_53_36_16, case_53_36_16_checked⟩

    · exact ⟨Witness.linear .conditional case_53_36_17, case_53_36_17_checked⟩

    · exact ⟨Witness.linear .conditional case_53_36_18, case_53_36_18_checked⟩

    · exact ⟨Witness.linear .conditional case_53_36_19, case_53_36_19_checked⟩

    · exact ⟨Witness.linear .conditional case_53_36_20, case_53_36_20_checked⟩

    · exact ⟨Witness.linear .conditional case_53_36_21, case_53_36_21_checked⟩

    · exact ⟨Witness.linear .conditional case_53_36_22, case_53_36_22_checked⟩

    · exact ⟨Witness.linear .conditional case_53_36_23, case_53_36_23_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_37_1_checked⟩

    · exact ⟨Witness.rising, case_53_37_2_checked⟩

    · exact ⟨Witness.rising, case_53_37_3_checked⟩

    · exact ⟨Witness.rising, case_53_37_4_checked⟩

    · exact ⟨Witness.rising, case_53_37_5_checked⟩

    · exact ⟨Witness.rising, case_53_37_6_checked⟩

    · exact ⟨Witness.rising, case_53_37_7_checked⟩

    · exact ⟨Witness.rising, case_53_37_8_checked⟩

    · exact ⟨Witness.rising, case_53_37_9_checked⟩

    · exact ⟨Witness.linear .positive case_53_37_10, case_53_37_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_37_11, case_53_37_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_37_12, case_53_37_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_37_13, case_53_37_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_37_14, case_53_37_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_37_15, case_53_37_15_checked⟩

    · exact ⟨Witness.linear .positive case_53_37_16, case_53_37_16_checked⟩

    · exact ⟨Witness.linear .positive case_53_37_17, case_53_37_17_checked⟩

    · exact ⟨Witness.linear .conditional case_53_37_18, case_53_37_18_checked⟩

    · exact ⟨Witness.linear .conditional case_53_37_19, case_53_37_19_checked⟩

    · exact ⟨Witness.linear .conditional case_53_37_20, case_53_37_20_checked⟩

    · exact ⟨Witness.linear .conditional case_53_37_21, case_53_37_21_checked⟩

    · exact ⟨Witness.linear .conditional case_53_37_22, case_53_37_22_checked⟩

    · exact ⟨Witness.linear .conditional case_53_37_23, case_53_37_23_checked⟩

    · exact ⟨Witness.linear .negative case_53_37_24, case_53_37_24_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_38_1_checked⟩

    · exact ⟨Witness.rising, case_53_38_2_checked⟩

    · exact ⟨Witness.rising, case_53_38_3_checked⟩

    · exact ⟨Witness.rising, case_53_38_4_checked⟩

    · exact ⟨Witness.rising, case_53_38_5_checked⟩

    · exact ⟨Witness.rising, case_53_38_6_checked⟩

    · exact ⟨Witness.rising, case_53_38_7_checked⟩

    · exact ⟨Witness.rising, case_53_38_8_checked⟩

    · exact ⟨Witness.rising, case_53_38_9_checked⟩

    · exact ⟨Witness.linear .positive case_53_38_10, case_53_38_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_38_11, case_53_38_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_38_12, case_53_38_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_38_13, case_53_38_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_38_14, case_53_38_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_38_15, case_53_38_15_checked⟩

    · exact ⟨Witness.linear .positive case_53_38_16, case_53_38_16_checked⟩

    · exact ⟨Witness.linear .positive case_53_38_17, case_53_38_17_checked⟩

    · exact ⟨Witness.linear .conditional case_53_38_18, case_53_38_18_checked⟩

    · exact ⟨Witness.linear .conditional case_53_38_19, case_53_38_19_checked⟩

    · exact ⟨Witness.linear .conditional case_53_38_20, case_53_38_20_checked⟩

    · exact ⟨Witness.linear .conditional case_53_38_21, case_53_38_21_checked⟩

    · exact ⟨Witness.linear .conditional case_53_38_22, case_53_38_22_checked⟩

    · exact ⟨Witness.linear .conditional case_53_38_23, case_53_38_23_checked⟩

    · exact ⟨Witness.linear .negative case_53_38_24, case_53_38_24_checked⟩

  · have hkHi : k ≤ 25 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_39_1_checked⟩

    · exact ⟨Witness.rising, case_53_39_2_checked⟩

    · exact ⟨Witness.rising, case_53_39_3_checked⟩

    · exact ⟨Witness.rising, case_53_39_4_checked⟩

    · exact ⟨Witness.rising, case_53_39_5_checked⟩

    · exact ⟨Witness.rising, case_53_39_6_checked⟩

    · exact ⟨Witness.rising, case_53_39_7_checked⟩

    · exact ⟨Witness.rising, case_53_39_8_checked⟩

    · exact ⟨Witness.rising, case_53_39_9_checked⟩

    · exact ⟨Witness.linear .positive case_53_39_10, case_53_39_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_39_11, case_53_39_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_39_12, case_53_39_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_39_13, case_53_39_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_39_14, case_53_39_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_39_15, case_53_39_15_checked⟩

    · exact ⟨Witness.linear .positive case_53_39_16, case_53_39_16_checked⟩

    · exact ⟨Witness.linear .positive case_53_39_17, case_53_39_17_checked⟩

    · exact ⟨Witness.linear .positive case_53_39_18, case_53_39_18_checked⟩

    · exact ⟨Witness.linear .conditional case_53_39_19, case_53_39_19_checked⟩

    · exact ⟨Witness.linear .conditional case_53_39_20, case_53_39_20_checked⟩

    · exact ⟨Witness.linear .conditional case_53_39_21, case_53_39_21_checked⟩

    · exact ⟨Witness.linear .conditional case_53_39_22, case_53_39_22_checked⟩

    · exact ⟨Witness.linear .conditional case_53_39_23, case_53_39_23_checked⟩

    · exact ⟨Witness.linear .negative case_53_39_24, case_53_39_24_checked⟩

    · exact ⟨Witness.linear .negative case_53_39_25, case_53_39_25_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_40_1_checked⟩

    · exact ⟨Witness.rising, case_53_40_2_checked⟩

    · exact ⟨Witness.rising, case_53_40_3_checked⟩

    · exact ⟨Witness.rising, case_53_40_4_checked⟩

    · exact ⟨Witness.rising, case_53_40_5_checked⟩

    · exact ⟨Witness.rising, case_53_40_6_checked⟩

    · exact ⟨Witness.rising, case_53_40_7_checked⟩

    · exact ⟨Witness.rising, case_53_40_8_checked⟩

    · exact ⟨Witness.rising, case_53_40_9_checked⟩

    · exact ⟨Witness.linear .positive case_53_40_10, case_53_40_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_40_11, case_53_40_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_40_12, case_53_40_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_40_13, case_53_40_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_40_14, case_53_40_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_40_15, case_53_40_15_checked⟩

    · exact ⟨Witness.linear .positive case_53_40_16, case_53_40_16_checked⟩

    · exact ⟨Witness.linear .positive case_53_40_17, case_53_40_17_checked⟩

    · exact ⟨Witness.linear .positive case_53_40_18, case_53_40_18_checked⟩

    · exact ⟨Witness.linear .positive case_53_40_19, case_53_40_19_checked⟩

    · exact ⟨Witness.linear .conditional case_53_40_20, case_53_40_20_checked⟩

    · exact ⟨Witness.linear .conditional case_53_40_21, case_53_40_21_checked⟩

    · exact ⟨Witness.linear .conditional case_53_40_22, case_53_40_22_checked⟩

    · exact ⟨Witness.linear .conditional case_53_40_23, case_53_40_23_checked⟩

    · exact ⟨Witness.linear .negative case_53_40_24, case_53_40_24_checked⟩

    · exact ⟨Witness.linear .negative case_53_40_25, case_53_40_25_checked⟩

    · exact ⟨Witness.linear .negative case_53_40_26, case_53_40_26_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_41_1_checked⟩

    · exact ⟨Witness.rising, case_53_41_2_checked⟩

    · exact ⟨Witness.rising, case_53_41_3_checked⟩

    · exact ⟨Witness.rising, case_53_41_4_checked⟩

    · exact ⟨Witness.rising, case_53_41_5_checked⟩

    · exact ⟨Witness.rising, case_53_41_6_checked⟩

    · exact ⟨Witness.rising, case_53_41_7_checked⟩

    · exact ⟨Witness.rising, case_53_41_8_checked⟩

    · exact ⟨Witness.rising, case_53_41_9_checked⟩

    · exact ⟨Witness.linear .positive case_53_41_10, case_53_41_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_41_11, case_53_41_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_41_12, case_53_41_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_41_13, case_53_41_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_41_14, case_53_41_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_41_15, case_53_41_15_checked⟩

    · exact ⟨Witness.linear .positive case_53_41_16, case_53_41_16_checked⟩

    · exact ⟨Witness.linear .positive case_53_41_17, case_53_41_17_checked⟩

    · exact ⟨Witness.linear .positive case_53_41_18, case_53_41_18_checked⟩

    · exact ⟨Witness.linear .positive case_53_41_19, case_53_41_19_checked⟩

    · exact ⟨Witness.linear .conditional case_53_41_20, case_53_41_20_checked⟩

    · exact ⟨Witness.linear .conditional case_53_41_21, case_53_41_21_checked⟩

    · exact ⟨Witness.linear .conditional case_53_41_22, case_53_41_22_checked⟩

    · exact ⟨Witness.linear .conditional case_53_41_23, case_53_41_23_checked⟩

    · exact ⟨Witness.linear .negative case_53_41_24, case_53_41_24_checked⟩

    · exact ⟨Witness.linear .negative case_53_41_25, case_53_41_25_checked⟩

    · exact ⟨Witness.linear .negative case_53_41_26, case_53_41_26_checked⟩

  · have hkHi : k ≤ 27 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_42_1_checked⟩

    · exact ⟨Witness.rising, case_53_42_2_checked⟩

    · exact ⟨Witness.rising, case_53_42_3_checked⟩

    · exact ⟨Witness.rising, case_53_42_4_checked⟩

    · exact ⟨Witness.rising, case_53_42_5_checked⟩

    · exact ⟨Witness.rising, case_53_42_6_checked⟩

    · exact ⟨Witness.rising, case_53_42_7_checked⟩

    · exact ⟨Witness.rising, case_53_42_8_checked⟩

    · exact ⟨Witness.rising, case_53_42_9_checked⟩

    · exact ⟨Witness.linear .positive case_53_42_10, case_53_42_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_42_11, case_53_42_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_42_12, case_53_42_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_42_13, case_53_42_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_42_14, case_53_42_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_42_15, case_53_42_15_checked⟩

    · exact ⟨Witness.linear .positive case_53_42_16, case_53_42_16_checked⟩

    · exact ⟨Witness.linear .positive case_53_42_17, case_53_42_17_checked⟩

    · exact ⟨Witness.linear .positive case_53_42_18, case_53_42_18_checked⟩

    · exact ⟨Witness.linear .positive case_53_42_19, case_53_42_19_checked⟩

    · exact ⟨Witness.linear .positive case_53_42_20, case_53_42_20_checked⟩

    · exact ⟨Witness.linear .conditional case_53_42_21, case_53_42_21_checked⟩

    · exact ⟨Witness.linear .conditional case_53_42_22, case_53_42_22_checked⟩

    · exact ⟨Witness.linear .conditional case_53_42_23, case_53_42_23_checked⟩

    · exact ⟨Witness.linear .negative case_53_42_24, case_53_42_24_checked⟩

    · exact ⟨Witness.linear .negative case_53_42_25, case_53_42_25_checked⟩

    · exact ⟨Witness.linear .negative case_53_42_26, case_53_42_26_checked⟩

    · exact ⟨Witness.linear .negative case_53_42_27, case_53_42_27_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_43_1_checked⟩

    · exact ⟨Witness.rising, case_53_43_2_checked⟩

    · exact ⟨Witness.rising, case_53_43_3_checked⟩

    · exact ⟨Witness.rising, case_53_43_4_checked⟩

    · exact ⟨Witness.rising, case_53_43_5_checked⟩

    · exact ⟨Witness.rising, case_53_43_6_checked⟩

    · exact ⟨Witness.rising, case_53_43_7_checked⟩

    · exact ⟨Witness.rising, case_53_43_8_checked⟩

    · exact ⟨Witness.rising, case_53_43_9_checked⟩

    · exact ⟨Witness.linear .positive case_53_43_10, case_53_43_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_43_11, case_53_43_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_43_12, case_53_43_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_43_13, case_53_43_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_43_14, case_53_43_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_43_15, case_53_43_15_checked⟩

    · exact ⟨Witness.linear .positive case_53_43_16, case_53_43_16_checked⟩

    · exact ⟨Witness.linear .positive case_53_43_17, case_53_43_17_checked⟩

    · exact ⟨Witness.linear .positive case_53_43_18, case_53_43_18_checked⟩

    · exact ⟨Witness.linear .positive case_53_43_19, case_53_43_19_checked⟩

    · exact ⟨Witness.linear .positive case_53_43_20, case_53_43_20_checked⟩

    · exact ⟨Witness.linear .positive case_53_43_21, case_53_43_21_checked⟩

    · exact ⟨Witness.linear .conditional case_53_43_22, case_53_43_22_checked⟩

    · exact ⟨Witness.linear .conditional case_53_43_23, case_53_43_23_checked⟩

    · exact ⟨Witness.linear .negative case_53_43_24, case_53_43_24_checked⟩

    · exact ⟨Witness.linear .negative case_53_43_25, case_53_43_25_checked⟩

    · exact ⟨Witness.linear .negative case_53_43_26, case_53_43_26_checked⟩

    · exact ⟨Witness.linear .negative case_53_43_27, case_53_43_27_checked⟩

    · exact ⟨Witness.linear .negative case_53_43_28, case_53_43_28_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_44_1_checked⟩

    · exact ⟨Witness.rising, case_53_44_2_checked⟩

    · exact ⟨Witness.rising, case_53_44_3_checked⟩

    · exact ⟨Witness.rising, case_53_44_4_checked⟩

    · exact ⟨Witness.rising, case_53_44_5_checked⟩

    · exact ⟨Witness.rising, case_53_44_6_checked⟩

    · exact ⟨Witness.rising, case_53_44_7_checked⟩

    · exact ⟨Witness.rising, case_53_44_8_checked⟩

    · exact ⟨Witness.rising, case_53_44_9_checked⟩

    · exact ⟨Witness.linear .positive case_53_44_10, case_53_44_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_44_11, case_53_44_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_44_12, case_53_44_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_44_13, case_53_44_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_44_14, case_53_44_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_44_15, case_53_44_15_checked⟩

    · exact ⟨Witness.linear .positive case_53_44_16, case_53_44_16_checked⟩

    · exact ⟨Witness.linear .positive case_53_44_17, case_53_44_17_checked⟩

    · exact ⟨Witness.linear .positive case_53_44_18, case_53_44_18_checked⟩

    · exact ⟨Witness.linear .positive case_53_44_19, case_53_44_19_checked⟩

    · exact ⟨Witness.linear .positive case_53_44_20, case_53_44_20_checked⟩

    · exact ⟨Witness.linear .positive case_53_44_21, case_53_44_21_checked⟩

    · exact ⟨Witness.linear .conditional case_53_44_22, case_53_44_22_checked⟩

    · exact ⟨Witness.linear .conditional case_53_44_23, case_53_44_23_checked⟩

    · exact ⟨Witness.linear .negative case_53_44_24, case_53_44_24_checked⟩

    · exact ⟨Witness.linear .negative case_53_44_25, case_53_44_25_checked⟩

    · exact ⟨Witness.linear .negative case_53_44_26, case_53_44_26_checked⟩

    · exact ⟨Witness.linear .negative case_53_44_27, case_53_44_27_checked⟩

    · exact ⟨Witness.linear .negative case_53_44_28, case_53_44_28_checked⟩

  · have hkHi : k ≤ 29 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_45_1_checked⟩

    · exact ⟨Witness.rising, case_53_45_2_checked⟩

    · exact ⟨Witness.rising, case_53_45_3_checked⟩

    · exact ⟨Witness.rising, case_53_45_4_checked⟩

    · exact ⟨Witness.rising, case_53_45_5_checked⟩

    · exact ⟨Witness.rising, case_53_45_6_checked⟩

    · exact ⟨Witness.rising, case_53_45_7_checked⟩

    · exact ⟨Witness.rising, case_53_45_8_checked⟩

    · exact ⟨Witness.rising, case_53_45_9_checked⟩

    · exact ⟨Witness.linear .positive case_53_45_10, case_53_45_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_45_11, case_53_45_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_45_12, case_53_45_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_45_13, case_53_45_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_45_14, case_53_45_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_45_15, case_53_45_15_checked⟩

    · exact ⟨Witness.linear .positive case_53_45_16, case_53_45_16_checked⟩

    · exact ⟨Witness.linear .positive case_53_45_17, case_53_45_17_checked⟩

    · exact ⟨Witness.linear .positive case_53_45_18, case_53_45_18_checked⟩

    · exact ⟨Witness.linear .positive case_53_45_19, case_53_45_19_checked⟩

    · exact ⟨Witness.linear .positive case_53_45_20, case_53_45_20_checked⟩

    · exact ⟨Witness.linear .positive case_53_45_21, case_53_45_21_checked⟩

    · exact ⟨Witness.linear .positive case_53_45_22, case_53_45_22_checked⟩

    · exact ⟨Witness.linear .conditional case_53_45_23, case_53_45_23_checked⟩

    · exact ⟨Witness.linear .negative case_53_45_24, case_53_45_24_checked⟩

    · exact ⟨Witness.linear .negative case_53_45_25, case_53_45_25_checked⟩

    · exact ⟨Witness.linear .negative case_53_45_26, case_53_45_26_checked⟩

    · exact ⟨Witness.linear .negative case_53_45_27, case_53_45_27_checked⟩

    · exact ⟨Witness.linear .negative case_53_45_28, case_53_45_28_checked⟩

    · exact ⟨Witness.linear .negative case_53_45_29, case_53_45_29_checked⟩

  · have hkHi : k ≤ 30 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_46_1_checked⟩

    · exact ⟨Witness.rising, case_53_46_2_checked⟩

    · exact ⟨Witness.rising, case_53_46_3_checked⟩

    · exact ⟨Witness.rising, case_53_46_4_checked⟩

    · exact ⟨Witness.rising, case_53_46_5_checked⟩

    · exact ⟨Witness.rising, case_53_46_6_checked⟩

    · exact ⟨Witness.rising, case_53_46_7_checked⟩

    · exact ⟨Witness.rising, case_53_46_8_checked⟩

    · exact ⟨Witness.rising, case_53_46_9_checked⟩

    · exact ⟨Witness.linear .positive case_53_46_10, case_53_46_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_46_11, case_53_46_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_46_12, case_53_46_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_46_13, case_53_46_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_46_14, case_53_46_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_46_15, case_53_46_15_checked⟩

    · exact ⟨Witness.linear .positive case_53_46_16, case_53_46_16_checked⟩

    · exact ⟨Witness.linear .positive case_53_46_17, case_53_46_17_checked⟩

    · exact ⟨Witness.linear .positive case_53_46_18, case_53_46_18_checked⟩

    · exact ⟨Witness.linear .positive case_53_46_19, case_53_46_19_checked⟩

    · exact ⟨Witness.linear .positive case_53_46_20, case_53_46_20_checked⟩

    · exact ⟨Witness.linear .positive case_53_46_21, case_53_46_21_checked⟩

    · exact ⟨Witness.linear .positive case_53_46_22, case_53_46_22_checked⟩

    · exact ⟨Witness.linear .conditional case_53_46_23, case_53_46_23_checked⟩

    · exact ⟨Witness.linear .conditional case_53_46_24, case_53_46_24_checked⟩

    · exact ⟨Witness.linear .negative case_53_46_25, case_53_46_25_checked⟩

    · exact ⟨Witness.linear .negative case_53_46_26, case_53_46_26_checked⟩

    · exact ⟨Witness.linear .negative case_53_46_27, case_53_46_27_checked⟩

    · exact ⟨Witness.linear .negative case_53_46_28, case_53_46_28_checked⟩

    · exact ⟨Witness.linear .negative case_53_46_29, case_53_46_29_checked⟩

    · exact ⟨Witness.linear .negative case_53_46_30, case_53_46_30_checked⟩

  · have hkHi : k ≤ 30 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_47_1_checked⟩

    · exact ⟨Witness.rising, case_53_47_2_checked⟩

    · exact ⟨Witness.rising, case_53_47_3_checked⟩

    · exact ⟨Witness.rising, case_53_47_4_checked⟩

    · exact ⟨Witness.rising, case_53_47_5_checked⟩

    · exact ⟨Witness.rising, case_53_47_6_checked⟩

    · exact ⟨Witness.rising, case_53_47_7_checked⟩

    · exact ⟨Witness.rising, case_53_47_8_checked⟩

    · exact ⟨Witness.rising, case_53_47_9_checked⟩

    · exact ⟨Witness.linear .positive case_53_47_10, case_53_47_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_47_11, case_53_47_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_47_12, case_53_47_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_47_13, case_53_47_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_47_14, case_53_47_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_47_15, case_53_47_15_checked⟩

    · exact ⟨Witness.linear .positive case_53_47_16, case_53_47_16_checked⟩

    · exact ⟨Witness.linear .positive case_53_47_17, case_53_47_17_checked⟩

    · exact ⟨Witness.linear .positive case_53_47_18, case_53_47_18_checked⟩

    · exact ⟨Witness.linear .positive case_53_47_19, case_53_47_19_checked⟩

    · exact ⟨Witness.linear .positive case_53_47_20, case_53_47_20_checked⟩

    · exact ⟨Witness.linear .positive case_53_47_21, case_53_47_21_checked⟩

    · exact ⟨Witness.linear .positive case_53_47_22, case_53_47_22_checked⟩

    · exact ⟨Witness.linear .positive case_53_47_23, case_53_47_23_checked⟩

    · exact ⟨Witness.linear .conditional case_53_47_24, case_53_47_24_checked⟩

    · exact ⟨Witness.linear .negative case_53_47_25, case_53_47_25_checked⟩

    · exact ⟨Witness.linear .negative case_53_47_26, case_53_47_26_checked⟩

    · exact ⟨Witness.linear .negative case_53_47_27, case_53_47_27_checked⟩

    · exact ⟨Witness.linear .negative case_53_47_28, case_53_47_28_checked⟩

    · exact ⟨Witness.linear .negative case_53_47_29, case_53_47_29_checked⟩

    · exact ⟨Witness.linear .negative case_53_47_30, case_53_47_30_checked⟩

  · have hkHi : k ≤ 31 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_48_1_checked⟩

    · exact ⟨Witness.rising, case_53_48_2_checked⟩

    · exact ⟨Witness.rising, case_53_48_3_checked⟩

    · exact ⟨Witness.rising, case_53_48_4_checked⟩

    · exact ⟨Witness.rising, case_53_48_5_checked⟩

    · exact ⟨Witness.rising, case_53_48_6_checked⟩

    · exact ⟨Witness.rising, case_53_48_7_checked⟩

    · exact ⟨Witness.rising, case_53_48_8_checked⟩

    · exact ⟨Witness.rising, case_53_48_9_checked⟩

    · exact ⟨Witness.linear .positive case_53_48_10, case_53_48_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_48_11, case_53_48_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_48_12, case_53_48_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_48_13, case_53_48_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_48_14, case_53_48_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_48_15, case_53_48_15_checked⟩

    · exact ⟨Witness.linear .positive case_53_48_16, case_53_48_16_checked⟩

    · exact ⟨Witness.linear .positive case_53_48_17, case_53_48_17_checked⟩

    · exact ⟨Witness.linear .positive case_53_48_18, case_53_48_18_checked⟩

    · exact ⟨Witness.linear .positive case_53_48_19, case_53_48_19_checked⟩

    · exact ⟨Witness.linear .positive case_53_48_20, case_53_48_20_checked⟩

    · exact ⟨Witness.linear .positive case_53_48_21, case_53_48_21_checked⟩

    · exact ⟨Witness.linear .positive case_53_48_22, case_53_48_22_checked⟩

    · exact ⟨Witness.linear .positive case_53_48_23, case_53_48_23_checked⟩

    · exact ⟨Witness.linear .positive case_53_48_24, case_53_48_24_checked⟩

    · exact ⟨Witness.linear .negative case_53_48_25, case_53_48_25_checked⟩

    · exact ⟨Witness.linear .negative case_53_48_26, case_53_48_26_checked⟩

    · exact ⟨Witness.linear .negative case_53_48_27, case_53_48_27_checked⟩

    · exact ⟨Witness.linear .negative case_53_48_28, case_53_48_28_checked⟩

    · exact ⟨Witness.linear .negative case_53_48_29, case_53_48_29_checked⟩

    · exact ⟨Witness.linear .negative case_53_48_30, case_53_48_30_checked⟩

    · exact ⟨Witness.linear .negative case_53_48_31, case_53_48_31_checked⟩

  · have hkHi : k ≤ 32 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_49_1_checked⟩

    · exact ⟨Witness.rising, case_53_49_2_checked⟩

    · exact ⟨Witness.rising, case_53_49_3_checked⟩

    · exact ⟨Witness.rising, case_53_49_4_checked⟩

    · exact ⟨Witness.rising, case_53_49_5_checked⟩

    · exact ⟨Witness.rising, case_53_49_6_checked⟩

    · exact ⟨Witness.rising, case_53_49_7_checked⟩

    · exact ⟨Witness.rising, case_53_49_8_checked⟩

    · exact ⟨Witness.rising, case_53_49_9_checked⟩

    · exact ⟨Witness.linear .positive case_53_49_10, case_53_49_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_49_11, case_53_49_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_49_12, case_53_49_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_49_13, case_53_49_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_49_14, case_53_49_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_49_15, case_53_49_15_checked⟩

    · exact ⟨Witness.linear .positive case_53_49_16, case_53_49_16_checked⟩

    · exact ⟨Witness.linear .positive case_53_49_17, case_53_49_17_checked⟩

    · exact ⟨Witness.linear .positive case_53_49_18, case_53_49_18_checked⟩

    · exact ⟨Witness.linear .positive case_53_49_19, case_53_49_19_checked⟩

    · exact ⟨Witness.linear .positive case_53_49_20, case_53_49_20_checked⟩

    · exact ⟨Witness.linear .positive case_53_49_21, case_53_49_21_checked⟩

    · exact ⟨Witness.linear .positive case_53_49_22, case_53_49_22_checked⟩

    · exact ⟨Witness.linear .positive case_53_49_23, case_53_49_23_checked⟩

    · exact ⟨Witness.linear .positive case_53_49_24, case_53_49_24_checked⟩

    · exact ⟨Witness.linear .negative case_53_49_25, case_53_49_25_checked⟩

    · exact ⟨Witness.linear .negative case_53_49_26, case_53_49_26_checked⟩

    · exact ⟨Witness.linear .negative case_53_49_27, case_53_49_27_checked⟩

    · exact ⟨Witness.linear .negative case_53_49_28, case_53_49_28_checked⟩

    · exact ⟨Witness.linear .negative case_53_49_29, case_53_49_29_checked⟩

    · exact ⟨Witness.linear .negative case_53_49_30, case_53_49_30_checked⟩

    · exact ⟨Witness.linear .negative case_53_49_31, case_53_49_31_checked⟩

    · exact ⟨Witness.linear .negative case_53_49_32, case_53_49_32_checked⟩

  · have hkHi : k ≤ 32 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_50_1_checked⟩

    · exact ⟨Witness.rising, case_53_50_2_checked⟩

    · exact ⟨Witness.rising, case_53_50_3_checked⟩

    · exact ⟨Witness.rising, case_53_50_4_checked⟩

    · exact ⟨Witness.rising, case_53_50_5_checked⟩

    · exact ⟨Witness.rising, case_53_50_6_checked⟩

    · exact ⟨Witness.rising, case_53_50_7_checked⟩

    · exact ⟨Witness.rising, case_53_50_8_checked⟩

    · exact ⟨Witness.rising, case_53_50_9_checked⟩

    · exact ⟨Witness.linear .positive case_53_50_10, case_53_50_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_50_11, case_53_50_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_50_12, case_53_50_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_50_13, case_53_50_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_50_14, case_53_50_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_50_15, case_53_50_15_checked⟩

    · exact ⟨Witness.linear .positive case_53_50_16, case_53_50_16_checked⟩

    · exact ⟨Witness.linear .positive case_53_50_17, case_53_50_17_checked⟩

    · exact ⟨Witness.linear .positive case_53_50_18, case_53_50_18_checked⟩

    · exact ⟨Witness.linear .positive case_53_50_19, case_53_50_19_checked⟩

    · exact ⟨Witness.linear .positive case_53_50_20, case_53_50_20_checked⟩

    · exact ⟨Witness.linear .positive case_53_50_21, case_53_50_21_checked⟩

    · exact ⟨Witness.linear .positive case_53_50_22, case_53_50_22_checked⟩

    · exact ⟨Witness.linear .positive case_53_50_23, case_53_50_23_checked⟩

    · exact ⟨Witness.linear .positive case_53_50_24, case_53_50_24_checked⟩

    · exact ⟨Witness.linear .positive case_53_50_25, case_53_50_25_checked⟩

    · exact ⟨Witness.linear .negative case_53_50_26, case_53_50_26_checked⟩

    · exact ⟨Witness.linear .negative case_53_50_27, case_53_50_27_checked⟩

    · exact ⟨Witness.linear .negative case_53_50_28, case_53_50_28_checked⟩

    · exact ⟨Witness.linear .negative case_53_50_29, case_53_50_29_checked⟩

    · exact ⟨Witness.linear .negative case_53_50_30, case_53_50_30_checked⟩

    · exact ⟨Witness.linear .negative case_53_50_31, case_53_50_31_checked⟩

    · exact ⟨Witness.linear .negative case_53_50_32, case_53_50_32_checked⟩

  · have hkHi : k ≤ 33 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_51_1_checked⟩

    · exact ⟨Witness.rising, case_53_51_2_checked⟩

    · exact ⟨Witness.rising, case_53_51_3_checked⟩

    · exact ⟨Witness.rising, case_53_51_4_checked⟩

    · exact ⟨Witness.rising, case_53_51_5_checked⟩

    · exact ⟨Witness.rising, case_53_51_6_checked⟩

    · exact ⟨Witness.rising, case_53_51_7_checked⟩

    · exact ⟨Witness.rising, case_53_51_8_checked⟩

    · exact ⟨Witness.rising, case_53_51_9_checked⟩

    · exact ⟨Witness.linear .positive case_53_51_10, case_53_51_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_51_11, case_53_51_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_51_12, case_53_51_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_51_13, case_53_51_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_51_14, case_53_51_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_51_15, case_53_51_15_checked⟩

    · exact ⟨Witness.linear .positive case_53_51_16, case_53_51_16_checked⟩

    · exact ⟨Witness.linear .positive case_53_51_17, case_53_51_17_checked⟩

    · exact ⟨Witness.linear .positive case_53_51_18, case_53_51_18_checked⟩

    · exact ⟨Witness.linear .positive case_53_51_19, case_53_51_19_checked⟩

    · exact ⟨Witness.linear .positive case_53_51_20, case_53_51_20_checked⟩

    · exact ⟨Witness.linear .positive case_53_51_21, case_53_51_21_checked⟩

    · exact ⟨Witness.linear .positive case_53_51_22, case_53_51_22_checked⟩

    · exact ⟨Witness.linear .positive case_53_51_23, case_53_51_23_checked⟩

    · exact ⟨Witness.linear .positive case_53_51_24, case_53_51_24_checked⟩

    · exact ⟨Witness.linear .positive case_53_51_25, case_53_51_25_checked⟩

    · exact ⟨Witness.linear .negative case_53_51_26, case_53_51_26_checked⟩

    · exact ⟨Witness.linear .negative case_53_51_27, case_53_51_27_checked⟩

    · exact ⟨Witness.linear .negative case_53_51_28, case_53_51_28_checked⟩

    · exact ⟨Witness.linear .negative case_53_51_29, case_53_51_29_checked⟩

    · exact ⟨Witness.linear .negative case_53_51_30, case_53_51_30_checked⟩

    · exact ⟨Witness.linear .negative case_53_51_31, case_53_51_31_checked⟩

    · exact ⟨Witness.linear .negative case_53_51_32, case_53_51_32_checked⟩

    · exact ⟨Witness.linear .negative case_53_51_33, case_53_51_33_checked⟩

  · have hkHi : k ≤ 34 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_53_52_1_checked⟩

    · exact ⟨Witness.rising, case_53_52_2_checked⟩

    · exact ⟨Witness.rising, case_53_52_3_checked⟩

    · exact ⟨Witness.rising, case_53_52_4_checked⟩

    · exact ⟨Witness.rising, case_53_52_5_checked⟩

    · exact ⟨Witness.rising, case_53_52_6_checked⟩

    · exact ⟨Witness.rising, case_53_52_7_checked⟩

    · exact ⟨Witness.rising, case_53_52_8_checked⟩

    · exact ⟨Witness.rising, case_53_52_9_checked⟩

    · exact ⟨Witness.linear .positive case_53_52_10, case_53_52_10_checked⟩

    · exact ⟨Witness.linear .positive case_53_52_11, case_53_52_11_checked⟩

    · exact ⟨Witness.linear .positive case_53_52_12, case_53_52_12_checked⟩

    · exact ⟨Witness.linear .positive case_53_52_13, case_53_52_13_checked⟩

    · exact ⟨Witness.linear .positive case_53_52_14, case_53_52_14_checked⟩

    · exact ⟨Witness.linear .positive case_53_52_15, case_53_52_15_checked⟩

    · exact ⟨Witness.linear .positive case_53_52_16, case_53_52_16_checked⟩

    · exact ⟨Witness.linear .positive case_53_52_17, case_53_52_17_checked⟩

    · exact ⟨Witness.linear .positive case_53_52_18, case_53_52_18_checked⟩

    · exact ⟨Witness.linear .positive case_53_52_19, case_53_52_19_checked⟩

    · exact ⟨Witness.linear .positive case_53_52_20, case_53_52_20_checked⟩

    · exact ⟨Witness.linear .positive case_53_52_21, case_53_52_21_checked⟩

    · exact ⟨Witness.linear .positive case_53_52_22, case_53_52_22_checked⟩

    · exact ⟨Witness.linear .positive case_53_52_23, case_53_52_23_checked⟩

    · exact ⟨Witness.linear .positive case_53_52_24, case_53_52_24_checked⟩

    · exact ⟨Witness.linear .positive case_53_52_25, case_53_52_25_checked⟩

    · exact ⟨Witness.linear .positive case_53_52_26, case_53_52_26_checked⟩

    · exact ⟨Witness.linear .negative case_53_52_27, case_53_52_27_checked⟩

    · exact ⟨Witness.linear .negative case_53_52_28, case_53_52_28_checked⟩

    · exact ⟨Witness.linear .negative case_53_52_29, case_53_52_29_checked⟩

    · exact ⟨Witness.linear .negative case_53_52_30, case_53_52_30_checked⟩

    · exact ⟨Witness.linear .negative case_53_52_31, case_53_52_31_checked⟩

    · exact ⟨Witness.linear .negative case_53_52_32, case_53_52_32_checked⟩

    · exact ⟨Witness.linear .negative case_53_52_33, case_53_52_33_checked⟩

    · exact ⟨Witness.linear .negative case_53_52_34, case_53_52_34_checked⟩


#print axioms coverage_53
end ForestUnimodality.FiniteRows.FiniteData
