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

theorem case_39_20_1_checked :
    (Witness.rising).check 39 20 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_20_2_checked :
    (Witness.rising).check 39 20 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_20_3_checked :
    (Witness.rising).check 39 20 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_20_4_checked :
    (Witness.rising).check 39 20 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_20_5_checked :
    (Witness.rising).check 39 20 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_20_6_checked :
    (Witness.rising).check 39 20 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_20_7_checked :
    (Witness.rising).check 39 20 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_20_8_checked :
    (Witness.rising).check 39 20 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_20_9 : Certificate := {
  objectiveScale := 3768433709040000
  eta := 36517660161550888320
  rows := #[⟨.count 2, 8837926692993478080⟩, ⟨.count 3, 1390913808271827840⟩, ⟨.count 4, 234562387785485760⟩, ⟨.count 5, 48352772920692240⟩, ⟨.count 6, 12345388830815040⟩, ⟨.count 7, 4669089365500560⟩, ⟨.count 8, 3745823106785760⟩, ⟨.path 9, 881000091107136⟩, ⟨.path 10, 703212569099040⟩, ⟨.privateRow 7 5, 218569155124320⟩, ⟨.privateRow 8 2, 17386182793980⟩, ⟨.privateRow 9 0, 114708838203960⟩, ⟨.privateRow 10 0, 63963711996912⟩, ⟨.privateRow 11 0, 63789305147568⟩, ⟨.hall 7 3, 14775949515096⟩, ⟨.hall 6 6, 4361839666470⟩, ⟨.hall 5 8, 403488861776⟩, ⟨.hall 5 9, 8872948460376⟩, ⟨.hall 8 11, 48361565932680⟩, ⟨.hall 4 12, 53276231561553⟩, ⟨.hall 3 16, 7746126325217280⟩]
  caps := #[0, 89540567186021952, 764823165410304, 1037719097390976, 0, 111392459823645, 13249839901584, 0, 93390228830052, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_39_20_9_checked :
    (Witness.linear .positive case_39_20_9).check 39 20 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_20_10 : Certificate := {
  objectiveScale := 8808800000
  eta := 113912603925120
  rows := #[⟨.count 2, 31593332010240⟩, ⟨.count 3, 5921585429760⟩, ⟨.count 4, 1116790234560⟩, ⟨.count 5, 249618489120⟩, ⟨.count 6, 63074531520⟩, ⟨.count 7, 21310248960⟩, ⟨.count 8, 9101252160⟩, ⟨.count 9, 8899450560⟩, ⟨.path 10, 257056800⟩, ⟨.path 11, 2579889312⟩, ⟨.privateRow 4 16, 30300510240⟩, ⟨.privateRow 8 4, 413132720⟩, ⟨.privateRow 9 2, 175567392⟩, ⟨.privateRow 10 0, 386358336⟩, ⟨.privateRow 11 0, 258306048⟩, ⟨.privateRow 12 1, 364188825⟩, ⟨.hall 8 3, 52132080⟩, ⟨.hall 7 5, 30884700⟩, ⟨.hall 6 7, 29034720⟩, ⟨.hall 6 8, 8717280⟩, ⟨.hall 5 10, 100324224⟩, ⟨.hall 9 10, 148599360⟩, ⟨.hall 4 13, 976521546⟩]
  caps := #[0, 206199209216, 0, 0, 1878036160, 0, 304656352, 0, 0, 55431376, 45083584, 57369312, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_39_20_10_checked :
    (Witness.linear .positive case_39_20_10).check 39 20 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_20_11 : Certificate := {
  objectiveScale := 3088800000
  eta := 50333476152960
  rows := #[⟨.count 2, 15600434129280⟩, ⟨.count 3, 3419629012800⟩, ⟨.count 4, 783484621920⟩, ⟨.count 5, 191181790800⟩, ⟨.count 6, 56272376160⟩, ⟨.count 7, 17814036240⟩, ⟨.count 8, 6548461920⟩, ⟨.count 9, 3087564480⟩, ⟨.count 10, 3087564480⟩, ⟨.path 12, 317425680⟩, ⟨.path 13, 525585060⟩, ⟨.privateRow 4 16, 31382671320⟩, ⟨.privateRow 8 6, 39639600⟩, ⟨.privateRow 9 4, 54234180⟩, ⟨.privateRow 11 0, 216936720⟩, ⟨.privateRow 12 0, 83243160⟩, ⟨.privateRow 13 0, 65405340⟩, ⟨.hall 9 3, 48019608⟩, ⟨.hall 8 5, 38238200⟩, ⟨.hall 9 5, 4226040⟩, ⟨.hall 7 7, 48315960⟩, ⟨.hall 6 9, 93528864⟩, ⟨.hall 10 9, 281513232⟩, ⟨.hall 9 10, 57788640⟩, ⟨.hall 5 12, 998389392⟩, ⟨.hall 4 14, 5491967481⟩]
  caps := #[0, 141371596080, 0, 3621926880, 835546140, 718680105, 63423360, 200463120, 0, 94259880, 1235520, 0, 110218680, 2342340, 0, 0, 0, 0, 0, 0] }

theorem case_39_20_11_checked :
    (Witness.linear .positive case_39_20_11).check 39 20 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_20_12 : Certificate := {
  objectiveScale := 190590400000
  eta := 1666302973695360
  rows := #[⟨.count 2, 437842372968000⟩, ⟨.count 3, 118327821131520⟩, ⟨.count 4, 33224509478160⟩, ⟨.count 5, 10596521295360⟩, ⟨.count 6, 3611016929520⟩, ⟨.count 7, 1333055964240⟩, ⟨.count 8, 537750813600⟩, ⟨.count 9, 291774843360⟩, ⟨.count 10, 222304642560⟩, ⟨.count 11, 215100325440⟩, ⟨.count 13, 189223594560⟩, ⟨.path 10, 9948818880⟩, ⟨.path 11, 25788514752⟩, ⟨.privateRow 3 17, 6181304088960⟩, ⟨.privateRow 9 5, 37491854400⟩, ⟨.privateRow 12 0, 11085214140⟩, ⟨.hall 10 2, 7165722564⟩, ⟨.hall 9 4, 5495463792⟩, ⟨.hall 10 4, 1054917864⟩, ⟨.hall 8 6, 5454288840⟩, ⟨.hall 7 7, 5440347990⟩, ⟨.hall 11 8, 5660534880⟩, ⟨.hall 6 9, 2718947088⟩, ⟨.hall 9 9, 1052578800⟩, ⟨.hall 7 10, 17387342280⟩, ⟨.hall 5 11, 36833909112⟩, ⟨.hall 6 11, 93673188180⟩, ⟨.hall 4 14, 1062871558749⟩, ⟨.hall 3 16, 13557314010240⟩, ⟨.assumptionRow 12, 188623470420⟩]
  caps := #[0, 1425704135856, 164212007960, 0, 50324233960, 17512279785, 0, 22462440, 1127441700, 4184768280, 2056161492, 0, 2317139440, 1366805440, 0, 0, 0, 0, 0, 0] }

theorem case_39_20_12_checked :
    (Witness.linear .conditional case_39_20_12).check 39 20 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_21_1_checked :
    (Witness.rising).check 39 21 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_21_2_checked :
    (Witness.rising).check 39 21 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_21_3_checked :
    (Witness.rising).check 39 21 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_21_4_checked :
    (Witness.rising).check 39 21 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_21_5_checked :
    (Witness.rising).check 39 21 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_21_6_checked :
    (Witness.rising).check 39 21 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_21_7_checked :
    (Witness.rising).check 39 21 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_21_8_checked :
    (Witness.rising).check 39 21 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_21_9 : Certificate := {
  objectiveScale := 19687151033550000
  eta := 254893481861578560000
  rows := #[⟨.count 2, 54427255244560598400⟩, ⟨.count 3, 7787370714226903800⟩, ⟨.count 4, 1304454877762196160⟩, ⟨.count 5, 267745254056280000⟩, ⟨.count 6, 66730355626334400⟩, ⟨.count 7, 24508988640536400⟩, ⟨.count 8, 19921744777334400⟩, ⟨.path 9, 5006992164894720⟩, ⟨.path 10, 3438890966691180⟩, ⟨.privateRow 5 11, 535490508112560⟩, ⟨.privateRow 5 12, 14565341820661632⟩, ⟨.privateRow 6 8, 2317026237025500⟩, ⟨.privateRow 6 9, 4766453973309600⟩, ⟨.privateRow 6 10, 6007105058955000⟩, ⟨.privateRow 6 11, 7290909225840240⟩, ⟨.privateRow 7 5, 1163662065706140⟩, ⟨.privateRow 7 6, 2185442030972200⟩, ⟨.privateRow 7 7, 2587345964678475⟩, ⟨.privateRow 7 8, 1294592437195200⟩, ⟨.privateRow 8 2, 567944478301200⟩, ⟨.privateRow 8 3, 1131917316894000⟩, ⟨.privateRow 8 4, 52425644150880⟩, ⟨.privateRow 9 0, 528289183366560⟩, ⟨.privateRow 10 0, 288341042829840⟩, ⟨.hall 10 9, 257362253104320⟩, ⟨.hall 4 13, 56698994976624⟩, ⟨.hall 4 14, 790110994813140⟩, ⟨.hall 5 15, 17068759946087850⟩, ⟨.hall 3 17, 121824090595607400⟩]
  caps := #[0, 0, 0, 1769858213923800, 0, 0, 936079400298900, 591126989726130, 0, 143844370306560, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_39_21_9_checked :
    (Witness.linear .positive case_39_21_9).check 39 21 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_21_10 : Certificate := {
  objectiveScale := 6171000000
  eta := 101788996108800
  rows := #[⟨.count 2, 22805666083200⟩, ⟨.count 3, 3879824949000⟩, ⟨.count 4, 779266968480⟩, ⟨.count 5, 176105529600⟩, ⟨.count 6, 44993995200⟩, ⟨.count 7, 15239901600⟩, ⟨.count 8, 6465412800⟩, ⟨.count 9, 6095960640⟩, ⟨.path 10, 245104860⟩, ⟨.path 11, 1729254450⟩, ⟨.privateRow 5 12, 2893162272⟩, ⟨.privateRow 6 9, 794824800⟩, ⟨.privateRow 6 10, 4576002200⟩, ⟨.privateRow 6 11, 5636344560⟩, ⟨.privateRow 7 7, 1572370800⟩, ⟨.privateRow 7 8, 2306719800⟩, ⟨.privateRow 7 9, 3174979500⟩, ⟨.privateRow 7 10, 3326169000⟩, ⟨.privateRow 8 4, 361755240⟩, ⟨.privateRow 8 5, 936458600⟩, ⟨.privateRow 8 6, 1342150425⟩, ⟨.privateRow 8 7, 538784400⟩, ⟨.privateRow 9 2, 503798400⟩, ⟨.privateRow 9 3, 286325424⟩, ⟨.privateRow 10 0, 243735800⟩, ⟨.privateRow 11 0, 157437000⟩, ⟨.privateRow 12 7, 745868200⟩, ⟨.privateRow 13 6, 362854800⟩, ⟨.hall 5 10, 21042175⟩, ⟨.hall 4 14, 1273312040⟩, ⟨.hall 6 14, 3386644800⟩, ⟨.hall 3 17, 124741416800⟩]
  caps := #[0, 0, 0, 6993841140, 2207446560, 584551968, 0, 104917890, 0, 94218612, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_39_21_10_checked :
    (Witness.linear .positive case_39_21_10).check 39 21 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_21_11 : Certificate := {
  objectiveScale := 707850000
  eta := 17292934058400
  rows := #[⟨.count 2, 4155498547200⟩, ⟨.count 3, 976650374700⟩, ⟨.count 4, 223646623200⟩, ⟨.count 5, 57457600200⟩, ⟨.count 6, 14745931200⟩, ⟨.count 7, 4578373800⟩, ⟨.count 8, 1614412800⟩, ⟨.count 9, 726485760⟩, ⟨.count 10, 706305600⟩, ⟨.path 12, 173738565⟩, ⟨.privateRow 10 2, 12108096⟩, ⟨.privateRow 11 3, 25225200⟩, ⟨.privateRow 12 0, 17837820⟩, ⟨.privateRow 12 5, 17837820⟩, ⟨.hall 12 2, 22022000⟩, ⟨.hall 10 3, 2407860⟩, ⟨.hall 11 3, 2147145⟩, ⟨.hall 9 4, 1662570⟩, ⟨.hall 8 5, 975100⟩, ⟨.hall 6 9, 10145520⟩]
  caps := #[0, 0, 5386880070, 0, 0, 0, 28648620, 3307590, 0, 0, 1544400, 20948070, 13198185, 0, 0, 0, 0, 0, 0] }

theorem case_39_21_11_checked :
    (Witness.linear .positive case_39_21_11).check 39 21 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_21_12 : Certificate := {
  objectiveScale := 20349000000
  eta := 345724886707200
  rows := #[⟨.count 2, 83465444462400⟩, ⟨.count 3, 22640531413500⟩, ⟨.count 4, 6312868642080⟩, ⟨.count 5, 1838479242600⟩, ⟨.count 6, 572669697600⟩, ⟨.count 7, 197582685300⟩, ⟨.count 8, 78514581600⟩, ⟨.count 9, 38664727920⟩, ⟨.count 10, 26665329600⟩, ⟨.count 11, 22406283900⟩, ⟨.count 13, 22697274600⟩, ⟨.path 10, 4948553610⟩, ⟨.privateRow 6 11, 81011810880⟩, ⟨.privateRow 7 9, 36567831300⟩, ⟨.privateRow 7 10, 94979364480⟩, ⟨.privateRow 8 7, 16454201400⟩, ⟨.privateRow 8 8, 44874293100⟩, ⟨.privateRow 8 9, 69589103220⟩, ⟨.privateRow 9 5, 7703317440⟩, ⟨.privateRow 9 6, 8147739600⟩, ⟨.privateRow 9 7, 63922720680⟩, ⟨.privateRow 9 8, 2281367088⟩, ⟨.privateRow 10 3, 3966879280⟩, ⟨.privateRow 10 4, 11740152060⟩, ⟨.privateRow 10 5, 9163561680⟩, ⟨.privateRow 11 1, 2536909830⟩, ⟨.privateRow 11 2, 3682942900⟩, ⟨.privateRow 12 0, 1280359080⟩, ⟨.hall 6 10, 6279120⟩, ⟨.hall 7 10, 586559925⟩, ⟨.hall 6 11, 3346073280⟩, ⟨.hall 7 11, 2141393100⟩, ⟨.hall 5 13, 25075084320⟩, ⟨.hall 4 14, 34289202948⟩, ⟨.hall 3 16, 259609350000⟩, ⟨.hall 2 18, 2698188292800⟩, ⟨.assumptionRow 12, 22053664800⟩]
  caps := #[0, 1393021609200, 151504954380, 26378635140, 2050791600, 6082928280, 2627474850, 0, 1296468420, 0, 591367590, 0, 1179195480, 0, 0, 0, 0, 0, 0] }

theorem case_39_21_12_checked :
    (Witness.linear .conditional case_39_21_12).check 39 21 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_21_13 : Certificate := {
  objectiveScale := 232188167568000000
  eta := 3365868427982144884800
  rows := #[⟨.count 2, 894526183991869228800⟩, ⟨.count 3, 243039060738236763000⟩, ⟨.count 4, 67944106650337837920⟩, ⟨.count 5, 19738180129028961600⟩, ⟨.count 6, 6010674995675750400⟩, ⟨.count 7, 1931164134352853400⟩, ⟨.count 8, 667378450040702400⟩, ⟨.count 9, 197225273295610560⟩, ⟨.count 10, 129491341052673600⟩, ⟨.count 11, 123265795809756600⟩, ⟨.count 12, 117395996009292000⟩, ⟨.count 14, 284880950315881920⟩, ⟨.path 9, 73960526099940480⟩, ⟨.privateRow 6 11, 724724615364029280⟩, ⟨.privateRow 7 9, 264467091009821700⟩, ⟨.privateRow 7 10, 1054216044163442160⟩, ⟨.privateRow 8 7, 87513378843290400⟩, ⟨.privateRow 8 8, 433090430732259300⟩, ⟨.privateRow 8 9, 916898303376815760⟩, ⟨.privateRow 9 4, 2545556277103840⟩, ⟨.privateRow 9 5, 19672722967617720⟩, ⟨.privateRow 9 6, 177445826695257120⟩, ⟨.privateRow 9 7, 439108457800412400⟩, ⟨.privateRow 9 8, 678733844563783008⟩, ⟨.privateRow 9 9, 108324487226755800⟩, ⟨.privateRow 10 4, 69103552196378700⟩, ⟨.privateRow 10 5, 217716210780868800⟩, ⟨.privateRow 10 6, 382663514264631600⟩, ⟨.privateRow 10 7, 9164002597573824⟩, ⟨.privateRow 11 2, 13281163184889600⟩, ⟨.privateRow 11 3, 113927477945381100⟩, ⟨.privateRow 11 4, 99075105722993400⟩, ⟨.privateRow 12 1, 50219398292863800⟩, ⟨.privateRow 12 2, 12228749584301250⟩, ⟨.privateRow 13 0, 14348399512246800⟩, ⟨.hall 7 10, 32670430008296850⟩, ⟨.hall 6 11, 14784155101829520⟩, ⟨.hall 6 12, 183137753774495520⟩, ⟨.hall 8 12, 1586077372657008000⟩, ⟨.hall 5 13, 383686917671400915⟩, ⟨.hall 4 14, 489534397711923564⟩, ⟨.hall 3 16, 3815868611461506600⟩, ⟨.hall 2 18, 47080325473256275200⟩, ⟨.assumptionRow 13, 126426457240776000⟩]
  caps := #[0, 10069265697941620800, 1165652295757098240, 130807816651413720, 0, 31546955774334000, 9770969093435550, 0, 1397404625142400, 12808553465427104, 0, 8153950898914800, 9030461231484000, 0, 0, 0, 0, 0, 0] }

theorem case_39_21_13_checked :
    (Witness.linear .conditional case_39_21_13).check 39 21 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_22_1_checked :
    (Witness.rising).check 39 22 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_22_2_checked :
    (Witness.rising).check 39 22 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_22_3_checked :
    (Witness.rising).check 39 22 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_22_4_checked :
    (Witness.rising).check 39 22 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_22_5_checked :
    (Witness.rising).check 39 22 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_22_6_checked :
    (Witness.rising).check 39 22 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_22_7_checked :
    (Witness.rising).check 39 22 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_22_8_checked :
    (Witness.rising).check 39 22 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_22_9 : Certificate := {
  objectiveScale := 108788680000
  eta := 1744893839969280
  rows := #[⟨.count 2, 318778682302080⟩, ⟨.count 3, 44041791633840⟩, ⟨.count 4, 7370259008112⟩, ⟨.count 5, 1521066587040⟩, ⟨.count 6, 380266646760⟩, ⟨.count 7, 139326347160⟩, ⟨.count 8, 111461077728⟩, ⟨.path 9, 28764504054⟩, ⟨.path 10, 18304831116⟩, ⟨.privateRow 4 15, 14980201236⟩, ⟨.privateRow 4 16, 339551228016⟩, ⟨.privateRow 5 12, 90649422864⟩, ⟨.privateRow 5 13, 106013731824⟩, ⟨.privateRow 5 14, 102556762308⟩, ⟨.privateRow 5 15, 147497366016⟩, ⟨.privateRow 6 8, 12803590800⟩, ⟨.privateRow 6 9, 28808079300⟩, ⟨.privateRow 6 10, 23595188760⟩, ⟨.privateRow 6 11, 93786302610⟩, ⟨.privateRow 7 5, 6666332400⟩, ⟨.privateRow 7 6, 14456417976⟩, ⟨.privateRow 7 7, 17808630840⟩, ⟨.privateRow 7 8, 3535537005⟩, ⟨.privateRow 8 2, 3271630824⟩, ⟨.privateRow 8 3, 6171912747⟩, ⟨.privateRow 9 0, 2560718160⟩, ⟨.privateRow 10 0, 1410185700⟩, ⟨.hall 10 1, 1833241410⟩, ⟨.hall 3 17, 15943839912⟩, ⟨.hall 4 17, 63249738552⟩, ⟨.hall 3 18, 397369548576⟩]
  caps := #[0, 1273317105060, 256010846520, 183725431032, 15668080428, 0, 122237830, 0, 0, 2433198482, 1664639856, 0, 0, 0, 0, 0, 0, 0] }

theorem case_39_22_9_checked :
    (Witness.linear .positive case_39_22_9).check 39 22 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_22_10 : Certificate := {
  objectiveScale := 127155600000
  eta := 2847146125824000
  rows := #[⟨.count 2, 538288564413600⟩, ⟨.count 3, 93421982253600⟩, ⟨.count 4, 17794663286400⟩, ⟨.count 5, 3910915008000⟩, ⟨.count 6, 1002171970800⟩, ⟨.count 7, 326650287600⟩, ⟨.count 8, 136882025280⟩, ⟨.count 9, 124438204800⟩, ⟨.path 10, 9167918760⟩, ⟨.path 11, 33010985700⟩, ⟨.privateRow 5 13, 328516860672⟩, ⟨.privateRow 5 14, 408201753960⟩, ⟨.privateRow 6 11, 354426672600⟩, ⟨.privateRow 6 12, 111624032520⟩, ⟨.privateRow 6 13, 239339850750⟩, ⟨.privateRow 7 10, 310354808400⟩, ⟨.privateRow 8 7, 68635447335⟩, ⟨.privateRow 8 10, 25509831984⟩, ⟨.privateRow 9 8, 11982938240⟩, ⟨.privateRow 9 10, 1728308400⟩, ⟨.privateRow 10 0, 4068172080⟩, ⟨.privateRow 10 8, 311095512⟩, ⟨.privateRow 11 0, 2777638500⟩, ⟨.hall 8 3, 345661680⟩, ⟨.hall 4 14, 3686452770⟩, ⟨.hall 5 14, 2492249760⟩, ⟨.hall 3 17, 273163690800⟩]
  caps := #[0, 0, 571721899320, 0, 36655122240, 17165554560, 23082409350, 0, 10056654153, 2717395200, 6462043488, 0, 0, 0, 0, 0, 0, 0] }

theorem case_39_22_10_checked :
    (Witness.linear .positive case_39_22_10).check 39 22 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_22_11 : Certificate := {
  objectiveScale := 108900000
  eta := 3188767982400
  rows := #[⟨.count 2, 686811565440⟩, ⟨.count 3, 162504522180⟩, ⟨.count 4, 37143890784⟩, ⟨.count 5, 9636386760⟩, ⟨.count 6, 2493330840⟩, ⟨.count 7, 750449700⟩, ⟨.count 8, 257297040⟩, ⟨.count 9, 120071952⟩, ⟨.count 10, 107207100⟩, ⟨.path 11, 4949505⟩, ⟨.path 12, 22276485⟩, ⟨.privateRow 11 0, 765765⟩, ⟨.privateRow 12 0, 2042040⟩, ⟨.hall 10 3, 250614⟩, ⟨.hall 9 4, 134946⟩, ⟨.hall 8 6, 22134⟩, ⟨.hall 7 8, 581672⟩]
  caps := #[0, 12478906440, 0, 311595570, 20994831, 1524600, 1531530, 4324320, 2577465, 0, 6822090, 0, 0, 0, 0, 0, 0, 0] }

theorem case_39_22_11_checked :
    (Witness.linear .positive case_39_22_11).check 39 22 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_22_12 : Certificate := {
  objectiveScale := 335758500000
  eta := 9311693088297600
  rows := #[⟨.count 2, 2296464849478800⟩, ⟨.count 3, 559959922201680⟩, ⟨.count 4, 152198844557760⟩, ⟨.count 5, 43788280536000⟩, ⟨.count 6, 13366948795200⟩, ⟨.count 7, 4473109040400⟩, ⟨.count 8, 1701248028480⟩, ⟨.count 9, 762628426560⟩, ⟨.count 10, 513307594800⟩, ⟨.count 11, 345696951600⟩, ⟨.path 10, 98899669440⟩, ⟨.privateRow 4 16, 19174657582080⟩, ⟨.privateRow 5 13, 1290601952640⟩, ⟨.privateRow 5 14, 7962553118520⟩, ⟨.privateRow 5 15, 17008290018720⟩, ⟨.privateRow 6 11, 1081903422600⟩, ⟨.privateRow 6 12, 3430081975320⟩, ⟨.privateRow 6 13, 7187615785350⟩, ⟨.privateRow 6 14, 8975317150800⟩, ⟨.privateRow 7 9, 625546864800⟩, ⟨.privateRow 7 10, 1620236217600⟩, ⟨.privateRow 7 11, 3195077886000⟩, ⟨.privateRow 7 12, 4182409331100⟩, ⟨.privateRow 7 13, 3614104494000⟩, ⟨.privateRow 8 7, 324483729570⟩, ⟨.privateRow 8 8, 811864053000⟩, ⟨.privateRow 8 9, 1482481220220⟩, ⟨.privateRow 8 10, 2202822878256⟩, ⟨.privateRow 9 5, 168024496640⟩, ⟨.privateRow 9 6, 255839023440⟩, ⟨.privateRow 9 7, 1190966736960⟩, ⟨.privateRow 10 3, 92395367064⟩, ⟨.privateRow 10 4, 248506057800⟩, ⟨.privateRow 10 5, 136576485045⟩, ⟨.privateRow 11 1, 60949324800⟩, ⟨.privateRow 11 2, 58663725120⟩, ⟨.privateRow 12 0, 34918884000⟩, ⟨.privateRow 13 0, 32265048816⟩, ⟨.hall 5 14, 36716179500⟩, ⟨.hall 5 15, 918469351800⟩, ⟨.hall 6 15, 770616121275⟩, ⟨.hall 4 17, 52730308350720⟩, ⟨.hall 3 18, 101881137037680⟩, ⟨.hall 2 19, 114823242473940⟩, ⟨.assumptionRow 12, 406098946440⟩]
  caps := #[0, 21833880251040, 0, 0, 161902849680, 128853616320, 63170657550, 0, 17353658322, 10509974640, 0, 39586363200, 3795030360, 13108011840, 0, 0, 0, 0] }

theorem case_39_22_12_checked :
    (Witness.linear .conditional case_39_22_12).check 39 22 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_22_13 : Certificate := {
  objectiveScale := 512794800000
  eta := 11744477769024000
  rows := #[⟨.count 2, 2915147160525600⟩, ⟨.count 3, 734029860564000⟩, ⟨.count 4, 204929152908480⟩, ⟨.count 5, 59229411040800⟩, ⟨.count 6, 17745776848800⟩, ⟨.count 7, 5573053886400⟩, ⟨.count 8, 1759911753600⟩, ⟨.count 9, 703964701440⟩, ⟨.count 10, 366648282000⟩, ⟨.count 11, 345696951600⟩, ⟨.count 12, 460929268800⟩, ⟨.path 9, 169523845920⟩, ⟨.privateRow 2 20, 146805972112800⟩, ⟨.privateRow 4 16, 35852614958160⟩, ⟨.privateRow 5 13, 1299820538016⟩, ⟨.privateRow 5 14, 13194100319400⟩, ⟨.privateRow 5 15, 32387963287680⟩, ⟨.privateRow 6 11, 848237890500⟩, ⟨.privateRow 6 12, 5189295351240⟩, ⟨.privateRow 6 13, 13088470695300⟩, ⟨.privateRow 6 14, 19935190875600⟩, ⟨.privateRow 7 9, 378620470800⟩, ⟨.privateRow 7 10, 2126560035600⟩, ⟨.privateRow 7 11, 5543722023840⟩, ⟨.privateRow 7 12, 8933123499300⟩, ⟨.privateRow 7 13, 10060130480400⟩, ⟨.privateRow 8 7, 130160140110⟩, ⟨.privateRow 8 8, 890431542000⟩, ⟨.privateRow 8 9, 2483431030080⟩, ⟨.privateRow 8 10, 4275118968120⟩, ⟨.privateRow 8 11, 5213738570040⟩, ⟨.privateRow 8 12, 923953670640⟩, ⟨.privateRow 9 5, 22451549120⟩, ⟨.privateRow 9 6, 371536925760⟩, ⟨.privateRow 9 7, 1177930353600⟩, ⟨.privateRow 9 8, 2219444267040⟩, ⟨.privateRow 9 9, 1462682212992⟩, ⟨.privateRow 10 4, 124660415880⟩, ⟨.privateRow 10 5, 590303734020⟩, ⟨.privateRow 10 6, 1110420511200⟩, ⟨.privateRow 11 2, 21998896920⟩, ⟨.privateRow 11 3, 285170886000⟩, ⟨.privateRow 11 4, 273676753350⟩, ⟨.privateRow 12 1, 120993933060⟩, ⟨.privateRow 12 2, 27741113400⟩, ⟨.privateRow 13 0, 32265048816⟩, ⟨.hall 6 15, 13100474061675⟩, ⟨.hall 5 16, 52261245036000⟩, ⟨.hall 4 17, 119275691174640⟩, ⟨.hall 3 18, 213034230208800⟩, ⟨.hall 2 19, 268445206149120⟩, ⟨.assumptionRow 13, 361947663000⟩]
  caps := #[0, 1118796159600, 0, 714249900000, 449697712464, 185395994784, 29351619900, 0, 60394263930, 30000918376, 1099659960, 16250711400, 0, 0, 512794800000, 0, 0, 0] }

theorem case_39_22_13_checked :
    (Witness.linear .conditional case_39_22_13).check 39 22 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_22_14 : Certificate := {
  objectiveScale := 5795102543076000000
  eta := 267681261677563138204800
  rows := #[⟨.count 2, 56536128543968076603600⟩, ⟨.count 3, 13127663407941793751040⟩, ⟨.count 4, 2988887650915319112960⟩, ⟨.count 5, 659313452407790980800⟩, ⟨.count 6, 143696521678621111200⟩, ⟨.count 7, 28688075629243430400⟩, ⟨.count 8, 4303211344386514560⟩, ⟨.path 7, 4803543065897325750⟩, ⟨.path 8, 3947414570346927680⟩, ⟨.privateRow 2 20, 3333195787172721069600⟩, ⟨.privateRow 4 15, 136899112687451043930⟩, ⟨.privateRow 4 16, 664197255758959802880⟩, ⟨.privateRow 5 13, 86105209852914924672⟩, ⟨.privateRow 5 14, 247524302538565972920⟩, ⟨.privateRow 5 15, 566709027326012931360⟩, ⟨.privateRow 6 11, 37802516323950978600⟩, ⟨.privateRow 6 12, 97206470547302516400⟩, ⟨.privateRow 6 13, 221590837147383453750⟩, ⟨.privateRow 6 14, 344214216962187171600⟩, ⟨.privateRow 7 8, 384215298605938800⟩, ⟨.privateRow 7 9, 13612199150610403200⟩, ⟨.privateRow 7 10, 38677673392997839200⟩, ⟨.privateRow 7 11, 91238326242290267040⟩, ⟨.privateRow 7 12, 149779930573215142200⟩, ⟨.privateRow 7 13, 183185316257564821200⟩, ⟨.privateRow 8 6, 258989571652892080⟩, ⟨.privateRow 8 7, 4415274139813246710⟩, ⟨.privateRow 8 8, 14920360762530623400⟩, ⟨.privateRow 8 9, 39431162284152819180⟩, ⟨.privateRow 8 10, 65946713852723335632⟩, ⟨.privateRow 8 11, 101394417302107249320⟩, ⟨.privateRow 8 12, 54059092513855589160⟩, ⟨.privateRow 9 4, 55782369279084448⟩, ⟨.privateRow 9 5, 1275025583521930240⟩, ⟨.privateRow 9 6, 5518470103680854320⟩, ⟨.privateRow 9 7, 17394991889477762560⟩, ⟨.privateRow 9 8, 35302270843763443520⟩, ⟨.privateRow 9 9, 50028816333441737792⟩, ⟨.privateRow 10 2, 16300042971161040⟩, ⟨.privateRow 10 3, 206195543585187156⟩, ⟨.privateRow 10 4, 1842810413684039800⟩, ⟨.privateRow 10 5, 7687507766273825490⟩, ⟨.privateRow 10 6, 18852163984931397120⟩, ⟨.privateRow 10 7, 14568163405475179500⟩, ⟨.privateRow 11 1, 46571551346174400⟩, ⟨.privateRow 11 2, 230529179163563280⟩, ⟨.privateRow 11 3, 3201794155049490000⟩, ⟨.privateRow 11 4, 10437848945461337400⟩, ⟨.privateRow 11 5, 1646636994025452000⟩, ⟨.privateRow 12 0, 85381177467986400⟩, ⟨.privateRow 12 1, 375677180859140160⟩, ⟨.privateRow 12 2, 4695964760739252000⟩, ⟨.privateRow 13 0, 1183383119706291504⟩, ⟨.privateRow 13 1, 313064317382616800⟩, ⟨.privateRow 14 0, 406983612597401840⟩, ⟨.hall 6 15, 301568986978723839375⟩, ⟨.hall 5 16, 991124797737202128000⟩, ⟨.hall 4 17, 2185501999648047880800⟩, ⟨.hall 3 18, 4001184416585877721200⟩, ⟨.hall 2 19, 5653612854396807660360⟩]
  caps := #[0, 0, 0, 13893073528395821760, 1952305449613044526, 3877165008195086608, 0, 273672281958497565, 0, 1176586108323545920, 0, 290868991019222400, 1101224019252255360, 0, 0, 5795102543076000000, 0, 0] }

theorem case_39_22_14_checked :
    (Witness.linear .negative case_39_22_14).check 39 22 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_23_1_checked :
    (Witness.rising).check 39 23 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_23_2_checked :
    (Witness.rising).check 39 23 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_23_3_checked :
    (Witness.rising).check 39 23 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_23_4_checked :
    (Witness.rising).check 39 23 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_23_5_checked :
    (Witness.rising).check 39 23 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_23_6_checked :
    (Witness.rising).check 39 23 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_23_7_checked :
    (Witness.rising).check 39 23 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_23_8_checked :
    (Witness.rising).check 39 23 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_23_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_39_23_9_checked :
    (Witness.linear .positive case_39_23_9).check 39 23 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_23_10 : Certificate := {
  objectiveScale := 4954950000
  eta := 175642859492100
  rows := #[⟨.count 2, 35652878941680⟩, ⟨.count 3, 7290364601520⟩, ⟨.count 4, 1521066587040⟩, ⟨.count 5, 326491565400⟩, ⟨.count 6, 78567489000⟩, ⟨.count 7, 20776735980⟩, ⟨.count 8, 7604556960⟩, ⟨.count 9, 4888643760⟩, ⟨.path 10, 2123550000⟩, ⟨.privateRow 5 14, 66962779884⟩, ⟨.privateRow 5 15, 71059928940⟩, ⟨.privateRow 8 12, 5567622060⟩, ⟨.privateRow 9 8, 387987600⟩, ⟨.privateRow 9 9, 1357956600⟩, ⟨.privateRow 10 2, 640179540⟩, ⟨.privateRow 10 7, 448957080⟩, ⟨.privateRow 10 8, 1338557220⟩, ⟨.privateRow 10 9, 419026608⟩, ⟨.privateRow 10 10, 349188840⟩, ⟨.privateRow 10 12, 87297210⟩, ⟨.hall 10 3, 228926250⟩, ⟨.hall 8 4, 25766356⟩, ⟨.hall 9 4, 21453660⟩, ⟨.hall 9 5, 3488400⟩, ⟨.hall 10 12, 268606800⟩, ⟨.hall 4 15, 1371034665⟩, ⟨.hall 3 17, 11643967335⟩, ⟨.hall 2 20, 1697756140080⟩]
  caps := #[0, 406514007900, 14266858320, 2469263940, 0, 535134600, 711711000, 458764020, 0, 1363277916, 0, 0, 0, 0, 0, 0, 0] }

theorem case_39_23_10_checked :
    (Witness.linear .positive case_39_23_10).check 39 23 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_23_11 : Certificate := {
  objectiveScale := 67245750000
  eta := 3449940344650800
  rows := #[⟨.count 2, 775624885995960⟩, ⟨.count 3, 192420684876420⟩, ⟨.count 4, 46945646027280⟩, ⟨.count 5, 11628861344100⟩, ⟨.count 6, 3189840053400⟩, ⟨.count 7, 872622911160⟩, ⟨.count 8, 296577721440⟩, ⟨.count 9, 128326898700⟩, ⟨.count 10, 109994484600⟩, ⟨.path 10, 25216731540⟩, ⟨.privateRow 6 11, 50632381800⟩, ⟨.hall 12 3, 488864376⟩, ⟨.hall 9 4, 1197742140⟩, ⟨.hall 11 5, 135795660⟩, ⟨.hall 10 7, 99710100⟩, ⟨.hall 8 8, 158523232⟩, ⟨.hall 4 15, 59758183485⟩]
  caps := #[0, 8904897401400, 860016231360, 0, 0, 23307235380, 0, 9962692740, 0, 0, 0, 0, 34220506320, 0, 0, 0, 0] }

theorem case_39_23_11_checked :
    (Witness.linear .positive case_39_23_11).check 39 23 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_23_12 : Certificate := {
  objectiveScale := 14812875000
  eta := 823162057918200
  rows := #[⟨.count 2, 174769014420000⟩, ⟨.count 3, 42244167485520⟩, ⟨.count 4, 10002165132960⟩, ⟨.count 5, 2727164840400⟩, ⟨.count 6, 775199224800⟩, ⟨.count 7, 234654900480⟩, ⟨.count 8, 78218300160⟩, ⟨.count 9, 36664828200⟩, ⟨.count 10, 20951330400⟩, ⟨.path 9, 6025318299⟩, ⟨.path 10, 1590114240⟩, ⟨.privateRow 2 21, 4543994374920⟩, ⟨.privateRow 4 16, 671228247690⟩, ⟨.privateRow 4 17, 1905174311040⟩, ⟨.privateRow 5 14, 482439301344⟩, ⟨.privateRow 5 15, 818149452120⟩, ⟨.privateRow 5 16, 1404553910760⟩, ⟨.privateRow 6 11, 39657875400⟩, ⟨.privateRow 6 12, 213005192400⟩, ⟨.privateRow 6 13, 388297990080⟩, ⟨.privateRow 6 14, 603223721100⟩, ⟨.privateRow 6 15, 625630005000⟩, ⟨.privateRow 7 9, 35093478420⟩, ⟨.privateRow 7 10, 100117428840⟩, ⟨.privateRow 7 11, 129374465220⟩, ⟨.privateRow 7 12, 385713992664⟩, ⟨.privateRow 7 13, 155039844960⟩, ⟨.privateRow 8 7, 22451549120⟩, ⟨.privateRow 8 8, 53775081360⟩, ⟨.privateRow 8 9, 88461172800⟩, ⟨.privateRow 8 10, 114068354400⟩, ⟨.privateRow 9 5, 13117860756⟩, ⟨.privateRow 9 6, 32138306200⟩, ⟨.privateRow 9 7, 41451625215⟩, ⟨.privateRow 10 3, 7713898920⟩, ⟨.privateRow 10 4, 16132524408⟩, ⟨.privateRow 11 0, 805820400⟩, ⟨.privateRow 11 1, 4219365150⟩, ⟨.privateRow 11 2, 476166600⟩, ⟨.privateRow 12 0, 1280359080⟩, ⟨.privateRow 13 0, 1047566520⟩, ⟨.hall 5 17, 410781871500⟩, ⟨.hall 4 18, 2763149669280⟩, ⟨.hall 3 19, 7205476794516⟩, ⟨.hall 2 20, 11851003644480⟩, ⟨.assumptionRow 12, 18601415910⟩]
  caps := #[0, 0, 251590559220, 48612074940, 0, 19121458356, 1523374776, 10644406344, 1565013285, 0, 4075122150, 0, 5332503330, 3289643280, 0, 0, 0] }

theorem case_39_23_12_checked :
    (Witness.linear .conditional case_39_23_12).check 39 23 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_23_13 : Certificate := {
  objectiveScale := 11903470081650000
  eta := 782819615994109293600
  rows := #[⟨.count 2, 163184785622652633840⟩, ⟨.count 3, 38139505811226860040⟩, ⟨.count 4, 8807844129440035680⟩, ⟨.count 5, 2107805264212447800⟩, ⟨.count 6, 536921322494356800⟩, ⟨.count 7, 138899211688757520⟩, ⟨.count 8, 36313519395753600⟩, ⟨.count 9, 16341083728089120⟩, ⟨.count 10, 11672202662920800⟩, ⟨.count 11, 10699519107677400⟩, ⟨.path 8, 11175895908777600⟩, ⟨.privateRow 2 21, 6231399928311317760⟩, ⟨.privateRow 4 16, 529626195830031300⟩, ⟨.privateRow 4 17, 1874555747665080480⟩, ⟨.privateRow 5 14, 357791918960732256⟩, ⟨.privateRow 5 15, 769830399797388930⟩, ⟨.privateRow 5 16, 1505778989087132760⟩, ⟨.privateRow 6 11, 8337287616372000⟩, ⟨.privateRow 6 12, 164221406910260700⟩, ⟨.privateRow 6 13, 342384611445676800⟩, ⟨.privateRow 6 14, 638080412239670400⟩, ⟨.privateRow 6 15, 798897426706579200⟩, ⟨.privateRow 7 9, 8754151997190600⟩, ⟨.privateRow 7 10, 67782148321104360⟩, ⟨.privateRow 7 11, 154559416928176260⟩, ⟨.privateRow 7 12, 244182479708303136⟩, ⟨.privateRow 7 13, 483083287711634610⟩, ⟨.privateRow 7 14, 162827227147745160⟩, ⟨.privateRow 8 7, 4387883593653560⟩, ⟨.privateRow 8 8, 29958653501496720⟩, ⟨.privateRow 8 9, 71005899532768200⟩, ⟨.privateRow 8 10, 147448019379841180⟩, ⟨.privateRow 8 11, 175394298681489888⟩, ⟨.privateRow 9 5, 1089405581872608⟩, ⟨.privateRow 9 6, 13920182435038880⟩, ⟨.privateRow 9 7, 35859600403306680⟩, ⟨.privateRow 9 8, 78787367974715400⟩, ⟨.privateRow 9 9, 27083833215999560⟩, ⟨.privateRow 10 4, 5602657278201984⟩, ⟨.privateRow 10 5, 20037281238014040⟩, ⟨.privateRow 10 6, 26627212324788075⟩, ⟨.privateRow 11 2, 1326386666241000⟩, ⟨.privateRow 11 3, 11088592529774760⟩, ⟨.privateRow 11 4, 2918050665730200⟩, ⟨.privateRow 12 1, 3696197509924920⟩, ⟨.privateRow 13 0, 583610133146040⟩, ⟨.hall 5 17, 1029531505249847600⟩, ⟨.hall 4 18, 3627474857053407360⟩, ⟨.hall 3 19, 8078564907060744096⟩, ⟨.hall 2 20, 12518437355982558000⟩, ⟨.assumptionRow 13, 9523276211121750⟩]
  caps := #[0, 161463739827782700, 162422298700552800, 32060377677542760, 36019487032044516, 0, 1195541017004700, 1525468986717192, 1052011275861000, 0, 1113150503956491, 0, 9523276211121750, 21155027081597010, 11903470081650000, 0, 0] }

theorem case_39_23_13_checked :
    (Witness.linear .conditional case_39_23_13).check 39 23 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_23_14 : Certificate := {
  objectiveScale := 1865630223604501200000
  eta := 196753251354716688332500800
  rows := #[⟨.count 2, 37687277373016988852094960⟩, ⟨.count 3, 7841615090224215839338800⟩, ⟨.count 4, 1532287624023832785389280⟩, ⟨.count 5, 314656882574764571641800⟩, ⟨.count 6, 59109440785451813156400⟩, ⟨.count 7, 9471753764415772469640⟩, ⟨.count 8, 886245966261124909440⟩, ⟨.path 7, 4704706945875044908800⟩, ⟨.path 8, 499894062970431729600⟩, ⟨.privateRow 2 21, 1069311148666938523546200⟩, ⟨.privateRow 4 16, 115744118839223565460770⟩, ⟨.privateRow 4 17, 371582360086215755557080⟩, ⟨.privateRow 5 14, 72070788042020764956960⟩, ⟨.privateRow 5 15, 147470933140330532642910⟩, ⟨.privateRow 5 16, 304995218960435700977280⟩, ⟨.privateRow 6 11, 3832109471460731432400⟩, ⟨.privateRow 6 12, 27517145961366623862300⟩, ⟨.privateRow 6 13, 62955115246192051602720⟩, ⟨.privateRow 6 14, 125370174356693730213750⟩, ⟨.privateRow 6 15, 174677497367985110499000⟩, ⟨.privateRow 7 9, 2448056659036031418375⟩, ⟨.privateRow 7 10, 10672255315652143201560⟩, ⟨.privateRow 7 11, 25614091007029119034440⟩, ⟨.privateRow 7 12, 56061387694346587128576⟩, ⟨.privateRow 7 13, 81417913467431066736210⟩, ⟨.privateRow 7 14, 86670107754090188688360⟩, ⟨.privateRow 8 7, 941636339152445216280⟩, ⟨.privateRow 8 8, 4382763255025719278715⟩, ⟨.privateRow 8 9, 10943555101242283479960⟩, ⟨.privateRow 8 10, 25784218580909602834020⟩, ⟨.privateRow 8 11, 42218542217764337873448⟩, ⟨.privateRow 8 12, 27889052750779774493940⟩, ⟨.privateRow 9 5, 216022454276149196676⟩, ⟨.privateRow 9 6, 1754028474891809716600⟩, ⟨.privateRow 9 7, 5068219119555808075860⟩, ⟨.privateRow 9 8, 12842653600373265428760⟩, ⟨.privateRow 9 9, 23494749834735030151300⟩, ⟨.privateRow 9 10, 742230996743692111656⟩, ⟨.privateRow 10 4, 541243072252329855408⟩, ⟨.privateRow 10 5, 2405524765565910468480⟩, ⟨.privateRow 10 6, 7130521395955858785885⟩, ⟨.privateRow 10 7, 6867275822750425797000⟩, ⟨.privateRow 11 2, 10790332381426033800⟩, ⟨.privateRow 11 3, 949549249565490974400⟩, ⟨.privateRow 11 4, 4233407070979480594200⟩, ⟨.privateRow 11 5, 712161937174118230800⟩, ⟨.privateRow 12 2, 1880107514139672129312⟩, ⟨.privateRow 13 1, 548364691624071037716⟩, ⟨.hall 6 16, 12232428567931913140800⟩, ⟨.hall 5 17, 290937933611659911677100⟩, ⟨.hall 4 18, 827412227933222374803360⟩, ⟨.hall 3 19, 1721081753568691528374360⟩, ⟨.hall 2 20, 2607082419607012019312640⟩, ⟨.assumptionRow 14, 507809642381265190680⟩]
  caps := #[0, 0, 0, 5199314671509414412320, 731989240200648440010, 355850661825251901000, 308158900930724590890, 0, 544426232401002172221, 75764733828966797328, 491553162122411254437, 389115986185578818880, 507809642381265190680, 507809642381265190680, 14417232146454744409320, 1865630223604501200000, 0] }

theorem case_39_23_14_checked :
    (Witness.linear .conditional case_39_23_14).check 39 23 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_24_1_checked :
    (Witness.rising).check 39 24 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_24_2_checked :
    (Witness.rising).check 39 24 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_24_3_checked :
    (Witness.rising).check 39 24 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_24_4_checked :
    (Witness.rising).check 39 24 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_24_5_checked :
    (Witness.rising).check 39 24 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_24_6_checked :
    (Witness.rising).check 39 24 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_24_7_checked :
    (Witness.rising).check 39 24 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_24_8_checked :
    (Witness.rising).check 39 24 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_24_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_39_24_9_checked :
    (Witness.linear .positive case_39_24_9).check 39 24 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_24_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_39_24_10_checked :
    (Witness.linear .positive case_39_24_10).check 39 24 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_24_11 : Certificate := {
  objectiveScale := 330330000
  eta := 33672163444920
  rows := #[⟨.count 2, 7523389954080⟩, ⟨.count 3, 1605570286320⟩, ⟨.count 4, 377705928600⟩, ⟨.count 5, 85551265800⟩, ⟨.count 6, 21649708080⟩, ⟨.count 7, 5431826400⟩, ⟨.count 8, 1629547920⟩, ⟨.count 9, 698377680⟩, ⟨.count 10, 581981400⟩, ⟨.path 9, 259568595⟩, ⟨.hall 8 5, 1314610⟩, ⟨.hall 10 6, 116280⟩, ⟨.hall 12 7, 6466460⟩, ⟨.hall 10 8, 1976760⟩, ⟨.hall 11 9, 7610526⟩, ⟨.hall 9 11, 12023352⟩]
  caps := #[0, 36261598230, 7529730780, 786185400, 238828590, 106370550, 154053900, 113352525, 69386460, 0, 0, 0, 1414662480, 0, 0, 0] }

theorem case_39_24_11_checked :
    (Witness.linear .positive case_39_24_11).check 39 24 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_24_12 : Certificate := {
  objectiveScale := 1386000000
  eta := 148204124228160
  rows := #[⟨.count 2, 29960402472000⟩, ⟨.count 3, 6337777446000⟩, ⟨.count 4, 1521066587040⟩, ⟨.count 5, 363156393600⟩, ⟨.count 6, 100566385920⟩, ⟨.count 7, 29331862560⟩, ⟨.count 8, 8147739600⟩, ⟨.count 9, 4190266080⟩, ⟨.count 10, 3491888400⟩, ⟨.path 9, 1056678480⟩, ⟨.privateRow 2 22, 948746078280⟩, ⟨.privateRow 3 19, 174128834880⟩, ⟨.privateRow 3 20, 772056525240⟩, ⟨.privateRow 4 17, 215580460095⟩, ⟨.privateRow 4 18, 328412104020⟩, ⟨.privateRow 4 19, 488777078790⟩, ⟨.privateRow 5 14, 29681051400⟩, ⟨.privateRow 5 15, 98191901808⟩, ⟨.privateRow 5 16, 150325795620⟩, ⟨.privateRow 5 17, 212539607280⟩, ⟨.privateRow 5 18, 163420377120⟩, ⟨.privateRow 6 11, 872972100⟩, ⟨.privateRow 6 12, 24443218800⟩, ⟨.privateRow 6 13, 45161756640⟩, ⟨.privateRow 6 14, 34430019624⟩, ⟨.privateRow 6 15, 161412541290⟩, ⟨.privateRow 6 16, 10708457760⟩, ⟨.privateRow 7 9, 2534852320⟩, ⟨.privateRow 7 10, 13152779640⟩, ⟨.privateRow 7 11, 23944377600⟩, ⟨.privateRow 7 12, 32202970800⟩, ⟨.privateRow 7 13, 28214458272⟩, ⟨.privateRow 8 7, 2444321880⟩, ⟨.privateRow 8 8, 7332965640⟩, ⟨.privateRow 8 9, 13443770340⟩, ⟨.privateRow 8 10, 9719089380⟩, ⟨.privateRow 9 5, 1883503440⟩, ⟨.privateRow 9 6, 4818805992⟩, ⟨.privateRow 9 7, 3103900800⟩, ⟨.privateRow 10 3, 1396755360⟩, ⟨.privateRow 10 4, 1174544280⟩, ⟨.privateRow 11 1, 590934960⟩, ⟨.privateRow 12 0, 147733740⟩, ⟨.hall 4 19, 52238650464⟩, ⟨.hall 3 20, 322650488160⟩, ⟨.hall 2 21, 776246791320⟩, ⟨.assumptionRow 12, 1841139300⟩]
  caps := #[0, 203505038880, 17287618920, 7720953240, 0, 5101482672, 0, 0, 836549784, 0, 0, 68334420, 0, 1386000000, 0, 0] }

theorem case_39_24_12_checked :
    (Witness.linear .conditional case_39_24_12).check 39 24 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_24_13 : Certificate := {
  objectiveScale := 900901157402400000
  eta := 90401688441562527469440
  rows := #[⟨.count 2, 18705564785243947010400⟩, ⟨.count 3, 3914568141569491966560⟩, ⟨.count 4, 859391596034389978560⟩, ⟨.count 5, 186356809815630854400⟩, ⟨.count 6, 44080553091004990560⟩, ⟨.count 7, 10870813905911799840⟩, ⟨.count 8, 2508649362902723040⟩, ⟨.count 9, 1075135441244024160⟩, ⟨.path 7, 1069098603819246000⟩, ⟨.path 8, 575353133133979200⟩, ⟨.privateRow 2 22, 2049924907971939398400⟩, ⟨.privateRow 3 19, 331141715903159441280⟩, ⟨.privateRow 3 20, 715502636147898078480⟩, ⟨.privateRow 4 16, 25426953185421171384⟩, ⟨.privateRow 4 17, 192426845327654407470⟩, ⟨.privateRow 4 18, 305846168160556983960⟩, ⟨.privateRow 4 19, 465175267578247786560⟩, ⟨.privateRow 5 14, 27654872738665732560⟩, ⟨.privateRow 5 15, 79918401132472462560⟩, ⟨.privateRow 5 16, 131704091552392959600⟩, ⟨.privateRow 5 17, 207262221173153546400⟩, ⟨.privateRow 5 18, 182235457290862095120⟩, ⟨.privateRow 6 12, 16690197802169136960⟩, ⟨.privateRow 6 13, 35150955954006012120⟩, ⟨.privateRow 6 14, 57340556866347955200⟩, ⟨.privateRow 6 15, 87847525011647140740⟩, ⟨.privateRow 6 16, 102197596664918074320⟩, ⟨.privateRow 7 9, 384925034519465440⟩, ⟨.privateRow 7 10, 7854461695754954280⟩, ⟨.privateRow 7 11, 17321626553375944800⟩, ⟨.privateRow 7 12, 27256674427093871760⟩, ⟨.privateRow 7 13, 44892877646611586592⟩, ⟨.privateRow 7 14, 19919870536382336520⟩, ⟨.privateRow 8 7, 250864936290272304⟩, ⟨.privateRow 8 8, 3681675222408162980⟩, ⟨.privateRow 8 9, 9067722176325467655⟩, ⟨.privateRow 8 10, 15022031304048448680⟩, ⟨.privateRow 8 11, 15365477347779178620⟩, ⟨.privateRow 9 5, 54299769759799200⟩, ⟨.privateRow 9 6, 1839676199461996896⟩, ⟨.privateRow 9 7, 5136758219277004320⟩, ⟨.privateRow 9 8, 7824596822387064720⟩, ⟨.privateRow 10 4, 879656270108747040⟩, ⟨.privateRow 10 5, 3261244171773539952⟩, ⟨.privateRow 10 6, 557477636200605120⟩, ⟨.privateRow 11 2, 358378480414674720⟩, ⟨.privateRow 11 3, 944815993820506080⟩, ⟨.privateRow 12 1, 328513607046785160⟩, ⟨.hall 4 19, 88107349409947779912⟩, ⟨.hall 3 20, 351415698509475325440⟩, ⟨.hall 2 21, 819969963188775759360⟩, ⟨.assumptionRow 13, 797368648076708400⟩]
  caps := #[0, 0, 49422127612496358720, 1622790165284127840, 5725249212786802842, 2421801128312365800, 203410994008677840, 431138255789793552, 390198833467180101, 1278973078485979968, 797368648076708400, 2730381828292350960, 468855041029923240, 8211642925947291600, 900901157402400000, 0] }

theorem case_39_24_13_checked :
    (Witness.linear .conditional case_39_24_13).check 39 24 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_24_14 : Certificate := {
  objectiveScale := 291471600000
  eta := 36355462644140640
  rows := #[⟨.count 2, 7199875425702960⟩, ⟨.count 3, 1406972037350880⟩, ⟨.count 4, 279256558220640⟩, ⟨.count 5, 52231544164800⟩, ⟨.count 6, 9474559174080⟩, ⟨.count 7, 1417134919200⟩, ⟨.count 8, 283426983840⟩, ⟨.count 9, 182203061040⟩, ⟨.path 7, 923553430800⟩, ⟨.privateRow 2 22, 829418701030920⟩, ⟨.privateRow 3 19, 123149024478480⟩, ⟨.privateRow 3 20, 281594830837320⟩, ⟨.privateRow 4 16, 8484589209096⟩, ⟨.privateRow 4 17, 69062551928370⟩, ⟨.privateRow 4 18, 117915747669720⟩, ⟨.privateRow 4 19, 192072393513000⟩, ⟨.privateRow 5 14, 8715379753080⟩, ⟨.privateRow 5 15, 27379046638944⟩, ⟨.privateRow 5 16, 49179642892380⟩, ⟨.privateRow 5 17, 85432990843200⟩, ⟨.privateRow 5 18, 85696173042480⟩, ⟨.privateRow 6 11, 64530250785⟩, ⟨.privateRow 6 12, 4758970427640⟩, ⟨.privateRow 6 13, 11347201745880⟩, ⟨.privateRow 6 14, 20625386509728⟩, ⟨.privateRow 6 15, 37609748516340⟩, ⟨.privateRow 6 16, 43941304887480⟩, ⟨.privateRow 6 17, 24217823529900⟩, ⟨.privateRow 7 9, 107972184320⟩, ⟨.privateRow 7 10, 2027009054070⟩, ⟨.privateRow 7 11, 5162420062800⟩, ⟨.privateRow 7 12, 9315975028360⟩, ⟨.privateRow 7 13, 17062304427168⟩, ⟨.privateRow 7 14, 23969824919040⟩, ⟨.privateRow 8 7, 33656954331⟩, ⟨.privateRow 8 8, 832566765030⟩, ⟨.privateRow 8 9, 2453414828865⟩, ⟨.privateRow 8 10, 3937610596920⟩, ⟨.privateRow 8 11, 10829272674220⟩, ⟨.privateRow 8 12, 5516197672986⟩, ⟨.privateRow 9 6, 313794160680⟩, ⟨.privateRow 9 7, 1228183596640⟩, ⟨.privateRow 9 8, 2684964552270⟩, ⟨.privateRow 9 9, 4777769156160⟩, ⟨.privateRow 10 4, 88340878080⟩, ⟨.privateRow 10 5, 622527125220⟩, ⟨.privateRow 10 6, 1673568856960⟩, ⟨.privateRow 10 7, 914811202305⟩, ⟨.privateRow 11 2, 10122392280⟩, ⟨.privateRow 11 3, 281586548880⟩, ⟨.privateRow 11 4, 807766903944⟩, ⟨.privateRow 12 1, 55673157540⟩, ⟨.privateRow 12 2, 273304591560⟩, ⟨.privateRow 13 0, 55673157540⟩, ⟨.hall 4 19, 51776036512200⟩, ⟨.hall 3 20, 159384296728800⟩, ⟨.hall 2 21, 341873676864720⟩, ⟨.assumptionRow 14, 128720798360⟩]
  caps := #[0, 0, 8900238199160, 0, 168888621174, 0, 231651241965, 0, 0, 0, 167802108565, 0, 0, 3520607730640, 2494523601640, 291471600000] }

theorem case_39_24_14_checked :
    (Witness.linear .conditional case_39_24_14).check 39 24 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_24_15 : Certificate := {
  objectiveScale := 1877667675428160000
  eta := 296316645447343840038720
  rows := #[⟨.count 2, 61190258502962391042240⟩, ⟨.count 3, 11873795813099002823040⟩, ⟨.count 4, 2444141236428081590400⟩, ⟨.count 5, 465892024539077136000⟩, ⟨.count 6, 81710293534545836160⟩, ⟨.count 7, 11707030360212707520⟩, ⟨.count 8, 1672432908601815360⟩, ⟨.path 7, 5778615017566591200⟩, ⟨.path 8, 850378531381579200⟩, ⟨.privateRow 5 14, 32254063237320724800⟩, ⟨.privateRow 6 12, 22680238117671557280⟩, ⟨.privateRow 6 14, 203272274091203501184⟩, ⟨.privateRow 7 10, 10870813905911799840⟩, ⟨.privateRow 7 12, 75259480887081691200⟩, ⟨.privateRow 7 14, 109604085260154685200⟩, ⟨.privateRow 8 7, 125432468145136152⟩, ⟨.privateRow 8 8, 4111397566979462760⟩, ⟨.privateRow 8 9, 10112992744201602255⟩, ⟨.privateRow 8 11, 101007979209097140180⟩, ⟨.privateRow 8 14, 310584728068262127480⟩, ⟨.privateRow 9 6, 621189366052102848⟩, ⟨.privateRow 9 7, 7618861028074936640⟩, ⟨.privateRow 9 12, 146517068742866181360⟩, ⟨.privateRow 10 5, 1361838225575763936⟩, ⟨.hall 10 4, 189750843776001600⟩, ⟨.hall 11 4, 427297418955958320⟩, ⟨.hall 9 5, 213618874439649600⟩, ⟨.hall 12 6, 733822602753857760⟩, ⟨.hall 10 7, 42604434734611680⟩, ⟨.hall 8 8, 32895450261321088⟩, ⟨.hall 6 11, 87760642747528080⟩, ⟨.hall 5 13, 261510268861241400⟩, ⟨.hall 4 15, 1201871608195622364⟩, ⟨.hall 3 18, 32527293146448905376⟩]
  caps := #[0, 0, 0, 0, 0, 1496495143285848420, 1217391973652368800, 24234377024938080, 0, 1043048819179712576, 0, 0, 12368196978045289920, 0, 65718368639985600000, 15021341403425280000] }

theorem case_39_24_15_checked :
    (Witness.linear .negative case_39_24_15).check 39 24 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_25_1_checked :
    (Witness.rising).check 39 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_25_2_checked :
    (Witness.rising).check 39 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_25_3_checked :
    (Witness.rising).check 39 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_25_4_checked :
    (Witness.rising).check 39 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_25_5_checked :
    (Witness.rising).check 39 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_25_6_checked :
    (Witness.rising).check 39 25 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_25_7_checked :
    (Witness.rising).check 39 25 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_25_8_checked :
    (Witness.rising).check 39 25 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_25_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_39_25_9_checked :
    (Witness.linear .positive case_39_25_9).check 39 25 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_25_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_39_25_10_checked :
    (Witness.linear .positive case_39_25_10).check 39 25 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_25_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_39_25_11_checked :
    (Witness.linear .positive case_39_25_11).check 39 25 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_25_12 : Certificate := {
  objectiveScale := 6932116000
  eta := 4421949550563402
  rows := #[⟨.count 2, 643724665756128⟩, ⟨.count 3, 91770665159448⟩, ⟨.count 4, 12635091579924⟩, ⟨.count 5, 1662512049990⟩, ⟨.count 6, 302274918180⟩, ⟨.count 7, 105796221363⟩, ⟨.count 8, 40303322424⟩, ⟨.path 5, 624318581718⟩, ⟨.path 6, 10001232787⟩]
  caps := #[0, 959659207251, 22669919407, 0, 0, 0, 0, 0, 0, 13864232000, 6932116000, 6932116000, 0, 0, 0] }

theorem case_39_25_12_checked :
    (Witness.linear .positive case_39_25_12).check 39 25 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_25_13 : Certificate := {
  objectiveScale := 3240162586029600000
  eta := 945551056676913706219200
  rows := #[⟨.count 2, 156843543431055011731200⟩, ⟨.count 3, 26414966999600390811600⟩, ⟨.count 4, 4653061402968495316800⟩, ⟨.count 5, 789115676526820843200⟩, ⟨.count 6, 136054426987382904000⟩, ⟨.count 7, 31746032963722677600⟩, ⟨.count 8, 9070295132492193600⟩, ⟨.path 6, 34263252600215438800⟩, ⟨.path 7, 4619490458245462800⟩, ⟨.privateRow 2 23, 14217687620181513468000⟩, ⟨.privateRow 3 19, 274376427757888856400⟩, ⟨.privateRow 3 20, 3467120314395141003600⟩, ⟨.privateRow 3 21, 4951247355449176181400⟩, ⟨.privateRow 4 17, 772789145288334894720⟩, ⟨.privateRow 4 18, 1571428631704272541200⟩, ⟨.privateRow 4 19, 2117913913436927205600⟩, ⟨.privateRow 4 20, 2789115753241349532000⟩, ⟨.privateRow 5 14, 101846456773412345280⟩, ⟨.privateRow 5 15, 416326546581391686240⟩, ⟨.privateRow 5 16, 666122474530226697984⟩, ⟨.privateRow 5 17, 901360578791411739000⟩, ⟨.privateRow 5 18, 1235374197045436768320⟩, ⟨.privateRow 5 19, 678911590667040690960⟩, ⟨.privateRow 6 11, 4535147566246096800⟩, ⟨.privateRow 6 12, 80876798264722059600⟩, ⟨.privateRow 6 13, 196307101796081047200⟩, ⟨.privateRow 6 14, 313429087356119134400⟩, ⟨.privateRow 6 15, 411186712672979443200⟩, ⟨.privateRow 6 16, 529856407323085642800⟩, ⟨.privateRow 7 9, 4875283633714554060⟩, ⟨.privateRow 7 10, 47871002088153244000⟩, ⟨.privateRow 7 11, 102465990324872749575⟩, ⟨.privateRow 7 12, 163751221052671566600⟩, ⟨.privateRow 7 13, 218065012143666487800⟩, ⟨.privateRow 7 14, 31972790342034982440⟩, ⟨.privateRow 8 7, 3092146067895066000⟩, ⟨.privateRow 8 8, 28458050978194257420⟩, ⟨.privateRow 8 9, 61476444786891534400⟩, ⟨.privateRow 8 10, 102607713686317940100⟩, ⟨.privateRow 8 11, 2429543339060409000⟩, ⟨.privateRow 9 5, 1637692176699979400⟩, ⟨.privateRow 9 6, 18415447693241726400⟩, ⟨.privateRow 9 7, 44746789320294821760⟩, ⟨.privateRow 10 3, 837258012230048640⟩, ⟨.privateRow 10 4, 13605442698738290400⟩, ⟨.privateRow 10 5, 5194805394063710880⟩, ⟨.privateRow 11 2, 5232862576437804000⟩, ⟨.privateRow 12 0, 1781665115310966600⟩, ⟨.hall 3 21, 1255102088958607289400⟩, ⟨.hall 2 22, 4294587564906086448000⟩, ⟨.assumptionRow 13, 3092324767771022784⟩]
  caps := #[0, 135749184234144103392, 132295933810729680992, 0, 8139084531306128400, 11714535254231803136, 731438767251593632, 11986746749335229586, 58841352562297536, 7256009185516349440, 2155434701622914880, 25314591044544710832, 0, 32549463678554577216, 3240162586029600000] }

theorem case_39_25_13_checked :
    (Witness.linear .conditional case_39_25_13).check 39 25 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_25_14 : Certificate := {
  objectiveScale := 82868247693000000
  eta := 27407157728271632110800
  rows := #[⟨.count 2, 4391024432416236014400⟩, ⟨.count 3, 710785597192900128900⟩, ⟨.count 4, 112322705621906379600⟩, ⟨.count 5, 15449591479593070800⟩, ⟨.count 6, 1809411614727116400⟩, ⟨.count 7, 365361960666052350⟩, ⟨.count 8, 139185508825162800⟩, ⟨.path 5, 320213513213193600⟩, ⟨.path 6, 1243037350673418300⟩, ⟨.privateRow 2 23, 436346570166885378000⟩, ⟨.privateRow 3 19, 2870701119518982750⟩, ⟨.privateRow 3 20, 97731424780068479400⟩, ⟨.privateRow 3 21, 150233358588160097250⟩, ⟨.privateRow 4 17, 17036306280199926720⟩, ⟨.privateRow 4 18, 43556365167974383725⟩, ⟨.privateRow 4 19, 64338501454431504300⟩, ⟨.privateRow 4 20, 92854132574986732950⟩, ⟨.privateRow 5 14, 1789527970609236000⟩, ⟨.privateRow 5 15, 9548125905406168080⟩, ⟨.privateRow 5 16, 17787908027855805840⟩, ⟨.privateRow 5 17, 27203807699878069260⟩, ⟨.privateRow 5 18, 42173209174024328400⟩, ⟨.privateRow 5 19, 34114368213047402280⟩, ⟨.privateRow 6 11, 7732528268064600⟩, ⟨.privateRow 6 12, 1423751767357394475⟩, ⟨.privateRow 6 13, 4361145943188434400⟩, ⟨.privateRow 6 14, 8049561927055248600⟩, ⟨.privateRow 6 15, 12132336852593357400⟩, ⟨.privateRow 6 16, 19601959159543761000⟩, ⟨.privateRow 6 17, 11993151343768194600⟩, ⟨.privateRow 7 10, 782918487141540750⟩, ⟨.privateRow 7 11, 2131278103885305375⟩, ⟨.privateRow 7 12, 4009039745267635650⟩, ⟨.privateRow 7 13, 6170557557915550800⟩, ⟨.privateRow 7 14, 9760383806364541350⟩, ⟨.privateRow 8 8, 382760149269197700⟩, ⟨.privateRow 8 9, 1181143692946867650⟩, ⟨.privateRow 8 10, 2287861801313613525⟩, ⟨.privateRow 8 11, 3643677784601583300⟩, ⟨.privateRow 8 12, 1409253276854773350⟩, ⟨.privateRow 9 6, 189798421125222000⟩, ⟨.privateRow 9 7, 735363438292943460⟩, ⟨.privateRow 9 8, 1559393200726361000⟩, ⟨.privateRow 9 9, 780018789041016525⟩, ⟨.privateRow 10 4, 100909493898243030⟩, ⟨.privateRow 10 5, 516251705460603840⟩, ⟨.privateRow 10 6, 513594527564850732⟩, ⟨.privateRow 11 2, 64239465611613600⟩, ⟨.privateRow 11 3, 287070111951898275⟩, ⟨.privateRow 12 0, 54680021324171100⟩, ⟨.privateRow 12 1, 29443088405322900⟩, ⟨.hall 4 20, 4672656367701894000⟩, ⟨.hall 3 21, 49480448387345375400⟩, ⟨.hall 2 22, 140389766053693556400⟩, ⟨.assumptionRow 14, 47274677943902640⟩]
  caps := #[0, 10465064777936371680, 1129500867793026960, 0, 573125583810825045, 141147369633739755, 47907799411741500, 6279045510909600, 222442454637758355, 47274677943902640, 1504058695627950, 0, 1309730287123645200, 3954863918039070960, 781407798986097360] }

theorem case_39_25_14_checked :
    (Witness.linear .conditional case_39_25_14).check 39 25 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_25_15 : Certificate := {
  objectiveScale := 759586686239224800000
  eta := 397171133601744515952818880
  rows := #[⟨.count 2, 59875292092570685746535520⟩, ⟨.count 3, 9320210561579399196394680⟩, ⟨.count 4, 1428898013992290210969600⟩, ⟨.count 5, 198706130070802857462960⟩, ⟨.count 6, 20838096037387565576640⟩, ⟨.count 7, 1302381002336722848540⟩, ⟨.path 3, 263937152981049616019952⟩, ⟨.path 6, 14919600974886649401360⟩, ⟨.path 7, 759237324142400943840⟩, ⟨.privateRow 3 20, 1287992793168050481832320⟩, ⟨.privateRow 4 17, 195133885035822131935536⟩, ⟨.privateRow 4 18, 561791348079390663023790⟩, ⟨.privateRow 4 19, 804127241728473735912840⟩, ⟨.privateRow 5 14, 20540408951139171782688⟩, ⟨.privateRow 5 15, 112153609744082361871416⟩, ⟨.privateRow 5 16, 222372253427550164082144⟩, ⟨.privateRow 5 17, 356443074896670519033276⟩, ⟨.privateRow 5 18, 558163286715738363660000⟩, ⟨.privateRow 5 19, 254968989371749284519888⟩, ⟨.privateRow 6 11, 1130108382980013477040⟩, ⟨.privateRow 6 12, 16062699028819581798660⟩, ⟨.privateRow 6 13, 50323293151514188977600⟩, ⟨.privateRow 6 14, 97864629604159459761720⟩, ⟨.privateRow 6 16, 599281315503797756449620⟩, ⟨.privateRow 6 17, 161329862575171192222320⟩, ⟨.privateRow 6 18, 102826081041632689660920⟩, ⟨.privateRow 7 10, 5147505866378476020420⟩, ⟨.privateRow 7 11, 34559610169149467016615⟩, ⟨.privateRow 7 13, 158580391570238110653180⟩, ⟨.privateRow 7 16, 401753530149394791087720⟩, ⟨.privateRow 8 7, 101484233948316066120⟩, ⟨.privateRow 8 8, 2846632762250265654666⟩, ⟨.privateRow 8 9, 8930612587451813818560⟩, ⟨.privateRow 8 14, 284012085723858204042330⟩, ⟨.privateRow 9 6, 45104103977029362720⟩, ⟨.privateRow 9 7, 7417369899022478699304⟩, ⟨.privateRow 10 4, 37210885781049224244⟩, ⟨.privateRow 11 12, 2232653146862953454640⟩, ⟨.hall 11 2, 89960383206932190480⟩, ⟨.hall 10 3, 7360394989658088312⟩, ⟨.hall 12 4, 34348509951737745456⟩, ⟨.hall 8 6, 50572648580902387830⟩, ⟨.hall 9 6, 41207059828464600474⟩, ⟨.hall 10 6, 25203776782768605432⟩, ⟨.hall 11 6, 13630361091959422800⟩, ⟨.hall 4 15, 43516932250946921910⟩, ⟨.hall 3 18, 1835224099855581852846⟩, ⟨.hall 2 21, 193755464397324134585280⟩]
  caps := #[0, 0, 19666814404806913286448, 5879206971811870553472, 0, 1240952268331541024688, 155403530638291375440, 0, 70297791300278729964, 1864102147055248999392, 0, 728679103976150742888, 20509296280470813134880, 0, 33421814194525891200000] }

theorem case_39_25_15_checked :
    (Witness.linear .negative case_39_25_15).check 39 25 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_25_16 : Certificate := {
  objectiveScale := 366010005804300000
  eta := 278097714800659668915000
  rows := #[⟨.count 2, 32297567663264828324400⟩, ⟨.count 3, 3695832150869650591800⟩, ⟨.count 4, 423704895039243417600⟩, ⟨.count 5, 47997820141164293400⟩, ⟨.count 6, 3310194492494089200⟩, ⟨.path 3, 668152773262559665080⟩, ⟨.path 5, 8543043074786220000⟩, ⟨.path 6, 3660221275327617000⟩, ⟨.privateRow 5 14, 4019521883742822600⟩, ⟨.privateRow 6 12, 3126294798466639800⟩, ⟨.privateRow 7 9, 13792477052058705⟩, ⟨.privateRow 7 10, 30649949004574900⟩, ⟨.hall 10 6, 3472231985133660⟩, ⟨.hall 11 6, 12125254551260400⟩, ⟨.hall 12 6, 10609597732352850⟩, ⟨.hall 7 8, 9808992318206200⟩, ⟨.hall 8 8, 13079496954893460⟩, ⟨.hall 9 8, 15406421919222684⟩, ⟨.hall 10 9, 20006670009579660⟩, ⟨.hall 6 11, 5489107323515200⟩]
  caps := #[0, 26453962534113783240, 26400291220159342200, 907937919304553280, 855701797872893400, 441768173706030600, 350026782833527800, 22081892708378850, 122599796018299600, 0, 2038675732329951000, 0, 0, 3976698713063719500, 40261100638473000000] }

theorem case_39_25_16_checked :
    (Witness.linear .negative case_39_25_16).check 39 25 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_26_1_checked :
    (Witness.rising).check 39 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_26_2_checked :
    (Witness.rising).check 39 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_26_3_checked :
    (Witness.rising).check 39 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_26_4_checked :
    (Witness.rising).check 39 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_26_5_checked :
    (Witness.rising).check 39 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_26_6_checked :
    (Witness.rising).check 39 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_26_7_checked :
    (Witness.rising).check 39 26 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_26_8_checked :
    (Witness.rising).check 39 26 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_26_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_39_26_9_checked :
    (Witness.linear .positive case_39_26_9).check 39 26 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_26_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_39_26_10_checked :
    (Witness.linear .positive case_39_26_10).check 39 26 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_26_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_39_26_11_checked :
    (Witness.linear .positive case_39_26_11).check 39 26 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_26_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_39_26_12_checked :
    (Witness.linear .positive case_39_26_12).check 39 26 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_26_13 : Certificate := {
  objectiveScale := 2745022721641200000
  eta := 2293101802172607123297600
  rows := #[⟨.count 2, 302715654127466356576800⟩, ⟨.count 3, 38989210219148391602400⟩, ⟨.count 4, 4781484806245132265280⟩, ⟨.count 5, 595823651868552307200⟩, ⟨.count 7, 18619489120892259600⟩, ⟨.path 5, 304881078873967596000⟩, ⟨.path 6, 4844220214174941600⟩, ⟨.privateRow 2 24, 21505509934630559838000⟩, ⟨.privateRow 3 20, 2699825922529377642000⟩, ⟨.privateRow 3 21, 5871345569454692527200⟩, ⟨.privateRow 3 22, 7280220246268873503600⟩, ⟨.privateRow 4 17, 750365411571958061880⟩, ⟨.privateRow 4 18, 1863438471218897340768⟩, ⟨.privateRow 4 19, 2558317805210596469040⟩, ⟨.privateRow 4 20, 2997737748463653795600⟩, ⟨.privateRow 4 21, 3418538202595818862560⟩, ⟨.privateRow 5 14, 130336423846245817200⟩, ⟨.privateRow 5 15, 514252556672262408000⟩, ⟨.privateRow 5 16, 858979098110496242880⟩, ⟨.privateRow 5 17, 1123127583772221099072⟩, ⟨.privateRow 5 18, 1287227347891018213680⟩, ⟨.privateRow 5 19, 989729288381650776960⟩, ⟨.privateRow 6 2, 1143301963563559800⟩, ⟨.privateRow 6 11, 8689094923083054480⟩, ⟨.privateRow 6 12, 110337713308991168000⟩, ⟨.privateRow 6 13, 284335115116958880975⟩, ⟨.privateRow 6 14, 429134892119612078400⟩, ⟨.privateRow 6 15, 558584673626767788000⟩, ⟨.privateRow 6 16, 411490709571718937160⟩, ⟨.privateRow 7 9, 8947027239909267600⟩, ⟨.privateRow 7 10, 79531817816382651720⟩, ⟨.privateRow 7 11, 170826423998027397600⟩, ⟨.privateRow 7 12, 256682957166586150200⟩, ⟨.privateRow 7 13, 121216674072747567600⟩, ⟨.privateRow 8 7, 7240912435902545400⟩, ⟨.privateRow 8 8, 60936509850192849600⟩, ⟨.privateRow 8 9, 125060901928659676980⟩, ⟨.privateRow 8 10, 20343515891345246600⟩, ⟨.privateRow 9 5, 6874888290790988160⟩, ⟨.privateRow 9 6, 54617168087950628160⟩, ⟨.privateRow 9 7, 5867960207796348480⟩, ⟨.privateRow 10 3, 7979781051810968400⟩, ⟨.privateRow 10 4, 12031054508884229280⟩, ⟨.privateRow 11 1, 4965197098904602560⟩, ⟨.hall 3 22, 456582254964488452800⟩, ⟨.hall 2 23, 4642459287475803393600⟩, ⟨.assumptionRow 13, 2802199049457784704⟩]
  caps := #[0, 0, 598457482922145148848, 0, 40715896810968202824, 5536855282895864928, 3495855071403978192, 10847896296233877504, 19297518328663330028, 16726701894101519040, 0, 0, 174938161923421198848, 30138073610236615296] }

theorem case_39_26_13_checked :
    (Witness.linear .conditional case_39_26_13).check 39 26 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_26_14 : Certificate := {
  objectiveScale := 47786926572000000
  eta := 51144617365220290111200
  rows := #[⟨.count 2, 5993292573249033452400⟩, ⟨.count 3, 645976060942893080400⟩, ⟨.count 4, 59667456118404214080⟩, ⟨.count 5, 4213803398192388000⟩, ⟨.count 6, 842760679638477600⟩, ⟨.count 7, 210690169909619400⟩, ⟨.path 4, 20513970263289222720⟩, ⟨.path 5, 2683103321342644200⟩, ⟨.privateRow 2 24, 461200781932156866600⟩, ⟨.privateRow 3 20, 49617535013715368700⟩, ⟨.privateRow 3 21, 115458213110471431200⟩, ⟨.privateRow 3 22, 155278655223389497800⟩, ⟨.privateRow 4 17, 11524752294056181180⟩, ⟨.privateRow 4 18, 32892949326289780728⟩, ⟨.privateRow 4 19, 50154794946984898170⟩, ⟨.privateRow 4 20, 65356090705963937880⟩, ⟨.privateRow 4 21, 83686135488100825680⟩, ⟨.privateRow 5 14, 1432693155385411920⟩, ⟨.privateRow 5 15, 7624977577681464000⟩, ⟨.privateRow 5 16, 14898136014497976240⟩, ⟨.privateRow 5 17, 21934251288724110336⟩, ⟨.privateRow 5 18, 28541495017089774720⟩, ⟨.privateRow 5 19, 38673351187854583200⟩, ⟨.privateRow 5 20, 3904791148991612880⟩, ⟨.privateRow 6 12, 1166599274129188900⟩, ⟨.privateRow 6 13, 4099679556158010825⟩, ⟨.privateRow 6 14, 7238712266180495100⟩, ⟨.privateRow 6 15, 10756903674830012700⟩, ⟨.privateRow 6 16, 13982804276335074180⟩, ⟨.privateRow 6 17, 9955110528229516650⟩, ⟨.privateRow 7 10, 764504330814904680⟩, ⟨.privateRow 7 11, 2344346176295923800⟩, ⟨.privateRow 7 12, 4142319233401624275⟩, ⟨.privateRow 7 13, 6148713121852158000⟩, ⟨.privateRow 7 14, 4605085142310252600⟩, ⟨.privateRow 8 8, 517148598869065800⟩, ⟨.privateRow 8 9, 1576664771490318510⟩, ⟨.privateRow 8 10, 2887235661724414000⟩, ⟨.privateRow 8 11, 1676742602197387725⟩, ⟨.privateRow 9 6, 402652324716161520⟩, ⟨.privateRow 9 7, 1307555963560304640⟩, ⟨.privateRow 9 8, 640498116525242976⟩, ⟨.privateRow 10 4, 388966467525451200⟩, ⟨.privateRow 10 5, 389776814332795890⟩, ⟨.privateRow 11 2, 240788765610993600⟩, ⟨.hall 3 22, 20226256311323462400⟩, ⟨.hall 2 23, 108154287220271292000⟩, ⟨.assumptionRow 14, 32201459405175060⟩]
  caps := #[0, 23950733809372524000, 4545297450121843800, 0, 203349281898262500, 3823727072325160, 0, 132362157762947970, 113220370453875300, 244216901253238368, 970209249077216610, 0, 10566318579957520380, 2719732714317899280] }

theorem case_39_26_14_checked :
    (Witness.linear .conditional case_39_26_14).check 39 26 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_26_15 : Certificate := {
  objectiveScale := 15243228000000
  eta := 1199821011291302400
  rows := #[⟨.count 2, 99985084274275200⟩, ⟨.count 3, 7609858422566400⟩, ⟨.count 10, 951232302820800⟩, ⟨.count 11, 24414962439067200⟩, ⟨.count 12, 6975703554019200⟩, ⟨.path 3, 7700259222976320⟩, ⟨.privateRow 2 19, 7557012183520800⟩, ⟨.privateRow 2 20, 28949169749179680⟩, ⟨.privateRow 2 21, 60892078940292600⟩, ⟨.privateRow 2 22, 114324030468648000⟩, ⟨.privateRow 2 23, 188925304588020000⟩, ⟨.privateRow 2 24, 263332809164224800⟩, ⟨.privateRow 3 14, 95123230282080⟩, ⟨.privateRow 3 15, 3006363821260800⟩, ⟨.privateRow 3 16, 1255098177333000⟩, ⟨.privateRow 3 17, 9074454190401600⟩, ⟨.privateRow 3 18, 8578706138402400⟩, ⟨.privateRow 3 19, 28769492536424640⟩, ⟨.privateRow 3 20, 34904940889618800⟩, ⟨.privateRow 3 21, 75358736879025600⟩, ⟨.privateRow 3 22, 76679892855165600⟩, ⟨.privateRow 4 9, 18118710529920⟩, ⟨.privateRow 4 11, 517893142646880⟩, ⟨.privateRow 4 13, 2080027968834816⟩, ⟨.privateRow 4 14, 486185399219520⟩, ⟨.privateRow 4 15, 2687231255468760⟩, ⟨.privateRow 4 16, 5372197672121280⟩, ⟨.privateRow 4 17, 8423690503868640⟩, ⟨.privateRow 4 18, 17762677868007072⟩, ⟨.privateRow 4 19, 25730833791302640⟩, ⟨.privateRow 4 20, 33134591881591200⟩, ⟨.privateRow 4 21, 40189564794178800⟩, ⟨.privateRow 5 7, 47913923401344⟩, ⟨.privateRow 5 9, 638490970212480⟩, ⟨.privateRow 5 10, 187897738828800⟩, ⟨.privateRow 5 11, 176794690625280⟩, ⟨.privateRow 5 12, 670794927618816⟩, ⟨.privateRow 5 13, 1155571093797120⟩, ⟨.privateRow 5 14, 1920080018656800⟩, ⟨.privateRow 5 15, 4503506161714560⟩, ⟨.privateRow 5 16, 7337406701264640⟩, ⟨.privateRow 5 17, 10645346393345664⟩, ⟨.privateRow 5 18, 13951407108038400⟩, ⟨.privateRow 5 19, 18357609083573760⟩, ⟨.privateRow 6 3, 18104730043400⟩, ⟨.privateRow 6 4, 6217204593600⟩, ⟨.privateRow 6 5, 79819840225125⟩, ⟨.privateRow 6 6, 239569617006720⟩, ⟨.privateRow 6 9, 605529822397500⟩, ⟨.privateRow 6 10, 73664454427200⟩, ⟨.privateRow 6 11, 500277729631680⟩, ⟨.privateRow 6 12, 1169467697398000⟩, ⟨.privateRow 6 13, 2212936260034500⟩, ⟨.privateRow 6 14, 3487851777009600⟩, ⟨.privateRow 6 15, 5071770997293000⟩, ⟨.privateRow 6 16, 6716756982695760⟩, ⟨.privateRow 6 17, 3377755445664600⟩, ⟨.privateRow 7 0, 22270915026360⟩, ⟨.privateRow 7 4, 268949609428500⟩, ⟨.privateRow 7 6, 315459692262000⟩, ⟨.privateRow 7 8, 207610224822000⟩, ⟨.privateRow 7 10, 1309076835786720⟩, ⟨.privateRow 7 11, 988140787233600⟩, ⟨.privateRow 7 12, 1268309737094400⟩, ⟨.privateRow 7 13, 4305350740204800⟩, ⟨.privateRow 8 0, 96421208083200⟩, ⟨.privateRow 8 2, 299980121641200⟩, ⟨.privateRow 8 4, 210210595314720⟩, ⟨.privateRow 8 8, 1515726219898800⟩, ⟨.privateRow 8 9, 563693216486400⟩, ⟨.privateRow 8 10, 276953437961200⟩, ⟨.privateRow 9 0, 849454360955200⟩, ⟨.privateRow 10 0, 337594209432480⟩, ⟨.hall 3 22, 7527142570147200⟩, ⟨.hall 2 23, 52705315741478400⟩]
  caps := #[0, 6135849920360160, 103042396416960, 90400800409920, 0, 69967974685056, 0, 0, 6724397599920, 0, 181449898549920, 553445024932800, 2734232681980800, 3170591424000000] }

theorem case_39_26_15_checked :
    (Witness.linear .negative case_39_26_15).check 39 26 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_26_16 : Certificate := {
  objectiveScale := 87734977200000
  eta := 112692314033573274000
  rows := #[⟨.count 2, 15685713998070316200⟩, ⟨.count 3, 2052224249173698600⟩, ⟨.count 4, 238280582679179040⟩, ⟨.count 5, 21093213973431600⟩, ⟨.count 6, 1091028308970600⟩, ⟨.path 5, 11883362392301400⟩, ⟨.path 6, 861633938365200⟩, ⟨.privateRow 8 8, 8265365977050⟩, ⟨.hall 11 5, 3996440692200⟩, ⟨.hall 8 6, 1308638422740⟩, ⟨.hall 9 6, 211576271940⟩, ⟨.hall 10 7, 2479609793115⟩, ⟨.hall 7 9, 3409291229400⟩, ⟨.hall 9 9, 3406377978234⟩, ⟨.hall 6 10, 2923093230750⟩, ⟨.hall 8 10, 3557140913200⟩, ⟨.hall 10 10, 817453777950⟩, ⟨.hall 11 10, 1998220346100⟩, ⟨.hall 5 14, 9918926589000⟩, ⟨.hall 4 16, 28747827529200⟩]
  caps := #[0, 19136536885837800, 0, 674653027627800, 0, 180386763687000, 0, 0, 12740880887700, 0, 0, 9127228697762175, 0, 37638305218800000] }

theorem case_39_26_16_checked :
    (Witness.linear .negative case_39_26_16).check 39 26 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_27_1_checked :
    (Witness.rising).check 39 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_27_2_checked :
    (Witness.rising).check 39 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_27_3_checked :
    (Witness.rising).check 39 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_27_4_checked :
    (Witness.rising).check 39 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_27_5_checked :
    (Witness.rising).check 39 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_27_6_checked :
    (Witness.rising).check 39 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_27_7_checked :
    (Witness.rising).check 39 27 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_27_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_39_27_8_checked :
    (Witness.linear .positive case_39_27_8).check 39 27 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_27_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_39_27_9_checked :
    (Witness.linear .positive case_39_27_9).check 39 27 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_27_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_39_27_10_checked :
    (Witness.linear .positive case_39_27_10).check 39 27 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_27_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_39_27_11_checked :
    (Witness.linear .positive case_39_27_11).check 39 27 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_27_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_39_27_12_checked :
    (Witness.linear .positive case_39_27_12).check 39 27 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_27_13 : Certificate := {
  objectiveScale := 3
  eta := 148580
  rows := #[⟨.assumptionRow 13, 7⟩]
  caps := #[0, 0, 43758, 13104, 4004, 1287, 429, 150, 56, 816, 1292, 592, 172] }

theorem case_39_27_13_checked :
    (Witness.linear .conditional case_39_27_13).check 39 27 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_27_14 : Certificate := {
  objectiveScale := 765730329000000
  eta := 950997486179541200400
  rows := #[⟨.count 2, 120665819023573824000⟩, ⟨.count 3, 15302619776171407680⟩, ⟨.count 4, 1736856485945380800⟩, ⟨.count 5, 148546936297960200⟩, ⟨.count 6, 19588606984346400⟩, ⟨.count 7, 11426687407535400⟩, ⟨.path 5, 116286462437745600⟩, ⟨.privateRow 2 24, 4422128026716199800⟩, ⟨.privateRow 2 25, 11723781280131320400⟩, ⟨.privateRow 3 21, 2060231739578632620⟩, ⟨.privateRow 3 22, 3715958744930512080⟩, ⟨.privateRow 3 23, 3983343230266840440⟩, ⟨.privateRow 4 17, 58765820953039200⟩, ⟨.privateRow 4 18, 400695838424241360⟩, ⟨.privateRow 4 19, 1181976545435461776⟩, ⟨.privateRow 4 20, 1517464087720701120⟩, ⟨.privateRow 4 21, 1764280535723465760⟩, ⟨.privateRow 4 22, 1771136548167987000⟩, ⟨.privateRow 5 14, 13712024889042480⟩, ⟨.privateRow 5 15, 78272808741617490⟩, ⟨.privateRow 5 16, 287299569103747200⟩, ⟨.privateRow 5 17, 539339645635670880⟩, ⟨.privateRow 5 18, 701141539326372144⟩, ⟨.privateRow 5 19, 807295465342376010⟩, ⟨.privateRow 5 20, 337468168102545480⟩, ⟨.privateRow 6 12, 12569356148288940⟩, ⟨.privateRow 6 13, 66020860576871200⟩, ⟨.privateRow 6 14, 169971975187089075⟩, ⟨.privateRow 6 15, 278671254122547000⟩, ⟨.privateRow 6 16, 376536556476880800⟩, ⟨.privateRow 6 17, 165197252234654640⟩, ⟨.privateRow 7 10, 10981491794254800⟩, ⟨.privateRow 7 11, 51256854942373080⟩, ⟨.privateRow 7 12, 97943034921732000⟩, ⟨.privateRow 7 13, 209353237145202150⟩, ⟨.privateRow 7 14, 28450119667741200⟩, ⟨.privateRow 8 8, 10664908247033040⟩, ⟨.privateRow 8 9, 45914507583005880⟩, ⟨.privateRow 8 10, 85700155556515500⟩, ⟨.privateRow 9 6, 13008844125501840⟩, ⟨.privateRow 9 7, 35803620543610920⟩, ⟨.privateRow 10 4, 15670885587477120⟩, ⟨.privateRow 11 2, 4570674963014160⟩, ⟨.hall 2 24, 1980016393977734112⟩, ⟨.assumptionRow 14, 598803780687840⟩]
  caps := #[0, 21147846860103600, 6856935805629000, 13540311004675728, 2909718815159520, 4071187393409136, 0, 0, 2499706222471920, 15880275288623760, 0, 0, 214113274888094400] }

theorem case_39_27_14_checked :
    (Witness.linear .conditional case_39_27_14).check 39 27 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_27_15 : Certificate := {
  objectiveScale := 66571343586000000
  eta := 89738054760590874237600
  rows := #[⟨.count 2, 10579655885139567626400⟩, ⟨.count 3, 1125903306264205669200⟩, ⟨.count 4, 97888754607885521280⟩, ⟨.count 5, 5022277521859798200⟩, ⟨.path 4, 35071782616199609280⟩, ⟨.path 5, 4800590779642257600⟩, ⟨.privateRow 2 24, 1075223960361802251000⟩, ⟨.privateRow 2 25, 1460113046809784967600⟩, ⟨.privateRow 3 20, 72649527207121008144⟩, ⟨.privateRow 3 21, 231070423073931260820⟩, ⟨.privateRow 3 22, 485243322748417593360⟩, ⟨.privateRow 3 23, 476385851482592131080⟩, ⟨.privateRow 4 17, 24315650131809516480⟩, ⟨.privateRow 4 18, 48457368574550295360⟩, ⟨.privateRow 4 19, 127693688846704396416⟩, ⟨.privateRow 4 20, 177605996000314681800⟩, ⟨.privateRow 4 21, 216962388944343282240⟩, ⟨.privateRow 4 22, 241525891733075749800⟩, ⟨.privateRow 5 14, 5103445643425209080⟩, ⟨.privateRow 5 15, 11768109375085118055⟩, ⟨.privateRow 5 16, 31059851375449816920⟩, ⟨.privateRow 5 17, 56706078928635176040⟩, ⟨.privateRow 5 18, 78621471751296113640⟩, ⟨.privateRow 5 19, 97683297800173074990⟩, ⟨.privateRow 5 20, 72959995272108704760⟩, ⟨.privateRow 6 11, 818269537209742800⟩, ⟨.privateRow 6 12, 2732901664492539540⟩, ⟨.privateRow 6 13, 8442934073544971000⟩, ⟨.privateRow 6 14, 17463828655557934650⟩, ⟨.privateRow 6 15, 28866448539372272400⟩, ⟨.privateRow 6 16, 41037007889655277500⟩, ⟨.privateRow 6 17, 40517386968562423920⟩, ⟨.privateRow 7 8, 120414246278356800⟩, ⟨.privateRow 7 9, 548971893623203050⟩, ⟨.privateRow 7 10, 2407372696428663600⟩, ⟨.privateRow 7 11, 6144136916353155720⟩, ⟨.privateRow 7 12, 11501232939670273800⟩, ⟨.privateRow 7 13, 18270980400142545075⟩, ⟨.privateRow 7 14, 15141374718037425000⟩, ⟨.privateRow 8 5, 24350436469623264⟩, ⟨.privateRow 8 6, 117403890121397880⟩, ⟨.privateRow 8 7, 653247286060085640⟩, ⟨.privateRow 8 8, 2427434135565569130⟩, ⟨.privateRow 8 9, 3992918162007542040⟩, ⟨.privateRow 8 10, 12939213179046061908⟩, ⟨.privateRow 9 2, 10742839618951440⟩, ⟨.privateRow 9 3, 34242801285407715⟩, ⟨.privateRow 9 4, 206978709991797744⟩, ⟨.privateRow 9 5, 978365751011649000⟩, ⟨.privateRow 9 6, 3203018951004290880⟩, ⟨.privateRow 9 7, 2906833353561277140⟩, ⟨.privateRow 10 0, 30438045587029080⟩, ⟨.privateRow 10 1, 96685556570562960⟩, ⟨.privateRow 10 2, 479399217995708010⟩, ⟨.privateRow 10 3, 1899334044630614592⟩, ⟨.privateRow 11 0, 805712971421358000⟩, ⟨.hall 2 24, 247863092824295204256⟩, ⟨.assumptionRow 15, 21086708434100400⟩]
  caps := #[0, 17936038752757667400, 0, 303789935625523224, 0, 213867195825423140, 21086708434100400, 1000875005003455470, 545616627972935994, 26946622710869862, 0, 443334888581130000, 53199574711324860000] }

theorem case_39_27_15_checked :
    (Witness.linear .conditional case_39_27_15).check 39 27 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_27_16 : Certificate := {
  objectiveScale := 256353197100000
  eta := 409006849065322107600
  rows := #[⟨.count 2, 53659724065786238400⟩, ⟨.count 3, 6677756120963687760⟩, ⟨.count 4, 713025294230208960⟩, ⟨.count 5, 53324541235165200⟩, ⟨.path 5, 52293040117718400⟩, ⟨.privateRow 4 17, 9576652303458240⟩, ⟨.privateRow 6 11, 98932358506800⟩, ⟨.privateRow 6 12, 1251494335111020⟩, ⟨.privateRow 6 18, 464277191927599050⟩, ⟨.privateRow 7 10, 1038789764321400⟩, ⟨.privateRow 8 8, 126963193417060⟩, ⟨.privateRow 8 9, 2216084830552320⟩, ⟨.hall 8 6, 24146029707800⟩, ⟨.hall 9 6, 17481034387740⟩, ⟨.hall 10 6, 7386352558200⟩, ⟨.hall 7 8, 11133090692108⟩, ⟨.hall 6 9, 9672604540500⟩, ⟨.hall 10 10, 3525304630050⟩, ⟨.hall 5 11, 3891410678375⟩, ⟨.hall 4 15, 20214614833140⟩, ⟨.hall 3 18, 194819773714020⟩, ⟨.hall 2 22, 34505283887450376⟩]
  caps := #[0, 16506828849310800, 0, 0, 0, 2446186354411800, 0, 1359244577745600, 3735929603607292, 0, 0, 0, 419906536849800000] }

theorem case_39_27_16_checked :
    (Witness.linear .negative case_39_27_16).check 39 27 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_27_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 4862, 4862, 3432, 2002] }

theorem case_39_27_17_checked :
    (Witness.linear .negative case_39_27_17).check 39 27 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_28_1_checked :
    (Witness.rising).check 39 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_28_2_checked :
    (Witness.rising).check 39 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_28_3_checked :
    (Witness.rising).check 39 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_28_4_checked :
    (Witness.rising).check 39 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_28_5_checked :
    (Witness.rising).check 39 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_28_6_checked :
    (Witness.rising).check 39 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_28_7_checked :
    (Witness.rising).check 39 28 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_28_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_39_28_8_checked :
    (Witness.linear .positive case_39_28_8).check 39 28 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_28_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_39_28_9_checked :
    (Witness.linear .positive case_39_28_9).check 39 28 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_28_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_39_28_10_checked :
    (Witness.linear .positive case_39_28_10).check 39 28 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_28_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_39_28_11_checked :
    (Witness.linear .positive case_39_28_11).check 39 28 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_28_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_39_28_12_checked :
    (Witness.linear .positive case_39_28_12).check 39 28 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_28_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_39_28_13_checked :
    (Witness.linear .positive case_39_28_13).check 39 28 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_28_14 : Certificate := {
  objectiveScale := 2
  eta := 96900
  rows := #[⟨.assumptionRow 14, 3⟩]
  caps := #[0, 0, 29070, 9282, 3016, 1001, 341, 120, 7752, 7752, 4284, 1768] }

theorem case_39_28_14_checked :
    (Witness.linear .conditional case_39_28_14).check 39 28 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_28_15 : Certificate := {
  objectiveScale := 743
  eta := 25915582
  rows := #[⟨.assumptionRow 15, 770⟩]
  caps := #[0, 0, 8507820, 2783172, 909636, 324506, 121693, 45320, 6153150, 5341128, 3185868, 1520344] }

theorem case_39_28_15_checked :
    (Witness.linear .conditional case_39_28_15).check 39 28 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_28_16 : Certificate := {
  objectiveScale := 334
  eta := 2129862
  rows := #[⟨.assumptionRow 16, 217⟩]
  caps := #[0, 0, 775200, 329460, 132076, 51506, 23621, 9174, 3511010, 3368244, 2259708, 1240456] }

theorem case_39_28_16_checked :
    (Witness.linear .conditional case_39_28_16).check 39 28 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_28_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 16796, 16796, 11934, 7072] }

theorem case_39_28_17_checked :
    (Witness.linear .negative case_39_28_17).check 39 28 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_28_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4862, 4862] }

theorem case_39_28_18_checked :
    (Witness.linear .negative case_39_28_18).check 39 28 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_29_1_checked :
    (Witness.rising).check 39 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_29_2_checked :
    (Witness.rising).check 39 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_29_3_checked :
    (Witness.rising).check 39 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_29_4_checked :
    (Witness.rising).check 39 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_29_5_checked :
    (Witness.rising).check 39 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_29_6_checked :
    (Witness.rising).check 39 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_29_7_checked :
    (Witness.rising).check 39 29 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_29_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_39_29_8_checked :
    (Witness.linear .positive case_39_29_8).check 39 29 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_29_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_39_29_9_checked :
    (Witness.linear .positive case_39_29_9).check 39 29 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_29_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_39_29_10_checked :
    (Witness.linear .positive case_39_29_10).check 39 29 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_29_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_39_29_11_checked :
    (Witness.linear .positive case_39_29_11).check 39 29 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_29_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_39_29_12_checked :
    (Witness.linear .positive case_39_29_12).check 39 29 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_29_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_39_29_13_checked :
    (Witness.linear .positive case_39_29_13).check 39 29 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_29_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_39_29_14_checked :
    (Witness.linear .positive case_39_29_14).check 39 29 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_29_15 : Certificate := {
  objectiveScale := 495
  eta := 30768980
  rows := #[⟨.assumptionRow 15, 589⟩]
  caps := #[0, 0, 10100210, 3327546, 1102348, 368368, 124553, 42735, 6641526, 5488416, 3108552] }

theorem case_39_29_15_checked :
    (Witness.linear .conditional case_39_29_15).check 39 29 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_29_16 : Certificate := {
  objectiveScale := 829
  eta := 24334497
  rows := #[⟨.assumptionRow 16, 696⟩]
  caps := #[0, 0, 9286896, 3333360, 1150016, 421148, 168623, 63954, 14276600, 13188090, 8488440] }

theorem case_39_29_16_checked :
    (Witness.linear .conditional case_39_29_16).check 39 29 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_29_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 58786, 58786, 41990, 25194] }

theorem case_39_29_17_checked :
    (Witness.linear .negative case_39_29_17).check 39 29 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_29_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 16796, 16796] }

theorem case_39_29_18_checked :
    (Witness.linear .negative case_39_29_18).check 39 29 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_30_1_checked :
    (Witness.rising).check 39 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_30_2_checked :
    (Witness.rising).check 39 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_30_3_checked :
    (Witness.rising).check 39 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_30_4_checked :
    (Witness.rising).check 39 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_30_5_checked :
    (Witness.rising).check 39 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_30_6_checked :
    (Witness.rising).check 39 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_30_7_checked :
    (Witness.rising).check 39 30 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_30_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_39_30_8_checked :
    (Witness.linear .positive case_39_30_8).check 39 30 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_30_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_39_30_9_checked :
    (Witness.linear .positive case_39_30_9).check 39 30 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_30_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_39_30_10_checked :
    (Witness.linear .positive case_39_30_10).check 39 30 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_39_30_11_checked :
    (Witness.linear .positive case_39_30_11).check 39 30 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_30_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_39_30_12_checked :
    (Witness.linear .positive case_39_30_12).check 39 30 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_30_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_39_30_13_checked :
    (Witness.linear .positive case_39_30_13).check 39 30 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_30_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_39_30_14_checked :
    (Witness.linear .positive case_39_30_14).check 39 30 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_30_15 : Certificate := {
  objectiveScale := 2
  eta := 326876
  rows := #[⟨.assumptionRow 15, 3⟩]
  caps := #[0, 0, 96900, 29070, 9282, 3016, 1001, 341, 10659, 22287] }

theorem case_39_30_15_checked :
    (Witness.linear .conditional case_39_30_15).check 39 30 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_30_16 : Certificate := {
  objectiveScale := 983
  eta := 25677531
  rows := #[⟨.assumptionRow 16, 804⟩]
  caps := #[0, 0, 9155112, 3457392, 1231888, 422422, 178633, 58510804, 54652246, 35866566] }

theorem case_39_30_16_checked :
    (Witness.linear .conditional case_39_30_16).check 39 30 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_30_17 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 208012, 208012, 149226, 90440] }

theorem case_39_30_17_checked :
    (Witness.linear .negative case_39_30_17).check 39 30 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_30_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 58786, 58786] }

theorem case_39_30_18_checked :
    (Witness.linear .negative case_39_30_18).check 39 30 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_30_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_39_30_19_checked :
    (Witness.linear .negative case_39_30_19).check 39 30 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_31_1_checked :
    (Witness.rising).check 39 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_31_2_checked :
    (Witness.rising).check 39 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_31_3_checked :
    (Witness.rising).check 39 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_31_4_checked :
    (Witness.rising).check 39 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_31_5_checked :
    (Witness.rising).check 39 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_31_6_checked :
    (Witness.rising).check 39 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_31_7_checked :
    (Witness.rising).check 39 31 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_31_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1, 0] }

theorem case_39_31_8_checked :
    (Witness.linear .positive case_39_31_8).check 39 31 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_31_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1] }

theorem case_39_31_9_checked :
    (Witness.linear .positive case_39_31_9).check 39 31 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_31_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_39_31_10_checked :
    (Witness.linear .positive case_39_31_10).check 39 31 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_39_31_11_checked :
    (Witness.linear .positive case_39_31_11).check 39 31 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_39_31_12_checked :
    (Witness.linear .positive case_39_31_12).check 39 31 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_31_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_39_31_13_checked :
    (Witness.linear .positive case_39_31_13).check 39 31 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_31_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_39_31_14_checked :
    (Witness.linear .positive case_39_31_14).check 39 31 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_31_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_39_31_15_checked :
    (Witness.linear .positive case_39_31_15).check 39 31 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_31_16 : Certificate := {
  objectiveScale := 785
  eta := 56304391
  rows := #[⟨.assumptionRow 16, 761⟩]
  caps := #[0, 0, 18049240, 6443850, 2244000, 769860, 261716, 77878207, 70033183] }

theorem case_39_31_16_checked :
    (Witness.linear .conditional case_39_31_16).check 39 31 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_31_17 : Certificate := {
  objectiveScale := 5
  eta := 46398
  rows := #[⟨.assumptionRow 17, 3⟩]
  caps := #[0, 0, 16473, 7752, 2924, 1344, 148580, 713184, 653752] }

theorem case_39_31_17_checked :
    (Witness.linear .conditional case_39_31_17).check 39 31 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_31_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 208012, 208012] }

theorem case_39_31_18_checked :
    (Witness.linear .negative case_39_31_18).check 39 31 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_31_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_39_31_19_checked :
    (Witness.linear .negative case_39_31_19).check 39 31 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_31_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_39_31_20_checked :
    (Witness.linear .negative case_39_31_20).check 39 31 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_32_1_checked :
    (Witness.rising).check 39 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_32_2_checked :
    (Witness.rising).check 39 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_32_3_checked :
    (Witness.rising).check 39 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_32_4_checked :
    (Witness.rising).check 39 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_32_5_checked :
    (Witness.rising).check 39 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_32_6_checked :
    (Witness.rising).check 39 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_32_7_checked :
    (Witness.rising).check 39 32 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_32_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1, 1] }

theorem case_39_32_8_checked :
    (Witness.linear .positive case_39_32_8).check 39 32 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_32_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_39_32_9_checked :
    (Witness.linear .positive case_39_32_9).check 39 32 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_32_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_39_32_10_checked :
    (Witness.linear .positive case_39_32_10).check 39 32 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_39_32_11_checked :
    (Witness.linear .positive case_39_32_11).check 39 32 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_39_32_12_checked :
    (Witness.linear .positive case_39_32_12).check 39 32 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_32_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42] }

theorem case_39_32_13_checked :
    (Witness.linear .positive case_39_32_13).check 39 32 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_32_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_39_32_14_checked :
    (Witness.linear .positive case_39_32_14).check 39 32 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_32_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_39_32_15_checked :
    (Witness.linear .positive case_39_32_15).check 39 32 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_32_16 : Certificate := {
  objectiveScale := 7
  eta := 17866745
  rows := #[⟨.assumptionRow 16, 18⟩]
  caps := #[0, 0, 5051720, 1456084, 425068, 125970, 38012, 11726] }

theorem case_39_32_16_checked :
    (Witness.linear .conditional case_39_32_16).check 39 32 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_32_17 : Certificate := {
  objectiveScale := 993
  eta := 10672794
  rows := #[⟨.assumptionRow 17, 611⟩]
  caps := #[0, 0, 4214181, 1775208, 638588, 334305, 442805545, 431364885] }

theorem case_39_32_17_checked :
    (Witness.linear .conditional case_39_32_17).check 39 32 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_32_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 742900, 742900] }

theorem case_39_32_18_checked :
    (Witness.linear .negative case_39_32_18).check 39 32 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_32_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_39_32_19_checked :
    (Witness.linear .negative case_39_32_19).check 39 32 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_32_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_39_32_20_checked :
    (Witness.linear .negative case_39_32_20).check 39 32 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_33_1_checked :
    (Witness.rising).check 39 33 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_33_2_checked :
    (Witness.rising).check 39 33 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_33_3_checked :
    (Witness.rising).check 39 33 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_33_4_checked :
    (Witness.rising).check 39 33 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_33_5_checked :
    (Witness.rising).check 39 33 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_33_6_checked :
    (Witness.rising).check 39 33 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_33_7_checked :
    (Witness.rising).check 39 33 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_33_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2, 1] }

theorem case_39_33_8_checked :
    (Witness.linear .positive case_39_33_8).check 39 33 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_33_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_39_33_9_checked :
    (Witness.linear .positive case_39_33_9).check 39 33 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_33_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_39_33_10_checked :
    (Witness.linear .positive case_39_33_10).check 39 33 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_33_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_39_33_11_checked :
    (Witness.linear .positive case_39_33_11).check 39 33 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_33_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_39_33_12_checked :
    (Witness.linear .positive case_39_33_12).check 39 33 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_33_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_39_33_13_checked :
    (Witness.linear .positive case_39_33_13).check 39 33 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_33_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429] }

theorem case_39_33_14_checked :
    (Witness.linear .positive case_39_33_14).check 39 33 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_33_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430] }

theorem case_39_33_15_checked :
    (Witness.linear .positive case_39_33_15).check 39 33 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_33_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862] }

theorem case_39_33_16_checked :
    (Witness.linear .positive case_39_33_16).check 39 33 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_33_17 : Certificate := {
  objectiveScale := 413
  eta := 24530121
  rows := #[⟨.assumptionRow 17, 324⟩]
  caps := #[0, 0, 8729721, 2953512, 1131792, 432208, 303961905] }

theorem case_39_33_17_checked :
    (Witness.linear .conditional case_39_33_17).check 39 33 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_33_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 2674440, 2674440] }

theorem case_39_33_18_checked :
    (Witness.linear .negative case_39_33_18).check 39 33 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_33_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_39_33_19_checked :
    (Witness.linear .negative case_39_33_19).check 39 33 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_33_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_39_33_20_checked :
    (Witness.linear .negative case_39_33_20).check 39 33 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_33_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_39_33_21_checked :
    (Witness.linear .negative case_39_33_21).check 39 33 21 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_34_1_checked :
    (Witness.rising).check 39 34 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_34_2_checked :
    (Witness.rising).check 39 34 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_34_3_checked :
    (Witness.rising).check 39 34 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_34_4_checked :
    (Witness.rising).check 39 34 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_34_5_checked :
    (Witness.rising).check 39 34 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_34_6_checked :
    (Witness.rising).check 39 34 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_34_7_checked :
    (Witness.rising).check 39 34 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_34_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5, 2] }

theorem case_39_34_8_checked :
    (Witness.linear .positive case_39_34_8).check 39 34 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_34_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_39_34_9_checked :
    (Witness.linear .positive case_39_34_9).check 39 34 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_34_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_39_34_10_checked :
    (Witness.linear .positive case_39_34_10).check 39 34 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_34_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_39_34_11_checked :
    (Witness.linear .positive case_39_34_11).check 39 34 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_34_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_39_34_12_checked :
    (Witness.linear .positive case_39_34_12).check 39 34 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_34_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_39_34_13_checked :
    (Witness.linear .positive case_39_34_13).check 39 34 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_34_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_39_34_14_checked :
    (Witness.linear .positive case_39_34_14).check 39 34 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_34_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862] }

theorem case_39_34_15_checked :
    (Witness.linear .positive case_39_34_15).check 39 34 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_34_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796] }

theorem case_39_34_16_checked :
    (Witness.linear .positive case_39_34_16).check 39 34 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_34_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786] }

theorem case_39_34_17_checked :
    (Witness.linear .positive case_39_34_17).check 39 34 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_34_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 9694845, 9694845] }

theorem case_39_34_18_checked :
    (Witness.linear .negative case_39_34_18).check 39 34 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_34_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_39_34_19_checked :
    (Witness.linear .negative case_39_34_19).check 39 34 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_34_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_39_34_20_checked :
    (Witness.linear .negative case_39_34_20).check 39 34 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_34_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_39_34_21_checked :
    (Witness.linear .negative case_39_34_21).check 39 34 21 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_34_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_39_34_22_checked :
    (Witness.linear .negative case_39_34_22).check 39 34 22 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_35_1_checked :
    (Witness.rising).check 39 35 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_35_2_checked :
    (Witness.rising).check 39 35 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_35_3_checked :
    (Witness.rising).check 39 35 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_35_4_checked :
    (Witness.rising).check 39 35 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_35_5_checked :
    (Witness.rising).check 39 35 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_35_6_checked :
    (Witness.rising).check 39 35 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_35_7_checked :
    (Witness.rising).check 39 35 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_35_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14, 5] }

theorem case_39_35_8_checked :
    (Witness.linear .positive case_39_35_8).check 39 35 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_35_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_39_35_9_checked :
    (Witness.linear .positive case_39_35_9).check 39 35 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_35_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_39_35_10_checked :
    (Witness.linear .positive case_39_35_10).check 39 35 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_35_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_39_35_11_checked :
    (Witness.linear .positive case_39_35_11).check 39 35 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_35_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_39_35_12_checked :
    (Witness.linear .positive case_39_35_12).check 39 35 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_35_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_39_35_13_checked :
    (Witness.linear .positive case_39_35_13).check 39 35 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_35_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_39_35_14_checked :
    (Witness.linear .positive case_39_35_14).check 39 35 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_35_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796] }

theorem case_39_35_15_checked :
    (Witness.linear .positive case_39_35_15).check 39 35 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_35_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786] }

theorem case_39_35_16_checked :
    (Witness.linear .positive case_39_35_16).check 39 35 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_35_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012] }

theorem case_39_35_17_checked :
    (Witness.linear .positive case_39_35_17).check 39 35 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_35_18 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 35357670, 35357670] }

theorem case_39_35_18_checked :
    (Witness.linear .negative case_39_35_18).check 39 35 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_35_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_39_35_19_checked :
    (Witness.linear .negative case_39_35_19).check 39 35 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_35_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_39_35_20_checked :
    (Witness.linear .negative case_39_35_20).check 39 35 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_35_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_39_35_21_checked :
    (Witness.linear .negative case_39_35_21).check 39 35 21 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_35_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_39_35_22_checked :
    (Witness.linear .negative case_39_35_22).check 39 35 22 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_36_1_checked :
    (Witness.rising).check 39 36 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_36_2_checked :
    (Witness.rising).check 39 36 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_36_3_checked :
    (Witness.rising).check 39 36 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_36_4_checked :
    (Witness.rising).check 39 36 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_36_5_checked :
    (Witness.rising).check 39 36 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_36_6_checked :
    (Witness.rising).check 39 36 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_36_7_checked :
    (Witness.rising).check 39 36 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_36_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42, 14] }

theorem case_39_36_8_checked :
    (Witness.linear .positive case_39_36_8).check 39 36 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_36_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_39_36_9_checked :
    (Witness.linear .positive case_39_36_9).check 39 36 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_36_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_39_36_10_checked :
    (Witness.linear .positive case_39_36_10).check 39 36 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_36_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_39_36_11_checked :
    (Witness.linear .positive case_39_36_11).check 39 36 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_36_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_39_36_12_checked :
    (Witness.linear .positive case_39_36_12).check 39 36 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_36_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_39_36_13_checked :
    (Witness.linear .positive case_39_36_13).check 39 36 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_36_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_39_36_14_checked :
    (Witness.linear .positive case_39_36_14).check 39 36 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_36_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_39_36_15_checked :
    (Witness.linear .positive case_39_36_15).check 39 36 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_36_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012] }

theorem case_39_36_16_checked :
    (Witness.linear .positive case_39_36_16).check 39 36 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_36_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900] }

theorem case_39_36_17_checked :
    (Witness.linear .positive case_39_36_17).check 39 36 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_36_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440] }

theorem case_39_36_18_checked :
    (Witness.linear .positive case_39_36_18).check 39 36 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_36_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_39_36_19_checked :
    (Witness.linear .negative case_39_36_19).check 39 36 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_36_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_39_36_20_checked :
    (Witness.linear .negative case_39_36_20).check 39 36 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_36_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_39_36_21_checked :
    (Witness.linear .negative case_39_36_21).check 39 36 21 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_36_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_39_36_22_checked :
    (Witness.linear .negative case_39_36_22).check 39 36 22 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_36_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_39_36_23_checked :
    (Witness.linear .negative case_39_36_23).check 39 36 23 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_37_1_checked :
    (Witness.rising).check 39 37 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_37_2_checked :
    (Witness.rising).check 39 37 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_37_3_checked :
    (Witness.rising).check 39 37 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_37_4_checked :
    (Witness.rising).check 39 37 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_37_5_checked :
    (Witness.rising).check 39 37 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_37_6_checked :
    (Witness.rising).check 39 37 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_37_7_checked :
    (Witness.rising).check 39 37 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_37_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0, 42] }

theorem case_39_37_8_checked :
    (Witness.linear .positive case_39_37_8).check 39 37 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_37_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_39_37_9_checked :
    (Witness.linear .positive case_39_37_9).check 39 37 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_37_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_39_37_10_checked :
    (Witness.linear .positive case_39_37_10).check 39 37 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_37_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_39_37_11_checked :
    (Witness.linear .positive case_39_37_11).check 39 37 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_37_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_39_37_12_checked :
    (Witness.linear .positive case_39_37_12).check 39 37 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_37_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_39_37_13_checked :
    (Witness.linear .positive case_39_37_13).check 39 37 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_37_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_39_37_14_checked :
    (Witness.linear .positive case_39_37_14).check 39 37 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_37_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_39_37_15_checked :
    (Witness.linear .positive case_39_37_15).check 39 37 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_37_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900] }

theorem case_39_37_16_checked :
    (Witness.linear .positive case_39_37_16).check 39 37 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_37_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440] }

theorem case_39_37_17_checked :
    (Witness.linear .positive case_39_37_17).check 39 37 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_37_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845] }

theorem case_39_37_18_checked :
    (Witness.linear .positive case_39_37_18).check 39 37 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_37_19 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_39_37_19_checked :
    (Witness.linear .negative case_39_37_19).check 39 37 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_37_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_39_37_20_checked :
    (Witness.linear .negative case_39_37_20).check 39 37 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_37_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_39_37_21_checked :
    (Witness.linear .negative case_39_37_21).check 39 37 21 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_37_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_39_37_22_checked :
    (Witness.linear .negative case_39_37_22).check 39 37 22 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_37_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_39_37_23_checked :
    (Witness.linear .negative case_39_37_23).check 39 37 23 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_37_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_39_37_24_checked :
    (Witness.linear .negative case_39_37_24).check 39 37 24 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_38_1_checked :
    (Witness.rising).check 39 38 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_38_2_checked :
    (Witness.rising).check 39 38 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_38_3_checked :
    (Witness.rising).check 39 38 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_38_4_checked :
    (Witness.rising).check 39 38 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_38_5_checked :
    (Witness.rising).check 39 38 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_38_6_checked :
    (Witness.rising).check 39 38 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_39_38_7_checked :
    (Witness.rising).check 39 38 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_38_8 : Certificate := {
  objectiveScale := 1
  eta := 132
  rows := #[]
  caps := #[0, 0] }

theorem case_39_38_8_checked :
    (Witness.linear .positive case_39_38_8).check 39 38 8 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_38_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_39_38_9_checked :
    (Witness.linear .positive case_39_38_9).check 39 38 9 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_38_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_39_38_10_checked :
    (Witness.linear .positive case_39_38_10).check 39 38 10 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_38_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_39_38_11_checked :
    (Witness.linear .positive case_39_38_11).check 39 38 11 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_38_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_39_38_12_checked :
    (Witness.linear .positive case_39_38_12).check 39 38 12 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_38_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_39_38_13_checked :
    (Witness.linear .positive case_39_38_13).check 39 38 13 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_38_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_39_38_14_checked :
    (Witness.linear .positive case_39_38_14).check 39 38 14 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_38_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_39_38_15_checked :
    (Witness.linear .positive case_39_38_15).check 39 38 15 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_38_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_39_38_16_checked :
    (Witness.linear .positive case_39_38_16).check 39 38 16 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_38_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0] }

theorem case_39_38_17_checked :
    (Witness.linear .positive case_39_38_17).check 39 38 17 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_38_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0] }

theorem case_39_38_18_checked :
    (Witness.linear .positive case_39_38_18).check 39 38 18 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_38_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0] }

theorem case_39_38_19_checked :
    (Witness.linear .positive case_39_38_19).check 39 38 19 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_38_20 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_39_38_20_checked :
    (Witness.linear .negative case_39_38_20).check 39 38 20 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_38_21 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_39_38_21_checked :
    (Witness.linear .negative case_39_38_21).check 39 38 21 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_38_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_39_38_22_checked :
    (Witness.linear .negative case_39_38_22).check 39 38 22 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_38_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_39_38_23_checked :
    (Witness.linear .negative case_39_38_23).check 39 38 23 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_39_38_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_39_38_24_checked :
    (Witness.linear .negative case_39_38_24).check 39 38 24 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff_eq_kernelCoeff, kernelCoeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_39 (a k : ℕ) (h : Domain 39 a k) :
    ∃ w : Witness, w.check 39 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 20 ≤ a := by omega
  have haHi : a ≤ 38 := by omega
  interval_cases a

  · have hkHi : k ≤ 12 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_39_20_1_checked⟩

    · exact ⟨Witness.rising, case_39_20_2_checked⟩

    · exact ⟨Witness.rising, case_39_20_3_checked⟩

    · exact ⟨Witness.rising, case_39_20_4_checked⟩

    · exact ⟨Witness.rising, case_39_20_5_checked⟩

    · exact ⟨Witness.rising, case_39_20_6_checked⟩

    · exact ⟨Witness.rising, case_39_20_7_checked⟩

    · exact ⟨Witness.rising, case_39_20_8_checked⟩

    · exact ⟨Witness.linear .positive case_39_20_9, case_39_20_9_checked⟩

    · exact ⟨Witness.linear .positive case_39_20_10, case_39_20_10_checked⟩

    · exact ⟨Witness.linear .positive case_39_20_11, case_39_20_11_checked⟩

    · exact ⟨Witness.linear .conditional case_39_20_12, case_39_20_12_checked⟩

  · have hkHi : k ≤ 13 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_39_21_1_checked⟩

    · exact ⟨Witness.rising, case_39_21_2_checked⟩

    · exact ⟨Witness.rising, case_39_21_3_checked⟩

    · exact ⟨Witness.rising, case_39_21_4_checked⟩

    · exact ⟨Witness.rising, case_39_21_5_checked⟩

    · exact ⟨Witness.rising, case_39_21_6_checked⟩

    · exact ⟨Witness.rising, case_39_21_7_checked⟩

    · exact ⟨Witness.rising, case_39_21_8_checked⟩

    · exact ⟨Witness.linear .positive case_39_21_9, case_39_21_9_checked⟩

    · exact ⟨Witness.linear .positive case_39_21_10, case_39_21_10_checked⟩

    · exact ⟨Witness.linear .positive case_39_21_11, case_39_21_11_checked⟩

    · exact ⟨Witness.linear .conditional case_39_21_12, case_39_21_12_checked⟩

    · exact ⟨Witness.linear .conditional case_39_21_13, case_39_21_13_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_39_22_1_checked⟩

    · exact ⟨Witness.rising, case_39_22_2_checked⟩

    · exact ⟨Witness.rising, case_39_22_3_checked⟩

    · exact ⟨Witness.rising, case_39_22_4_checked⟩

    · exact ⟨Witness.rising, case_39_22_5_checked⟩

    · exact ⟨Witness.rising, case_39_22_6_checked⟩

    · exact ⟨Witness.rising, case_39_22_7_checked⟩

    · exact ⟨Witness.rising, case_39_22_8_checked⟩

    · exact ⟨Witness.linear .positive case_39_22_9, case_39_22_9_checked⟩

    · exact ⟨Witness.linear .positive case_39_22_10, case_39_22_10_checked⟩

    · exact ⟨Witness.linear .positive case_39_22_11, case_39_22_11_checked⟩

    · exact ⟨Witness.linear .conditional case_39_22_12, case_39_22_12_checked⟩

    · exact ⟨Witness.linear .conditional case_39_22_13, case_39_22_13_checked⟩

    · exact ⟨Witness.linear .negative case_39_22_14, case_39_22_14_checked⟩

  · have hkHi : k ≤ 14 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_39_23_1_checked⟩

    · exact ⟨Witness.rising, case_39_23_2_checked⟩

    · exact ⟨Witness.rising, case_39_23_3_checked⟩

    · exact ⟨Witness.rising, case_39_23_4_checked⟩

    · exact ⟨Witness.rising, case_39_23_5_checked⟩

    · exact ⟨Witness.rising, case_39_23_6_checked⟩

    · exact ⟨Witness.rising, case_39_23_7_checked⟩

    · exact ⟨Witness.rising, case_39_23_8_checked⟩

    · exact ⟨Witness.linear .positive case_39_23_9, case_39_23_9_checked⟩

    · exact ⟨Witness.linear .positive case_39_23_10, case_39_23_10_checked⟩

    · exact ⟨Witness.linear .positive case_39_23_11, case_39_23_11_checked⟩

    · exact ⟨Witness.linear .conditional case_39_23_12, case_39_23_12_checked⟩

    · exact ⟨Witness.linear .conditional case_39_23_13, case_39_23_13_checked⟩

    · exact ⟨Witness.linear .conditional case_39_23_14, case_39_23_14_checked⟩

  · have hkHi : k ≤ 15 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_39_24_1_checked⟩

    · exact ⟨Witness.rising, case_39_24_2_checked⟩

    · exact ⟨Witness.rising, case_39_24_3_checked⟩

    · exact ⟨Witness.rising, case_39_24_4_checked⟩

    · exact ⟨Witness.rising, case_39_24_5_checked⟩

    · exact ⟨Witness.rising, case_39_24_6_checked⟩

    · exact ⟨Witness.rising, case_39_24_7_checked⟩

    · exact ⟨Witness.rising, case_39_24_8_checked⟩

    · exact ⟨Witness.linear .positive case_39_24_9, case_39_24_9_checked⟩

    · exact ⟨Witness.linear .positive case_39_24_10, case_39_24_10_checked⟩

    · exact ⟨Witness.linear .positive case_39_24_11, case_39_24_11_checked⟩

    · exact ⟨Witness.linear .conditional case_39_24_12, case_39_24_12_checked⟩

    · exact ⟨Witness.linear .conditional case_39_24_13, case_39_24_13_checked⟩

    · exact ⟨Witness.linear .conditional case_39_24_14, case_39_24_14_checked⟩

    · exact ⟨Witness.linear .negative case_39_24_15, case_39_24_15_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_39_25_1_checked⟩

    · exact ⟨Witness.rising, case_39_25_2_checked⟩

    · exact ⟨Witness.rising, case_39_25_3_checked⟩

    · exact ⟨Witness.rising, case_39_25_4_checked⟩

    · exact ⟨Witness.rising, case_39_25_5_checked⟩

    · exact ⟨Witness.rising, case_39_25_6_checked⟩

    · exact ⟨Witness.rising, case_39_25_7_checked⟩

    · exact ⟨Witness.rising, case_39_25_8_checked⟩

    · exact ⟨Witness.linear .positive case_39_25_9, case_39_25_9_checked⟩

    · exact ⟨Witness.linear .positive case_39_25_10, case_39_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_39_25_11, case_39_25_11_checked⟩

    · exact ⟨Witness.linear .positive case_39_25_12, case_39_25_12_checked⟩

    · exact ⟨Witness.linear .conditional case_39_25_13, case_39_25_13_checked⟩

    · exact ⟨Witness.linear .conditional case_39_25_14, case_39_25_14_checked⟩

    · exact ⟨Witness.linear .negative case_39_25_15, case_39_25_15_checked⟩

    · exact ⟨Witness.linear .negative case_39_25_16, case_39_25_16_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_39_26_1_checked⟩

    · exact ⟨Witness.rising, case_39_26_2_checked⟩

    · exact ⟨Witness.rising, case_39_26_3_checked⟩

    · exact ⟨Witness.rising, case_39_26_4_checked⟩

    · exact ⟨Witness.rising, case_39_26_5_checked⟩

    · exact ⟨Witness.rising, case_39_26_6_checked⟩

    · exact ⟨Witness.rising, case_39_26_7_checked⟩

    · exact ⟨Witness.rising, case_39_26_8_checked⟩

    · exact ⟨Witness.linear .positive case_39_26_9, case_39_26_9_checked⟩

    · exact ⟨Witness.linear .positive case_39_26_10, case_39_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_39_26_11, case_39_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_39_26_12, case_39_26_12_checked⟩

    · exact ⟨Witness.linear .conditional case_39_26_13, case_39_26_13_checked⟩

    · exact ⟨Witness.linear .conditional case_39_26_14, case_39_26_14_checked⟩

    · exact ⟨Witness.linear .negative case_39_26_15, case_39_26_15_checked⟩

    · exact ⟨Witness.linear .negative case_39_26_16, case_39_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_39_27_1_checked⟩

    · exact ⟨Witness.rising, case_39_27_2_checked⟩

    · exact ⟨Witness.rising, case_39_27_3_checked⟩

    · exact ⟨Witness.rising, case_39_27_4_checked⟩

    · exact ⟨Witness.rising, case_39_27_5_checked⟩

    · exact ⟨Witness.rising, case_39_27_6_checked⟩

    · exact ⟨Witness.rising, case_39_27_7_checked⟩

    · exact ⟨Witness.linear .positive case_39_27_8, case_39_27_8_checked⟩

    · exact ⟨Witness.linear .positive case_39_27_9, case_39_27_9_checked⟩

    · exact ⟨Witness.linear .positive case_39_27_10, case_39_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_39_27_11, case_39_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_39_27_12, case_39_27_12_checked⟩

    · exact ⟨Witness.linear .conditional case_39_27_13, case_39_27_13_checked⟩

    · exact ⟨Witness.linear .conditional case_39_27_14, case_39_27_14_checked⟩

    · exact ⟨Witness.linear .conditional case_39_27_15, case_39_27_15_checked⟩

    · exact ⟨Witness.linear .negative case_39_27_16, case_39_27_16_checked⟩

    · exact ⟨Witness.linear .negative case_39_27_17, case_39_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_39_28_1_checked⟩

    · exact ⟨Witness.rising, case_39_28_2_checked⟩

    · exact ⟨Witness.rising, case_39_28_3_checked⟩

    · exact ⟨Witness.rising, case_39_28_4_checked⟩

    · exact ⟨Witness.rising, case_39_28_5_checked⟩

    · exact ⟨Witness.rising, case_39_28_6_checked⟩

    · exact ⟨Witness.rising, case_39_28_7_checked⟩

    · exact ⟨Witness.linear .positive case_39_28_8, case_39_28_8_checked⟩

    · exact ⟨Witness.linear .positive case_39_28_9, case_39_28_9_checked⟩

    · exact ⟨Witness.linear .positive case_39_28_10, case_39_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_39_28_11, case_39_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_39_28_12, case_39_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_39_28_13, case_39_28_13_checked⟩

    · exact ⟨Witness.linear .conditional case_39_28_14, case_39_28_14_checked⟩

    · exact ⟨Witness.linear .conditional case_39_28_15, case_39_28_15_checked⟩

    · exact ⟨Witness.linear .conditional case_39_28_16, case_39_28_16_checked⟩

    · exact ⟨Witness.linear .negative case_39_28_17, case_39_28_17_checked⟩

    · exact ⟨Witness.linear .negative case_39_28_18, case_39_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_39_29_1_checked⟩

    · exact ⟨Witness.rising, case_39_29_2_checked⟩

    · exact ⟨Witness.rising, case_39_29_3_checked⟩

    · exact ⟨Witness.rising, case_39_29_4_checked⟩

    · exact ⟨Witness.rising, case_39_29_5_checked⟩

    · exact ⟨Witness.rising, case_39_29_6_checked⟩

    · exact ⟨Witness.rising, case_39_29_7_checked⟩

    · exact ⟨Witness.linear .positive case_39_29_8, case_39_29_8_checked⟩

    · exact ⟨Witness.linear .positive case_39_29_9, case_39_29_9_checked⟩

    · exact ⟨Witness.linear .positive case_39_29_10, case_39_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_39_29_11, case_39_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_39_29_12, case_39_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_39_29_13, case_39_29_13_checked⟩

    · exact ⟨Witness.linear .positive case_39_29_14, case_39_29_14_checked⟩

    · exact ⟨Witness.linear .conditional case_39_29_15, case_39_29_15_checked⟩

    · exact ⟨Witness.linear .conditional case_39_29_16, case_39_29_16_checked⟩

    · exact ⟨Witness.linear .negative case_39_29_17, case_39_29_17_checked⟩

    · exact ⟨Witness.linear .negative case_39_29_18, case_39_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_39_30_1_checked⟩

    · exact ⟨Witness.rising, case_39_30_2_checked⟩

    · exact ⟨Witness.rising, case_39_30_3_checked⟩

    · exact ⟨Witness.rising, case_39_30_4_checked⟩

    · exact ⟨Witness.rising, case_39_30_5_checked⟩

    · exact ⟨Witness.rising, case_39_30_6_checked⟩

    · exact ⟨Witness.rising, case_39_30_7_checked⟩

    · exact ⟨Witness.linear .positive case_39_30_8, case_39_30_8_checked⟩

    · exact ⟨Witness.linear .positive case_39_30_9, case_39_30_9_checked⟩

    · exact ⟨Witness.linear .positive case_39_30_10, case_39_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_39_30_11, case_39_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_39_30_12, case_39_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_39_30_13, case_39_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_39_30_14, case_39_30_14_checked⟩

    · exact ⟨Witness.linear .conditional case_39_30_15, case_39_30_15_checked⟩

    · exact ⟨Witness.linear .conditional case_39_30_16, case_39_30_16_checked⟩

    · exact ⟨Witness.linear .negative case_39_30_17, case_39_30_17_checked⟩

    · exact ⟨Witness.linear .negative case_39_30_18, case_39_30_18_checked⟩

    · exact ⟨Witness.linear .negative case_39_30_19, case_39_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_39_31_1_checked⟩

    · exact ⟨Witness.rising, case_39_31_2_checked⟩

    · exact ⟨Witness.rising, case_39_31_3_checked⟩

    · exact ⟨Witness.rising, case_39_31_4_checked⟩

    · exact ⟨Witness.rising, case_39_31_5_checked⟩

    · exact ⟨Witness.rising, case_39_31_6_checked⟩

    · exact ⟨Witness.rising, case_39_31_7_checked⟩

    · exact ⟨Witness.linear .positive case_39_31_8, case_39_31_8_checked⟩

    · exact ⟨Witness.linear .positive case_39_31_9, case_39_31_9_checked⟩

    · exact ⟨Witness.linear .positive case_39_31_10, case_39_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_39_31_11, case_39_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_39_31_12, case_39_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_39_31_13, case_39_31_13_checked⟩

    · exact ⟨Witness.linear .positive case_39_31_14, case_39_31_14_checked⟩

    · exact ⟨Witness.linear .positive case_39_31_15, case_39_31_15_checked⟩

    · exact ⟨Witness.linear .conditional case_39_31_16, case_39_31_16_checked⟩

    · exact ⟨Witness.linear .conditional case_39_31_17, case_39_31_17_checked⟩

    · exact ⟨Witness.linear .negative case_39_31_18, case_39_31_18_checked⟩

    · exact ⟨Witness.linear .negative case_39_31_19, case_39_31_19_checked⟩

    · exact ⟨Witness.linear .negative case_39_31_20, case_39_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_39_32_1_checked⟩

    · exact ⟨Witness.rising, case_39_32_2_checked⟩

    · exact ⟨Witness.rising, case_39_32_3_checked⟩

    · exact ⟨Witness.rising, case_39_32_4_checked⟩

    · exact ⟨Witness.rising, case_39_32_5_checked⟩

    · exact ⟨Witness.rising, case_39_32_6_checked⟩

    · exact ⟨Witness.rising, case_39_32_7_checked⟩

    · exact ⟨Witness.linear .positive case_39_32_8, case_39_32_8_checked⟩

    · exact ⟨Witness.linear .positive case_39_32_9, case_39_32_9_checked⟩

    · exact ⟨Witness.linear .positive case_39_32_10, case_39_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_39_32_11, case_39_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_39_32_12, case_39_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_39_32_13, case_39_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_39_32_14, case_39_32_14_checked⟩

    · exact ⟨Witness.linear .positive case_39_32_15, case_39_32_15_checked⟩

    · exact ⟨Witness.linear .conditional case_39_32_16, case_39_32_16_checked⟩

    · exact ⟨Witness.linear .conditional case_39_32_17, case_39_32_17_checked⟩

    · exact ⟨Witness.linear .negative case_39_32_18, case_39_32_18_checked⟩

    · exact ⟨Witness.linear .negative case_39_32_19, case_39_32_19_checked⟩

    · exact ⟨Witness.linear .negative case_39_32_20, case_39_32_20_checked⟩

  · have hkHi : k ≤ 21 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_39_33_1_checked⟩

    · exact ⟨Witness.rising, case_39_33_2_checked⟩

    · exact ⟨Witness.rising, case_39_33_3_checked⟩

    · exact ⟨Witness.rising, case_39_33_4_checked⟩

    · exact ⟨Witness.rising, case_39_33_5_checked⟩

    · exact ⟨Witness.rising, case_39_33_6_checked⟩

    · exact ⟨Witness.rising, case_39_33_7_checked⟩

    · exact ⟨Witness.linear .positive case_39_33_8, case_39_33_8_checked⟩

    · exact ⟨Witness.linear .positive case_39_33_9, case_39_33_9_checked⟩

    · exact ⟨Witness.linear .positive case_39_33_10, case_39_33_10_checked⟩

    · exact ⟨Witness.linear .positive case_39_33_11, case_39_33_11_checked⟩

    · exact ⟨Witness.linear .positive case_39_33_12, case_39_33_12_checked⟩

    · exact ⟨Witness.linear .positive case_39_33_13, case_39_33_13_checked⟩

    · exact ⟨Witness.linear .positive case_39_33_14, case_39_33_14_checked⟩

    · exact ⟨Witness.linear .positive case_39_33_15, case_39_33_15_checked⟩

    · exact ⟨Witness.linear .positive case_39_33_16, case_39_33_16_checked⟩

    · exact ⟨Witness.linear .conditional case_39_33_17, case_39_33_17_checked⟩

    · exact ⟨Witness.linear .negative case_39_33_18, case_39_33_18_checked⟩

    · exact ⟨Witness.linear .negative case_39_33_19, case_39_33_19_checked⟩

    · exact ⟨Witness.linear .negative case_39_33_20, case_39_33_20_checked⟩

    · exact ⟨Witness.linear .negative case_39_33_21, case_39_33_21_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_39_34_1_checked⟩

    · exact ⟨Witness.rising, case_39_34_2_checked⟩

    · exact ⟨Witness.rising, case_39_34_3_checked⟩

    · exact ⟨Witness.rising, case_39_34_4_checked⟩

    · exact ⟨Witness.rising, case_39_34_5_checked⟩

    · exact ⟨Witness.rising, case_39_34_6_checked⟩

    · exact ⟨Witness.rising, case_39_34_7_checked⟩

    · exact ⟨Witness.linear .positive case_39_34_8, case_39_34_8_checked⟩

    · exact ⟨Witness.linear .positive case_39_34_9, case_39_34_9_checked⟩

    · exact ⟨Witness.linear .positive case_39_34_10, case_39_34_10_checked⟩

    · exact ⟨Witness.linear .positive case_39_34_11, case_39_34_11_checked⟩

    · exact ⟨Witness.linear .positive case_39_34_12, case_39_34_12_checked⟩

    · exact ⟨Witness.linear .positive case_39_34_13, case_39_34_13_checked⟩

    · exact ⟨Witness.linear .positive case_39_34_14, case_39_34_14_checked⟩

    · exact ⟨Witness.linear .positive case_39_34_15, case_39_34_15_checked⟩

    · exact ⟨Witness.linear .positive case_39_34_16, case_39_34_16_checked⟩

    · exact ⟨Witness.linear .positive case_39_34_17, case_39_34_17_checked⟩

    · exact ⟨Witness.linear .negative case_39_34_18, case_39_34_18_checked⟩

    · exact ⟨Witness.linear .negative case_39_34_19, case_39_34_19_checked⟩

    · exact ⟨Witness.linear .negative case_39_34_20, case_39_34_20_checked⟩

    · exact ⟨Witness.linear .negative case_39_34_21, case_39_34_21_checked⟩

    · exact ⟨Witness.linear .negative case_39_34_22, case_39_34_22_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_39_35_1_checked⟩

    · exact ⟨Witness.rising, case_39_35_2_checked⟩

    · exact ⟨Witness.rising, case_39_35_3_checked⟩

    · exact ⟨Witness.rising, case_39_35_4_checked⟩

    · exact ⟨Witness.rising, case_39_35_5_checked⟩

    · exact ⟨Witness.rising, case_39_35_6_checked⟩

    · exact ⟨Witness.rising, case_39_35_7_checked⟩

    · exact ⟨Witness.linear .positive case_39_35_8, case_39_35_8_checked⟩

    · exact ⟨Witness.linear .positive case_39_35_9, case_39_35_9_checked⟩

    · exact ⟨Witness.linear .positive case_39_35_10, case_39_35_10_checked⟩

    · exact ⟨Witness.linear .positive case_39_35_11, case_39_35_11_checked⟩

    · exact ⟨Witness.linear .positive case_39_35_12, case_39_35_12_checked⟩

    · exact ⟨Witness.linear .positive case_39_35_13, case_39_35_13_checked⟩

    · exact ⟨Witness.linear .positive case_39_35_14, case_39_35_14_checked⟩

    · exact ⟨Witness.linear .positive case_39_35_15, case_39_35_15_checked⟩

    · exact ⟨Witness.linear .positive case_39_35_16, case_39_35_16_checked⟩

    · exact ⟨Witness.linear .positive case_39_35_17, case_39_35_17_checked⟩

    · exact ⟨Witness.linear .negative case_39_35_18, case_39_35_18_checked⟩

    · exact ⟨Witness.linear .negative case_39_35_19, case_39_35_19_checked⟩

    · exact ⟨Witness.linear .negative case_39_35_20, case_39_35_20_checked⟩

    · exact ⟨Witness.linear .negative case_39_35_21, case_39_35_21_checked⟩

    · exact ⟨Witness.linear .negative case_39_35_22, case_39_35_22_checked⟩

  · have hkHi : k ≤ 23 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_39_36_1_checked⟩

    · exact ⟨Witness.rising, case_39_36_2_checked⟩

    · exact ⟨Witness.rising, case_39_36_3_checked⟩

    · exact ⟨Witness.rising, case_39_36_4_checked⟩

    · exact ⟨Witness.rising, case_39_36_5_checked⟩

    · exact ⟨Witness.rising, case_39_36_6_checked⟩

    · exact ⟨Witness.rising, case_39_36_7_checked⟩

    · exact ⟨Witness.linear .positive case_39_36_8, case_39_36_8_checked⟩

    · exact ⟨Witness.linear .positive case_39_36_9, case_39_36_9_checked⟩

    · exact ⟨Witness.linear .positive case_39_36_10, case_39_36_10_checked⟩

    · exact ⟨Witness.linear .positive case_39_36_11, case_39_36_11_checked⟩

    · exact ⟨Witness.linear .positive case_39_36_12, case_39_36_12_checked⟩

    · exact ⟨Witness.linear .positive case_39_36_13, case_39_36_13_checked⟩

    · exact ⟨Witness.linear .positive case_39_36_14, case_39_36_14_checked⟩

    · exact ⟨Witness.linear .positive case_39_36_15, case_39_36_15_checked⟩

    · exact ⟨Witness.linear .positive case_39_36_16, case_39_36_16_checked⟩

    · exact ⟨Witness.linear .positive case_39_36_17, case_39_36_17_checked⟩

    · exact ⟨Witness.linear .positive case_39_36_18, case_39_36_18_checked⟩

    · exact ⟨Witness.linear .negative case_39_36_19, case_39_36_19_checked⟩

    · exact ⟨Witness.linear .negative case_39_36_20, case_39_36_20_checked⟩

    · exact ⟨Witness.linear .negative case_39_36_21, case_39_36_21_checked⟩

    · exact ⟨Witness.linear .negative case_39_36_22, case_39_36_22_checked⟩

    · exact ⟨Witness.linear .negative case_39_36_23, case_39_36_23_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_39_37_1_checked⟩

    · exact ⟨Witness.rising, case_39_37_2_checked⟩

    · exact ⟨Witness.rising, case_39_37_3_checked⟩

    · exact ⟨Witness.rising, case_39_37_4_checked⟩

    · exact ⟨Witness.rising, case_39_37_5_checked⟩

    · exact ⟨Witness.rising, case_39_37_6_checked⟩

    · exact ⟨Witness.rising, case_39_37_7_checked⟩

    · exact ⟨Witness.linear .positive case_39_37_8, case_39_37_8_checked⟩

    · exact ⟨Witness.linear .positive case_39_37_9, case_39_37_9_checked⟩

    · exact ⟨Witness.linear .positive case_39_37_10, case_39_37_10_checked⟩

    · exact ⟨Witness.linear .positive case_39_37_11, case_39_37_11_checked⟩

    · exact ⟨Witness.linear .positive case_39_37_12, case_39_37_12_checked⟩

    · exact ⟨Witness.linear .positive case_39_37_13, case_39_37_13_checked⟩

    · exact ⟨Witness.linear .positive case_39_37_14, case_39_37_14_checked⟩

    · exact ⟨Witness.linear .positive case_39_37_15, case_39_37_15_checked⟩

    · exact ⟨Witness.linear .positive case_39_37_16, case_39_37_16_checked⟩

    · exact ⟨Witness.linear .positive case_39_37_17, case_39_37_17_checked⟩

    · exact ⟨Witness.linear .positive case_39_37_18, case_39_37_18_checked⟩

    · exact ⟨Witness.linear .negative case_39_37_19, case_39_37_19_checked⟩

    · exact ⟨Witness.linear .negative case_39_37_20, case_39_37_20_checked⟩

    · exact ⟨Witness.linear .negative case_39_37_21, case_39_37_21_checked⟩

    · exact ⟨Witness.linear .negative case_39_37_22, case_39_37_22_checked⟩

    · exact ⟨Witness.linear .negative case_39_37_23, case_39_37_23_checked⟩

    · exact ⟨Witness.linear .negative case_39_37_24, case_39_37_24_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_39_38_1_checked⟩

    · exact ⟨Witness.rising, case_39_38_2_checked⟩

    · exact ⟨Witness.rising, case_39_38_3_checked⟩

    · exact ⟨Witness.rising, case_39_38_4_checked⟩

    · exact ⟨Witness.rising, case_39_38_5_checked⟩

    · exact ⟨Witness.rising, case_39_38_6_checked⟩

    · exact ⟨Witness.rising, case_39_38_7_checked⟩

    · exact ⟨Witness.linear .positive case_39_38_8, case_39_38_8_checked⟩

    · exact ⟨Witness.linear .positive case_39_38_9, case_39_38_9_checked⟩

    · exact ⟨Witness.linear .positive case_39_38_10, case_39_38_10_checked⟩

    · exact ⟨Witness.linear .positive case_39_38_11, case_39_38_11_checked⟩

    · exact ⟨Witness.linear .positive case_39_38_12, case_39_38_12_checked⟩

    · exact ⟨Witness.linear .positive case_39_38_13, case_39_38_13_checked⟩

    · exact ⟨Witness.linear .positive case_39_38_14, case_39_38_14_checked⟩

    · exact ⟨Witness.linear .positive case_39_38_15, case_39_38_15_checked⟩

    · exact ⟨Witness.linear .positive case_39_38_16, case_39_38_16_checked⟩

    · exact ⟨Witness.linear .positive case_39_38_17, case_39_38_17_checked⟩

    · exact ⟨Witness.linear .positive case_39_38_18, case_39_38_18_checked⟩

    · exact ⟨Witness.linear .positive case_39_38_19, case_39_38_19_checked⟩

    · exact ⟨Witness.linear .negative case_39_38_20, case_39_38_20_checked⟩

    · exact ⟨Witness.linear .negative case_39_38_21, case_39_38_21_checked⟩

    · exact ⟨Witness.linear .negative case_39_38_22, case_39_38_22_checked⟩

    · exact ⟨Witness.linear .negative case_39_38_23, case_39_38_23_checked⟩

    · exact ⟨Witness.linear .negative case_39_38_24, case_39_38_24_checked⟩


#print axioms coverage_39
end ForestUnimodality.FiniteRows.FiniteData
