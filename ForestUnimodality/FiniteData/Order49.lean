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

theorem case_49_25_1_checked :
    (Witness.rising).check 49 25 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_25_2_checked :
    (Witness.rising).check 49 25 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_25_3_checked :
    (Witness.rising).check 49 25 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_25_4_checked :
    (Witness.rising).check 49 25 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_25_5_checked :
    (Witness.rising).check 49 25 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_25_6_checked :
    (Witness.rising).check 49 25 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_25_7_checked :
    (Witness.rising).check 49 25 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_25_8_checked :
    (Witness.rising).check 49 25 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_25_9_checked :
    (Witness.rising).check 49 25 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_25_10 : Certificate := {
  objectiveScale := 1807557785390011200000
  eta := 245674290149641016160456960
  rows := #[⟨.count 2, 55781119019483708983292160⟩, ⟨.count 3, 8496640469602209056932800⟩, ⟨.count 4, 1125178692573172355838720⟩, ⟨.count 5, 175327501753696377365280⟩, ⟨.count 6, 32246469379800721805760⟩, ⟨.count 7, 7334888737334126448480⟩, ⟨.count 8, 2449602310760543178240⟩, ⟨.count 9, 1816324440649152754320⟩, ⟨.count 11, 229650216633800922960⟩, ⟨.path 10, 623986970158299908160⟩, ⟨.path 11, 236033279517498503040⟩, ⟨.privateRow 10 0, 14875070850143923419⟩, ⟨.hall 8 3, 2538023784544680432⟩, ⟨.hall 7 5, 866700784276748960⟩, ⟨.hall 7 6, 98778398208011830⟩, ⟨.hall 6 8, 447132715333318560⟩, ⟨.hall 6 9, 20417353122421584⟩, ⟨.hall 5 13, 1636808130305847642⟩, ⟨.hall 9 15, 11743476986955729015⟩, ⟨.hall 8 16, 39298432792949890560⟩, ⟨.hall 4 18, 281999672324103347328⟩]
  caps := #[0, 0, 0, 0, 2656399462482301885440, 1155838327964980271040, 500426166712536123696, 322493425117941080640, 0, 0, 8635037292830625222, 6383062883697580080, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_25_10_checked :
    (Witness.linear .positive case_49_25_10).check 49 25 10 = true := by
  change case_49_25_10.check 49 25 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_25_11 : Certificate := {
  objectiveScale := 4662362905200000
  eta := 1013469667105103208000
  rows := #[⟨.count 2, 259095723590348124480⟩, ⟨.count 3, 45185525078836222080⟩, ⟨.count 4, 6867101075810976000⟩, ⟨.count 5, 1201742688266920800⟩, ⟨.count 6, 231312878343106560⟩, ⟨.count 7, 52005239141375520⟩, ⟨.count 8, 13890111567171840⟩, ⟨.count 9, 5580848397524400⟩, ⟨.count 10, 4712716424576160⟩, ⟨.path 11, 954248308453440⟩, ⟨.path 12, 876257805440160⟩, ⟨.privateRow 7 11, 1003962145586400⟩, ⟨.privateRow 8 7, 7516294138080⟩, ⟨.privateRow 9 4, 3179970596880⟩, ⟨.privateRow 9 5, 299712228755940⟩, ⟨.privateRow 9 6, 150325882761600⟩, ⟨.privateRow 10 2, 116932061662416⟩, ⟨.privateRow 11 0, 126381117150288⟩, ⟨.privateRow 12 0, 62106772677840⟩, ⟨.hall 9 3, 9863587369251⟩, ⟨.hall 9 4, 221462237997⟩, ⟨.hall 8 5, 4391387967120⟩, ⟨.hall 7 6, 3590085852430⟩, ⟨.hall 7 7, 1525743468200⟩, ⟨.hall 6 10, 3921166751040⟩, ⟨.hall 10 14, 33071694207552⟩, ⟨.hall 5 15, 81645745074894⟩, ⟨.hall 4 19, 16132237447936896⟩]
  caps := #[0, 0, 0, 76847205989473920, 37034859423481920, 4156502184188640, 2558969096379696, 113215958492560, 1480025098741280, 35762816129040, 193266527652198, 0, 6762987950400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_25_11_checked :
    (Witness.linear .positive case_49_25_11).check 49 25 11 = true := by
  change case_49_25_11.check 49 25 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_25_12 : Certificate := {
  objectiveScale := 2986483500000
  eta := 856916945363278800
  rows := #[⟨.count 2, 243865691961091200⟩, ⟨.count 3, 47726240219658000⟩, ⟨.count 4, 8504214847128000⟩, ⟨.count 5, 1642193211859200⟩, ⟨.count 6, 347268301380000⟩, ⟨.count 7, 82829920773600⟩, ⟨.count 8, 21184122960000⟩, ⟨.count 9, 7149641499000⟩, ⟨.count 10, 3177618444000⟩, ⟨.count 11, 2996040247200⟩, ⟨.path 12, 107854718400⟩, ⟨.path 13, 811496485800⟩, ⟨.privateRow 9 6, 9629146800⟩, ⟨.privateRow 9 7, 217137260340⟩, ⟨.privateRow 10 4, 137696799240⟩, ⟨.privateRow 10 5, 268653195720⟩, ⟨.privateRow 10 6, 69907605768⟩, ⟨.privateRow 11 2, 109994484600⟩, ⟨.privateRow 12 0, 108373250700⟩, ⟨.privateRow 13 0, 62048170800⟩, ⟨.privateRow 14 0, 68091823800⟩, ⟨.privateRow 15 3, 43692253605⟩, ⟨.privateRow 15 5, 116512676280⟩, ⟨.privateRow 16 4, 247148101200⟩, ⟨.hall 10 3, 9777287520⟩, ⟨.hall 9 5, 4444221600⟩, ⟨.hall 8 6, 6797044800⟩, ⟨.hall 7 8, 4440106580⟩, ⟨.hall 7 9, 1427911940⟩, ⟨.hall 6 12, 11749023000⟩, ⟨.hall 6 13, 8276825700⟩, ⟨.hall 11 13, 35667145800⟩, ⟨.hall 5 16, 456971795280⟩, ⟨.hall 4 19, 20248130588400⟩]
  caps := #[0, 9282867549555600, 523989281415600, 125016588496800, 29556971215200, 18116748421200, 961096336200, 893555863200, 575351576800, 697045887720, 0, 0, 0, 58054411800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_25_12_checked :
    (Witness.linear .positive case_49_25_12).check 49 25 12 = true := by
  change case_49_25_12.check 49 25 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_25_13 : Certificate := {
  objectiveScale := 3602742000000
  eta := 1402227728776274400
  rows := #[⟨.count 2, 433539007930828800⟩, ⟨.count 3, 96068302893763200⟩, ⟨.count 4, 19589019027177600⟩, ⟨.count 5, 4340082059913600⟩, ⟨.count 6, 1009393196011200⟩, ⟨.count 7, 255692364127200⟩, ⟨.count 8, 69483923308800⟩, ⟨.count 9, 21925567263600⟩, ⟨.count 10, 7626284265600⟩, ⟨.count 11, 3495380288400⟩, ⟨.count 12, 3687434150400⟩, ⟨.path 14, 613683220150⟩, ⟨.path 15, 310107907200⟩, ⟨.privateRow 8 11, 1482888607200⟩, ⟨.privateRow 9 8, 376606630400⟩, ⟨.privateRow 10 6, 482998003488⟩, ⟨.privateRow 10 7, 1172188137120⟩, ⟨.privateRow 10 8, 802348657110⟩, ⟨.privateRow 11 4, 342522507600⟩, ⟨.privateRow 11 5, 236051655840⟩, ⟨.privateRow 12 2, 6401795400⟩, ⟨.privateRow 13 0, 180235162800⟩, ⟨.privateRow 14 0, 52960307400⟩, ⟨.privateRow 15 0, 28887440400⟩, ⟨.hall 11 3, 34544753100⟩, ⟨.hall 10 5, 15068027520⟩, ⟨.hall 9 7, 13101194925⟩, ⟨.hall 8 8, 18489511040⟩, ⟨.hall 8 9, 1054413360⟩, ⟨.hall 12 10, 2686068000⟩, ⟨.hall 7 11, 41094353300⟩, ⟨.hall 12 11, 2954674800⟩, ⟨.hall 11 13, 107001437400⟩, ⟨.hall 6 14, 287658090720⟩, ⟨.hall 5 17, 6782450034360⟩, ⟨.hall 4 20, 932810429865600⟩]
  caps := #[0, 0, 1578917057818100, 0, 28730693829500, 11877039460000, 2144261969850, 189542152800, 802365964400, 713159246800, 215237120462, 252818598760, 0, 156842921400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_25_13_checked :
    (Witness.linear .positive case_49_25_13).check 49 25 13 = true := by
  change case_49_25_13.check 49 25 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_25_14 : Certificate := {
  objectiveScale := 479278800000
  eta := 259671801625236000
  rows := #[⟨.count 2, 84901389053120640⟩, ⟨.count 3, 20075812014978720⟩, ⟨.count 4, 4574681090179200⟩, ⟨.count 5, 1137805296788160⟩, ⟨.count 6, 296335617177600⟩, ⟨.count 7, 78508359689760⟩, ⟨.count 8, 24404109649920⟩, ⟨.count 9, 8198255585520⟩, ⟨.count 10, 3050513706240⟩, ⟨.count 11, 1398152115360⟩, ⟨.count 12, 829672683840⟩, ⟨.count 13, 898812074160⟩, ⟨.path 14, 136655699180⟩, ⟨.privateRow 4 21, 93839612106240⟩, ⟨.privateRow 10 7, 97446965616⟩, ⟨.privateRow 11 5, 69907605768⟩, ⟨.privateRow 11 6, 258244546560⟩, ⟨.privateRow 11 7, 90789098400⟩, ⟨.privateRow 12 3, 35617261680⟩, ⟨.privateRow 12 4, 30728617920⟩, ⟨.privateRow 13 1, 16004488500⟩, ⟨.privateRow 14 0, 55986610680⟩, ⟨.privateRow 15 0, 43908909408⟩, ⟨.privateRow 16 6, 169472983680⟩, ⟨.hall 12 2, 13752668160⟩, ⟨.hall 12 3, 3739006656⟩, ⟨.hall 11 4, 8280763920⟩, ⟨.hall 10 6, 5310492096⟩, ⟨.hall 9 7, 7201490751⟩, ⟨.hall 9 8, 183324141⟩, ⟨.hall 8 9, 8079769152⟩, ⟨.hall 8 10, 1369368000⟩, ⟨.hall 13 11, 16644668040⟩, ⟨.hall 7 12, 21436314900⟩, ⟨.hall 7 13, 24580307752⟩, ⟨.hall 6 15, 368532063900⟩, ⟨.hall 5 17, 2219087318448⟩, ⟨.hall 4 20, 318384398217600⟩, ⟨.assumptionRow 14, 854100383136⟩]
  caps := #[0, 2743152071211552, 172033637175400, 0, 9058129224144, 2014608115520, 1074640294728, 392463751680, 6440926128, 0, 0, 0, 92869559640, 18981266304, 36856740284, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_25_14_checked :
    (Witness.linear .conditional case_49_25_14).check 49 25 14 = true := by
  change case_49_25_14.check 49 25 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_25_15 : Certificate := {
  objectiveScale := 277763850000
  eta := 36354052227533040
  rows := #[⟨.count 2, 9935268931748160⟩, ⟨.count 3, 2771201045012400⟩, ⟨.count 4, 809366654416320⟩, ⟨.count 5, 246328981778880⟩, ⟨.count 6, 78714148312800⟩, ⟨.count 7, 26649626683680⟩, ⟨.count 8, 9659960069760⟩, ⟨.count 9, 3717813579480⟩, ⟨.count 10, 1525256853120⟩, ⟨.count 11, 649142053560⟩, ⟨.count 12, 322650488160⟩, ⟨.count 13, 299604024720⟩, ⟨.count 14, 254209475520⟩, ⟨.path 13, 30103753680⟩, ⟨.privateRow 3 22, 328438642371840⟩, ⟨.privateRow 12 4, 11139123996⟩, ⟨.privateRow 12 5, 22619677080⟩, ⟨.privateRow 13 3, 49165788672⟩, ⟨.privateRow 13 4, 8108940840⟩, ⟨.privateRow 14 1, 20221208280⟩, ⟨.privateRow 15 0, 30620686824⟩, ⟨.privateRow 16 0, 27539359848⟩, ⟨.hall 13 2, 5447345904⟩, ⟨.hall 13 3, 2521919400⟩, ⟨.hall 12 4, 5164413408⟩, ⟨.hall 11 5, 6676158060⟩, ⟨.hall 10 6, 4784239824⟩, ⟨.hall 10 7, 2250504438⟩, ⟨.hall 9 8, 7238525931⟩, ⟨.hall 9 9, 371409948⟩, ⟨.hall 8 10, 9993896640⟩, ⟨.hall 14 10, 5777488080⟩, ⟨.hall 8 11, 3466783320⟩, ⟨.hall 7 13, 71025656702⟩, ⟨.hall 6 15, 332634532230⟩, ⟨.hall 5 17, 2277394094976⟩, ⟨.hall 4 19, 24130185970176⟩, ⟨.hall 3 21, 461866840835400⟩, ⟨.assumptionRow 15, 253514521260⟩]
  caps := #[0, 0, 0, 0, 0, 107751047040, 683339280624, 74995780860, 0, 18527909400, 12687820236, 29929952052, 0, 0, 0, 14516483436, 2370251520, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_25_15_checked :
    (Witness.linear .conditional case_49_25_15).check 49 25 15 = true := by
  change case_49_25_15.check 49 25 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_25_16 : Certificate := {
  objectiveScale := 6814473120000
  eta := 796326858317390400
  rows := #[⟨.count 2, 221586604053534720⟩, ⟨.count 3, 63265493486875680⟩, ⟨.count 4, 18705362679843840⟩, ⟨.count 5, 5845425837451200⟩, ⟨.count 6, 1888522193638080⟩, ⟨.count 7, 623985403161120⟩, ⟨.count 8, 213084031480320⟩, ⟨.count 9, 73085224212000⟩, ⟨.count 10, 24361741404000⟩, ⟨.count 11, 10719166217760⟩, ⟨.count 12, 4240549272960⟩, ⟨.count 13, 3062618919360⟩, ⟨.count 14, 2923408968480⟩, ⟨.count 15, 2923408968480⟩, ⟨.count 17, 5521994718240⟩, ⟨.path 12, 1049308088400⟩, ⟨.path 13, 61996334400⟩, ⟨.privateRow 3 22, 5036059183034880⟩, ⟨.privateRow 12 5, 497348371520⟩, ⟨.privateRow 16 0, 341064379656⟩, ⟨.hall 14 2, 250015447136⟩, ⟨.hall 13 3, 192187071076⟩, ⟨.hall 14 3, 40602902340⟩, ⟨.hall 12 4, 113784228096⟩, ⟨.hall 13 4, 76565472984⟩, ⟨.hall 12 5, 134198941800⟩, ⟨.hall 11 6, 229817526510⟩, ⟨.hall 10 7, 151981679668⟩, ⟨.hall 10 8, 115218678848⟩, ⟨.hall 9 9, 309224970873⟩, ⟨.hall 15 9, 146170448424⟩, ⟨.hall 9 10, 55337172345⟩, ⟨.hall 8 11, 711342551920⟩, ⟨.hall 7 13, 2182889368660⟩, ⟨.hall 6 15, 9798732003060⟩, ⟨.hall 5 17, 65461932624088⟩, ⟨.hall 4 19, 691601665017120⟩, ⟨.hall 3 20, 643814384194800⟩, ⟨.hall 3 21, 343367671570560⟩, ⟨.hall 2 22, 5118168843627840⟩, ⟨.assumptionRow 16, 2864208233250⟩]
  caps := #[0, 0, 0, 360027337346820, 134139374443620, 18991976842800, 4883738185872, 4260862465860, 1361062202500, 0, 271530139244, 0, 16518377590, 0, 312330018000, 117123756750, 498734251470, 1292478401760, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_25_16_checked :
    (Witness.linear .conditional case_49_25_16).check 49 25 16 = true := by
  change case_49_25_16.check 49 25 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_26_1_checked :
    (Witness.rising).check 49 26 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_26_2_checked :
    (Witness.rising).check 49 26 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_26_3_checked :
    (Witness.rising).check 49 26 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_26_4_checked :
    (Witness.rising).check 49 26 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_26_5_checked :
    (Witness.rising).check 49 26 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_26_6_checked :
    (Witness.rising).check 49 26 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_26_7_checked :
    (Witness.rising).check 49 26 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_26_8_checked :
    (Witness.rising).check 49 26 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_26_9_checked :
    (Witness.rising).check 49 26 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_26_10 : Certificate := {
  objectiveScale := 502453666000000
  eta := 89750043462731652000
  rows := #[⟨.count 2, 18717923502922644000⟩, ⟨.count 3, 2536861427136036000⟩, ⟨.count 4, 340076558880938880⟩, ⟨.count 5, 52685884546495200⟩, ⟨.count 6, 9622992611232000⟩, ⟨.count 7, 2080264579192800⟩, ⟨.count 8, 693421526397600⟩, ⟨.count 9, 505207112089680⟩, ⟨.count 11, 53884404327600⟩, ⟨.path 10, 181776070476000⟩, ⟨.path 11, 61726432868100⟩, ⟨.privateRow 4 22, 8227658682603360⟩, ⟨.privateRow 6 14, 1145594358480000⟩, ⟨.privateRow 6 15, 153700576429400⟩, ⟨.privateRow 7 9, 63038320581600⟩, ⟨.privateRow 7 10, 107551093890240⟩, ⟨.privateRow 7 11, 117928831020000⟩, ⟨.privateRow 7 12, 222885490627800⟩, ⟨.privateRow 7 13, 353786493060000⟩, ⟨.privateRow 8 5, 4864564279575⟩, ⟨.privateRow 8 6, 30003816046050⟩, ⟨.privateRow 8 7, 50561986299825⟩, ⟨.privateRow 8 8, 59098425545250⟩, ⟨.privateRow 8 9, 53244867205530⟩, ⟨.privateRow 9 3, 25755656694768⟩, ⟨.privateRow 9 4, 5660583888960⟩, ⟨.privateRow 10 0, 4120572095640⟩, ⟨.hall 5 13, 109505343090⟩, ⟨.hall 4 18, 17715054579768⟩, ⟨.hall 6 19, 553322075145840⟩]
  caps := #[0, 323864327505004000, 41786137481774400, 1335541309245000, 2008452109503840, 0, 7441149515800, 46718021821900, 44572978128810, 0, 3533222967560, 7842028540500, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_26_10_checked :
    (Witness.linear .positive case_49_26_10).check 49 26 10 = true := by
  change case_49_26_10.check 49 26 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_26_11 : Certificate := {
  objectiveScale := 2059200000
  eta := 602818662045600
  rows := #[⟨.count 2, 138397504845600⟩, ⟨.count 3, 21097989712800⟩, ⟨.count 4, 3290755628160⟩, ⟨.count 5, 572669697600⟩, ⟨.count 6, 109412503200⟩, ⟨.count 7, 23963940000⟩, ⟨.count 8, 6230624400⟩, ⟨.count 9, 2588105520⟩, ⟨.count 10, 2054052000⟩, ⟨.path 11, 458300700⟩, ⟨.path 12, 365645280⟩, ⟨.privateRow 4 22, 119422583280⟩, ⟨.privateRow 6 14, 2494206000⟩, ⟨.privateRow 6 15, 6595789200⟩, ⟨.privateRow 7 11, 1156355200⟩, ⟨.privateRow 7 12, 2071169100⟩, ⟨.privateRow 7 13, 2875672800⟩, ⟨.privateRow 7 14, 3560356800⟩, ⟨.privateRow 8 8, 397583550⟩, ⟨.privateRow 8 9, 706936230⟩, ⟨.privateRow 8 10, 998497500⟩, ⟨.privateRow 8 11, 1168242075⟩, ⟨.privateRow 8 12, 1223872650⟩, ⟨.privateRow 8 13, 489263775⟩, ⟨.privateRow 9 5, 137639040⟩, ⟨.privateRow 9 6, 258278020⟩, ⟨.privateRow 9 7, 360185280⟩, ⟨.privateRow 9 8, 399399000⟩, ⟨.privateRow 10 2, 56144088⟩, ⟨.privateRow 10 3, 111505680⟩, ⟨.privateRow 10 4, 52141320⟩, ⟨.privateRow 11 0, 49376250⟩, ⟨.privateRow 12 0, 24139500⟩, ⟨.hall 6 12, 854700⟩, ⟨.hall 5 14, 2865720⟩, ⟨.hall 5 15, 3024450⟩, ⟨.hall 7 18, 2270268000⟩, ⟨.hall 4 19, 1269475272⟩]
  caps := #[0, 947133158400, 26139278880, 52904880600, 0, 0, 221707200, 0, 543314460, 111836240, 5148000, 32432400, 3552780, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_26_11_checked :
    (Witness.linear .positive case_49_26_11).check 49 26 11 = true := by
  change case_49_26_11.check 49 26 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_26_12 : Certificate := {
  objectiveScale := 2654652000000
  eta := 1165136083814102400
  rows := #[⟨.count 2, 302984647588022400⟩, ⟨.count 3, 54192375991353600⟩, ⟨.count 4, 9149362180358400⟩, ⟨.count 5, 1740971750918400⟩, ⟨.count 6, 358072204089600⟩, ⟨.count 7, 81347032166400⟩, ⟨.count 8, 20336758041600⟩, ⟨.count 9, 6863655839040⟩, ⟨.count 10, 2723672952000⟩, ⟨.count 11, 2765575612800⟩, ⟨.path 12, 202284482400⟩, ⟨.path 13, 657265288680⟩, ⟨.privateRow 4 22, 228734054508960⟩, ⟨.privateRow 6 15, 3944281941600⟩, ⟨.privateRow 7 12, 1180258279200⟩, ⟨.privateRow 7 13, 6536815084800⟩, ⟨.privateRow 7 14, 9018383774400⟩, ⟨.privateRow 8 9, 206545198860⟩, ⟨.privateRow 8 10, 1871264194800⟩, ⟨.privateRow 8 11, 2998877406525⟩, ⟨.privateRow 8 12, 4630244018400⟩, ⟨.privateRow 8 13, 5772673506600⟩, ⟨.privateRow 9 7, 346649284800⟩, ⟨.privateRow 9 8, 1296468325152⟩, ⟨.privateRow 9 9, 1365199035200⟩, ⟨.privateRow 9 10, 1811242513080⟩, ⟨.privateRow 9 11, 2493673902720⟩, ⟨.privateRow 9 12, 225963978240⟩, ⟨.privateRow 10 4, 104756652000⟩, ⟨.privateRow 10 5, 304143479640⟩, ⟨.privateRow 10 6, 524926059840⟩, ⟨.privateRow 10 7, 811654539696⟩, ⟨.privateRow 11 2, 155638454400⟩, ⟨.privateRow 11 3, 186950332800⟩, ⟨.privateRow 12 0, 81942981120⟩, ⟨.privateRow 13 0, 47888755200⟩, ⟨.privateRow 14 3, 70815496752⟩, ⟨.privateRow 15 6, 169472983680⟩, ⟨.hall 7 11, 1555554000⟩, ⟨.hall 6 12, 4900896000⟩, ⟨.hall 7 12, 475675200⟩, ⟨.hall 5 16, 21843993600⟩, ⟨.hall 5 17, 399972624480⟩, ⟨.hall 8 17, 1553502350400⟩, ⟨.hall 4 20, 30010395430080⟩]
  caps := #[0, 0, 0, 0, 0, 0, 1200433634400, 0, 545769904680, 520088479456, 144719083080, 0, 275851015440, 0, 157973031216, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_26_12_checked :
    (Witness.linear .positive case_49_26_12).check 49 26 12 = true := by
  change case_49_26_12.check 49 26 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_26_13 : Certificate := {
  objectiveScale := 1592791200000
  eta := 1002558955840041600
  rows := #[⟨.count 2, 298058067952444800⟩, ⟨.count 3, 61934143990118400⟩, ⟨.count 4, 11894170834465920⟩, ⟨.count 5, 2426247865641600⟩, ⟨.count 6, 543281964825600⟩, ⟨.count 7, 132188927270400⟩, ⟨.count 8, 33047231817600⟩, ⟨.count 9, 9914169545280⟩, ⟨.count 10, 3813142132800⟩, ⟨.count 11, 1382787806400⟩, ⟨.count 12, 1382787806400⟩, ⟨.path 14, 366292967040⟩, ⟨.path 15, 63836572800⟩, ⟨.privateRow 4 22, 52784781809760⟩, ⟨.privateRow 7 14, 8534175249600⟩, ⟨.privateRow 8 11, 1251187262325⟩, ⟨.privateRow 8 12, 3949325780400⟩, ⟨.privateRow 8 13, 8473649184000⟩, ⟨.privateRow 9 9, 1110989559680⟩, ⟨.privateRow 9 10, 1980715496760⟩, ⟨.privateRow 9 11, 3607353509760⟩, ⟨.privateRow 9 12, 5070066761760⟩, ⟨.privateRow 10 6, 148563979200⟩, ⟨.privateRow 10 7, 512050514976⟩, ⟨.privateRow 10 8, 817101885600⟩, ⟨.privateRow 10 9, 1702295595000⟩, ⟨.privateRow 10 10, 2708109106560⟩, ⟨.privateRow 11 4, 150151201200⟩, ⟨.privateRow 11 5, 297127958400⟩, ⟨.privateRow 11 6, 473500067040⟩, ⟨.privateRow 11 7, 656475019200⟩, ⟨.privateRow 12 2, 127051016400⟩, ⟨.privateRow 12 3, 192053862000⟩, ⟨.privateRow 12 4, 6983776800⟩, ⟨.privateRow 13 0, 68840085600⟩, ⟨.privateRow 14 0, 29331862560⟩, ⟨.privateRow 15 0, 35306871600⟩, ⟨.hall 8 11, 513513000⟩, ⟨.hall 7 12, 9751341600⟩, ⟨.hall 8 12, 6276270000⟩, ⟨.hall 6 15, 91983691800⟩, ⟨.hall 6 16, 74861186400⟩, ⟨.hall 9 16, 3185095193280⟩, ⟨.hall 5 17, 589514777280⟩, ⟨.hall 4 20, 28182351038400⟩]
  caps := #[0, 3534917776790400, 0, 54441178471680, 15615724924800, 940905201600, 3637328323200, 0, 1028972980035, 491570759680, 0, 387865951200, 270874259040, 258597630720, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_26_13_checked :
    (Witness.linear .positive case_49_26_13).check 49 26 13 = true := by
  change case_49_26_13.check 49 26 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_26_14 : Certificate := {
  objectiveScale := 239639400000
  eta := 352250443943798400
  rows := #[⟨.count 2, 99147415165999200⟩, ⟨.count 3, 21025938087554400⟩, ⟨.count 4, 4979364417387360⟩, ⟨.count 5, 1148300516563200⟩, ⟨.count 6, 304052690541600⟩, ⟨.count 7, 81982555855200⟩, ⟨.count 8, 22561090952400⟩, ⟨.count 9, 7435627158960⟩, ⟨.count 10, 2723672952000⟩, ⟨.count 11, 1152323172000⟩, ⟨.count 12, 691393903200⟩, ⟨.count 13, 680918238000⟩, ⟨.path 15, 119037718800⟩, ⟨.privateRow 4 22, 413480790843120⟩, ⟨.privateRow 7 14, 3011171763600⟩, ⟨.privateRow 8 12, 1957639934250⟩, ⟨.privateRow 8 13, 5401951354800⟩, ⟨.privateRow 8 14, 2057507942490⟩, ⟨.privateRow 9 9, 4707582880⟩, ⟨.privateRow 9 10, 990357748380⟩, ⟨.privateRow 9 11, 2481568689600⟩, ⟨.privateRow 9 12, 4060290234000⟩, ⟨.privateRow 10 7, 61282641420⟩, ⟨.privateRow 10 8, 417629852640⟩, ⟨.privateRow 10 9, 1157561004600⟩, ⟨.privateRow 10 10, 1900734624360⟩, ⟨.privateRow 10 11, 2453575384260⟩, ⟨.privateRow 11 5, 51425992800⟩, ⟨.privateRow 11 6, 219988969200⟩, ⟨.privateRow 11 7, 506323818000⟩, ⟨.privateRow 11 8, 900907207200⟩, ⟨.privateRow 11 9, 989202099600⟩, ⟨.privateRow 12 3, 34409650275⟩, ⟨.privateRow 12 4, 127453926600⟩, ⟨.privateRow 12 5, 262153521630⟩, ⟨.privateRow 12 6, 243268225200⟩, ⟨.privateRow 13 1, 24980432400⟩, ⟨.privateRow 13 2, 85551265800⟩, ⟨.privateRow 13 3, 34283995200⟩, ⟨.privateRow 14 0, 38759961240⟩, ⟨.privateRow 15 0, 30010840860⟩, ⟨.hall 8 10, 443877525⟩, ⟨.hall 8 11, 5404724325⟩, ⟨.hall 9 12, 6119020908⟩, ⟨.hall 7 13, 22455232800⟩, ⟨.hall 9 13, 6228399177⟩, ⟨.hall 6 16, 416992736160⟩, ⟨.hall 5 18, 3166901234640⟩, ⟨.hall 4 20, 29591468590320⟩, ⟨.assumptionRow 14, 712668656700⟩]
  caps := #[0, 320173575321600, 0, 0, 0, 1627293868200, 1375887169800, 0, 162443456175, 64292157930, 5273541000, 164981255400, 27577404855, 6769986300, 42554732220, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_26_14_checked :
    (Witness.linear .conditional case_49_26_14).check 49 26 14 = true := by
  change case_49_26_14.check 49 26 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_26_15 : Certificate := {
  objectiveScale := 942172000000
  eta := 383515276246502400
  rows := #[⟨.count 2, 100236947200790400⟩, ⟨.count 3, 25837473967905600⟩, ⟨.count 4, 6848487075830400⟩, ⟨.count 5, 1966072844736000⟩, ⟨.count 6, 584360539963200⟩, ⟨.count 7, 182150866497600⟩, ⟨.count 8, 58468179369600⟩, ⟨.count 9, 20238985166400⟩, ⟨.count 10, 7710089587200⟩, ⟨.count 11, 3669706101600⟩, ⟨.count 12, 1223235367200⟩, ⟨.count 13, 963761198400⟩, ⟨.count 14, 1349265677760⟩, ⟨.path 13, 140971210380⟩, ⟨.privateRow 3 23, 1660239291110400⟩, ⟨.privateRow 7 14, 4229840815200⟩, ⟨.privateRow 8 12, 1907444038500⟩, ⟨.privateRow 8 13, 13539506280300⟩, ⟨.privateRow 9 10, 749592043200⟩, ⟨.privateRow 9 11, 5257852760160⟩, ⟨.privateRow 9 12, 12580653125040⟩, ⟨.privateRow 10 8, 278419901760⟩, ⟨.privateRow 10 9, 2132321651460⟩, ⟨.privateRow 10 10, 5390178702480⟩, ⟨.privateRow 10 11, 9163762728120⟩, ⟨.privateRow 10 12, 1089050154192⟩, ⟨.privateRow 11 6, 88962572160⟩, ⟨.privateRow 11 7, 889625721600⟩, ⟨.privateRow 11 8, 2363068323000⟩, ⟨.privateRow 11 9, 4215131395200⟩, ⟨.privateRow 11 10, 5794923103200⟩, ⟨.privateRow 11 11, 192752239680⟩, ⟨.privateRow 12 1, 14562325800⟩, ⟨.privateRow 12 5, 394153618320⟩, ⟨.privateRow 12 6, 1091095744200⟩, ⟨.privateRow 12 7, 2025983576925⟩, ⟨.privateRow 12 8, 2019309177600⟩, ⟨.privateRow 13 3, 171859514400⟩, ⟨.privateRow 13 4, 548602528320⟩, ⟨.privateRow 13 5, 741354768000⟩, ⟨.privateRow 14 1, 92360448180⟩, ⟨.privateRow 14 2, 240940299600⟩, ⟨.privateRow 15 0, 93699005400⟩, ⟨.privateRow 16 0, 89439959700⟩, ⟨.hall 8 11, 10579245600⟩, ⟨.hall 9 11, 31970924370⟩, ⟨.hall 8 12, 43901850300⟩, ⟨.hall 7 14, 264175111200⟩, ⟨.hall 7 15, 69621552000⟩, ⟨.hall 10 15, 22558035550050⟩, ⟨.hall 6 16, 1616131717200⟩, ⟨.hall 5 17, 2057915985840⟩, ⟨.hall 4 20, 139206752249760⟩, ⟨.hall 3 22, 2706911887680000⟩, ⟨.assumptionRow 15, 1044086745240⟩]
  caps := #[0, 5326026051407600, 0, 58546868229080, 0, 2026262518280, 3177267407600, 163601438000, 361472717760, 492252552792, 0, 0, 0, 221296757220, 0, 694314811960, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_26_15_checked :
    (Witness.linear .conditional case_49_26_15).check 49 26 15 = true := by
  change case_49_26_15.check 49 26 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_26_16 : Certificate := {
  objectiveScale := 1387562400000
  eta := 407484981011908800
  rows := #[⟨.count 2, 104595075339955200⟩, ⟨.count 3, 28639127771654400⟩, ⟨.count 4, 8218184490996480⟩, ⟨.count 5, 2408439234801600⟩, ⟨.count 6, 720893376403200⟩, ⟨.count 7, 227126389089600⟩, ⟨.count 8, 75334000341600⟩, ⟨.count 9, 26310680716320⟩, ⟨.count 10, 9637611984000⟩, ⟨.count 11, 3669706101600⟩, ⟨.count 12, 1630980489600⟩, ⟨.count 13, 963761198400⟩, ⟨.count 14, 674632838880⟩, ⟨.count 15, 1124388064800⟩, ⟨.path 12, 217409872680⟩, ⟨.privateRow 3 23, 3735538404998400⟩, ⟨.privateRow 7 14, 214169155200⟩, ⟨.privateRow 8 13, 14499921085650⟩, ⟨.privateRow 9 11, 4465426885920⟩, ⟨.privateRow 9 12, 16590970556160⟩, ⟨.privateRow 9 13, 3433131557856⟩, ⟨.privateRow 10 9, 1349265677760⟩, ⟨.privateRow 10 10, 6223143738240⟩, ⟨.privateRow 10 11, 14022725436720⟩, ⟨.privateRow 10 12, 11439845425008⟩, ⟨.privateRow 11 7, 354202833600⟩, ⟨.privateRow 11 8, 2307466715400⟩, ⟨.privateRow 11 9, 5952019708800⟩, ⟨.privateRow 11 10, 10527237705600⟩, ⟨.privateRow 11 11, 10141733226240⟩, ⟨.privateRow 12 5, 47570264280⟩, ⟨.privateRow 12 6, 845693587200⟩, ⟨.privateRow 12 7, 2544159669975⟩, ⟨.privateRow 12 8, 3320210282400⟩, ⟨.privateRow 12 9, 10635351942600⟩, ⟨.privateRow 13 4, 252060621120⟩, ⟨.privateRow 13 5, 1025540762400⟩, ⟨.privateRow 13 6, 2627175959100⟩, ⟨.privateRow 13 7, 2229359695200⟩, ⟨.privateRow 14 2, 43807327200⟩, ⟨.privateRow 14 3, 481880599200⟩, ⟨.privateRow 14 4, 1161867666960⟩, ⟨.privateRow 15 1, 204434193600⟩, ⟨.privateRow 15 2, 187398010800⟩, ⟨.privateRow 16 0, 76662822600⟩, ⟨.hall 9 11, 81839751840⟩, ⟨.hall 10 11, 41635013310⟩, ⟨.hall 8 12, 140760496800⟩, ⟨.hall 10 12, 95581811160⟩, ⟨.hall 7 14, 143575111680⟩, ⟨.hall 11 14, 10030530011040⟩, ⟨.hall 7 15, 1501794894600⟩, ⟨.hall 6 16, 2857185611280⟩, ⟨.hall 5 18, 20933666170560⟩, ⟨.hall 4 19, 23650324317360⟩, ⟨.hall 3 22, 4818303160070400⟩, ⟨.assumptionRow 16, 948672986800⟩]
  caps := #[0, 0, 673752228398480, 58322030138400, 4566772302960, 0, 0, 2281496417200, 310436464800, 575050443968, 0, 216862732350, 369895964405, 0, 274040147920, 832263353600, 0, 1387562400000, 0, 0, 0, 0, 0, 0] }

theorem case_49_26_16_checked :
    (Witness.linear .conditional case_49_26_16).check 49 26 16 = true := by
  change case_49_26_16.check 49 26 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_27_1_checked :
    (Witness.rising).check 49 27 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_27_2_checked :
    (Witness.rising).check 49 27 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_27_3_checked :
    (Witness.rising).check 49 27 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_27_4_checked :
    (Witness.rising).check 49 27 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_27_5_checked :
    (Witness.rising).check 49 27 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_27_6_checked :
    (Witness.rising).check 49 27 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_27_7_checked :
    (Witness.rising).check 49 27 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_27_8_checked :
    (Witness.rising).check 49 27 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_27_9_checked :
    (Witness.rising).check 49 27 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_27_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_27_10_checked :
    (Witness.linear .positive case_49_27_10).check 49 27 10 = true := by
  change case_49_27_10.check 49 27 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_27_11 : Certificate := {
  objectiveScale := 26960232000000
  eta := 11529427992160478400
  rows := #[⟨.count 2, 2522526072930864000⟩, ⟨.count 3, 365024361141760320⟩, ⟨.count 4, 53886779886139200⟩, ⟨.count 5, 8720807372877600⟩, ⟨.count 6, 1653814216454400⟩, ⟨.count 7, 341673423191100⟩, ⟨.count 8, 85753329742080⟩, ⟨.count 9, 34454462842800⟩, ⟨.count 10, 26503432956000⟩, ⟨.path 11, 6854083922400⟩, ⟨.path 12, 4417473660600⟩, ⟨.privateRow 5 18, 93716138932416⟩, ⟨.privateRow 5 19, 429532303440240⟩, ⟨.privateRow 6 15, 86409605224800⟩, ⟨.privateRow 6 16, 117400391908800⟩, ⟨.privateRow 6 17, 143943089209920⟩, ⟨.privateRow 6 18, 220125734829000⟩, ⟨.privateRow 7 11, 9187856758080⟩, ⟨.privateRow 7 12, 23607687503400⟩, ⟨.privateRow 7 13, 39479072007375⟩, ⟨.privateRow 7 14, 54142727324400⟩, ⟨.privateRow 7 15, 16270163009100⟩, ⟨.privateRow 7 16, 145282984987140⟩, ⟨.privateRow 8 8, 4131345313095⟩, ⟨.privateRow 8 9, 9135653026500⟩, ⟨.privateRow 8 10, 13264968194478⟩, ⟨.privateRow 8 11, 9081515823380⟩, ⟨.privateRow 8 12, 35172264152025⟩, ⟨.privateRow 9 5, 1585999083240⟩, ⟨.privateRow 9 6, 3592687578480⟩, ⟨.privateRow 9 7, 5168169426420⟩, ⟨.privateRow 9 8, 4454718428160⟩, ⟨.privateRow 10 2, 695715115095⟩, ⟨.privateRow 10 3, 1590205977360⟩, ⟨.privateRow 10 4, 340758423720⟩, ⟨.privateRow 11 0, 571642671600⟩, ⟨.privateRow 12 0, 276077426625⟩, ⟨.hall 12 6, 1059078240⟩, ⟨.hall 5 16, 42158402000⟩, ⟨.hall 4 20, 1146536614080⟩, ⟨.hall 6 20, 17500679539200⟩, ⟨.hall 4 21, 113904002852640⟩, ⟨.hall 3 23, 1947538512189270⟩]
  caps := #[0, 40742742050181600, 290186457132000, 1136347627374960, 58030120004688, 83982337062624, 47095600211400, 8861845108545, 11582933328746, 0, 2132425878375, 0, 2153638762275, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_27_11_checked :
    (Witness.linear .positive case_49_27_11).check 49 27 11 = true := by
  change case_49_27_11.check 49 27 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_27_12 : Certificate := {
  objectiveScale := 2462803200000
  eta := 1501375143942273600
  rows := #[⟨.count 2, 348027661399017600⟩, ⟨.count 3, 56655665809142400⟩, ⟨.count 4, 9627203363057280⟩, ⟨.count 5, 1751261182070400⟩, ⟨.count 6, 359161673270400⟩, ⟨.count 7, 80393746633200⟩, ⟨.count 8, 21438332435520⟩, ⟨.count 9, 6264447789600⟩, ⟨.count 10, 2891283595200⟩, ⟨.count 11, 2650343295600⟩, ⟨.path 12, 241313900100⟩, ⟨.path 13, 578532995040⟩, ⟨.privateRow 5 19, 76913497861200⟩, ⟨.privateRow 6 16, 24361741404000⟩, ⟨.privateRow 6 17, 34524067818240⟩, ⟨.privateRow 6 18, 60904353510000⟩, ⟨.privateRow 7 12, 348024877200⟩, ⟨.privateRow 7 13, 6199193125125⟩, ⟨.privateRow 7 14, 10217016037800⟩, ⟨.privateRow 7 15, 16618187886300⟩, ⟨.privateRow 7 16, 21716752337280⟩, ⟨.privateRow 7 17, 23752697868900⟩, ⟨.privateRow 8 10, 1754045381088⟩, ⟨.privateRow 8 11, 3194094984080⟩, ⟨.privateRow 8 12, 5024609164575⟩, ⟨.privateRow 8 14, 20748083095740⟩, ⟨.privateRow 8 15, 535958310888⟩, ⟨.privateRow 9 7, 417629852640⟩, ⟨.privateRow 9 8, 1025091456480⟩, ⟨.privateRow 9 9, 1670519410560⟩, ⟨.privateRow 9 10, 2150020352480⟩, ⟨.privateRow 9 11, 2436174140400⟩, ⟨.privateRow 10 4, 89492111280⟩, ⟨.privateRow 10 5, 355850288640⟩, ⟨.privateRow 10 6, 586288062360⟩, ⟨.privateRow 10 7, 630825511680⟩, ⟨.privateRow 11 2, 155272637520⟩, ⟨.privateRow 11 3, 154890192600⟩, ⟨.privateRow 12 0, 65254664475⟩, ⟨.privateRow 13 0, 38550447936⟩, ⟨.hall 13 1, 49717839600⟩, ⟨.hall 14 3, 4259045700⟩, ⟨.hall 5 19, 107571325680⟩, ⟨.hall 6 19, 2545553387520⟩, ⟨.hall 5 20, 15674678884800⟩, ⟨.hall 6 20, 22671334857600⟩, ⟨.hall 4 21, 38220559715520⟩, ⟨.hall 3 23, 640748601412920⟩]
  caps := #[0, 4099148492150400, 655314271154400, 87795075688320, 7641029306040, 6441702696000, 0, 3838104222030, 0, 1319856659680, 654186651240, 0, 427978546125, 276276000, 696049754400, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_27_12_checked :
    (Witness.linear .positive case_49_27_12).check 49 27 12 = true := by
  change case_49_27_12.check 49 27 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_27_13 : Certificate := {
  objectiveScale := 2693691000000
  eta := 2152915300747411200
  rows := #[⟨.count 2, 469432659561465600⟩, ⟨.count 3, 95505265221125760⟩, ⟨.count 4, 19935978645623040⟩, ⟨.count 5, 4212493113628800⟩, ⟨.count 6, 968901258124800⟩, ⟨.count 7, 233872717478400⟩, ⟨.count 8, 58468179369600⟩, ⟨.count 9, 17540453810880⟩, ⟨.count 10, 5782567190400⟩, ⟨.count 11, 3533791060800⟩, ⟨.count 12, 1927522396800⟩, ⟨.path 14, 705511023360⟩, ⟨.privateRow 8 15, 30695794169040⟩, ⟨.privateRow 9 13, 12714508847040⟩, ⟨.privateRow 10 10, 3782762703720⟩, ⟨.privateRow 10 16, 192173982960960⟩, ⟨.privateRow 11 12, 1542017917440⟩, ⟨.privateRow 12 12, 321253732800⟩, ⟨.privateRow 13 0, 38550447936⟩, ⟨.privateRow 13 12, 257002986240⟩, ⟨.privateRow 14 0, 59661407520⟩, ⟨.privateRow 14 6, 34802487720⟩, ⟨.privateRow 15 0, 74959204320⟩, ⟨.privateRow 15 4, 54137203120⟩, ⟨.privateRow 15 11, 243617414040⟩, ⟨.hall 15 1, 174012438600⟩, ⟨.hall 16 1, 506218003200⟩, ⟨.hall 15 2, 15819312600⟩, ⟨.hall 16 2, 50621800320⟩, ⟨.hall 11 3, 10899680220⟩, ⟨.hall 12 3, 4236312960⟩, ⟨.hall 12 4, 423631296⟩, ⟨.hall 17 4, 90155015808⟩, ⟨.hall 18 4, 338081309280⟩, ⟨.hall 10 5, 2933231400⟩, ⟨.hall 8 10, 12152125440⟩, ⟨.hall 7 12, 20748672945⟩, ⟨.hall 13 12, 123912154080⟩, ⟨.hall 10 13, 58716543600⟩, ⟨.hall 6 15, 138378754800⟩, ⟨.hall 10 16, 76760744860800⟩, ⟨.hall 5 17, 573713736960⟩, ⟨.hall 4 20, 17574882923520⟩]
  caps := #[0, 0, 0, 216053843765760, 87609462420480, 6574863609600, 0, 6761626185600, 794746592640, 1924516513920, 310325832960, 0, 1591266877200, 380008244616, 0, 691290439840, 5568398035200, 0, 0, 0, 0, 0, 0] }

theorem case_49_27_13_checked :
    (Witness.linear .positive case_49_27_13).check 49 27 13 = true := by
  change case_49_27_13.check 49 27 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_27_14 : Certificate := {
  objectiveScale := 471395925000
  eta := 410753577116282400
  rows := #[⟨.count 2, 98472942953985600⟩, ⟨.count 3, 23066949650865120⟩, ⟨.count 4, 5921156050729920⟩, ⟨.count 5, 1526437111399200⟩, ⟨.count 6, 392572061481600⟩, ⟨.count 7, 100492183291500⟩, ⟨.count 8, 29234089684800⟩, ⟨.count 9, 8770226905440⟩, ⟨.count 10, 2891283595200⟩, ⟨.count 11, 883447765200⟩, ⟨.count 12, 481880599200⟩, ⟨.count 13, 626444778960⟩, ⟨.path 15, 78572894400⟩, ⟨.privateRow 12 13, 856676620800⟩, ⟨.privateRow 13 7, 144564179760⟩, ⟨.privateRow 14 2, 5800414620⟩, ⟨.privateRow 14 6, 8700621930⟩, ⟨.privateRow 14 11, 301621560240⟩, ⟨.privateRow 15 0, 9369900540⟩, ⟨.privateRow 16 0, 21751554825⟩, ⟨.privateRow 16 6, 217515548250⟩, ⟨.privateRow 17 1, 69604975440⟩, ⟨.hall 17 2, 52590425888⟩, ⟨.hall 13 4, 1807921440⟩, ⟨.hall 14 4, 3236874732⟩, ⟨.hall 16 7, 3163862520⟩, ⟨.hall 12 11, 8207856360⟩, ⟨.hall 13 13, 1879334336880⟩, ⟨.hall 11 14, 154603358910⟩, ⟨.hall 7 16, 437361139215⟩, ⟨.hall 5 18, 1577577975480⟩, ⟨.hall 4 20, 10126403801280⟩]
  caps := #[0, 0, 0, 30417374267280, 29094879733920, 2859856599600, 685274990400, 2088149263200, 0, 29357087760, 0, 137916979200, 42585182640, 250977406680, 17726621640, 20011016025, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_27_14_checked :
    (Witness.linear .positive case_49_27_14).check 49 27 14 = true := by
  change case_49_27_14.check 49 27 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_27_15 : Certificate := {
  objectiveScale := 29752800000
  eta := 17432512556659200
  rows := #[⟨.count 2, 4461893094859200⟩, ⟨.count 3, 1182920494916160⟩, ⟨.count 4, 314571655157760⟩, ⟨.count 5, 85560577502400⟩, ⟨.count 6, 23772776227200⟩, ⟨.count 7, 7167973913100⟩, ⟨.count 8, 2248776129600⟩, ⟨.count 9, 771008958720⟩, ⟨.count 10, 259474168800⟩, ⟨.count 11, 101936280600⟩, ⟨.count 12, 74135476800⟩, ⟨.count 13, 48188059920⟩, ⟨.path 13, 4959154200⟩, ⟨.privateRow 5 19, 6963174658440⟩, ⟨.privateRow 6 17, 2837741306400⟩, ⟨.privateRow 6 18, 8339211480600⟩, ⟨.privateRow 7 15, 1107656099550⟩, ⟨.privateRow 7 16, 3180411954720⟩, ⟨.privateRow 7 17, 5807665138275⟩, ⟨.privateRow 8 12, 9369900540⟩, ⟨.privateRow 8 13, 414952738200⟩, ⟨.privateRow 8 14, 1238388521370⟩, ⟨.privateRow 8 15, 2284381751652⟩, ⟨.privateRow 8 16, 3263067863055⟩, ⟨.privateRow 9 10, 9518629120⟩, ⟨.privateRow 9 11, 159288309180⟩, ⟨.privateRow 9 12, 489529497600⟩, ⟨.privateRow 9 13, 937882425480⟩, ⟨.privateRow 9 14, 1365328364400⟩, ⟨.privateRow 9 15, 1579497519600⟩, ⟨.privateRow 10 8, 4448128608⟩, ⟨.privateRow 10 9, 65074474080⟩, ⟨.privateRow 10 10, 200629134090⟩, ⟨.privateRow 10 11, 399802035600⟩, ⟨.privateRow 10 12, 331756258680⟩, ⟨.privateRow 10 13, 1274388846192⟩, ⟨.privateRow 11 6, 1404081000⟩, ⟨.privateRow 11 7, 28109701620⟩, ⟨.privateRow 11 8, 88207488600⟩, ⟨.privateRow 11 9, 66413031300⟩, ⟨.privateRow 11 10, 513652946400⟩, ⟨.privateRow 11 11, 14415231600⟩, ⟨.privateRow 12 5, 12636729000⟩, ⟨.privateRow 12 6, 20387256120⟩, ⟨.privateRow 12 7, 129737084400⟩, ⟨.privateRow 12 8, 42859572525⟩, ⟨.privateRow 13 3, 5560160760⟩, ⟨.privateRow 13 4, 21229704720⟩, ⟨.privateRow 13 5, 25206062112⟩, ⟨.privateRow 14 0, 2677114440⟩, ⟨.privateRow 14 1, 823727520⟩, ⟨.privateRow 14 2, 7585157580⟩, ⟨.privateRow 15 0, 2883046320⟩, ⟨.privateRow 16 0, 1673196525⟩, ⟨.hall 8 16, 12196664480⟩, ⟨.hall 7 17, 118192254180⟩, ⟨.hall 8 17, 186082937040⟩, ⟨.hall 7 18, 30328888590⟩, ⟨.hall 6 19, 2615923252800⟩, ⟨.hall 5 20, 5090921347200⟩, ⟨.hall 4 21, 8321487501600⟩, ⟨.hall 3 22, 10291904572950⟩, ⟨.hall 2 24, 178475723794368⟩, ⟨.assumptionRow 15, 36069765732⟩]
  caps := #[0, 0, 20738054213184, 0, 221486601336, 235035128328, 157620983520, 0, 187420320087, 0, 36799330194, 23141462880, 0, 18689667612, 0, 0, 9674441700, 0, 0, 0, 0, 0, 0] }

theorem case_49_27_15_checked :
    (Witness.linear .conditional case_49_27_15).check 49 27 15 = true := by
  change case_49_27_15.check 49 27 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_27_16 : Certificate := {
  objectiveScale := 40378800000
  eta := 13074384417494400
  rows := #[⟨.count 2, 3528008493609600⟩, ⟨.count 3, 965014087957920⟩, ⟨.count 4, 265419834039360⟩, ⟨.count 5, 75548169496800⟩, ⟨.count 6, 22487761296000⟩, ⟨.count 7, 7027425405000⟩, ⟨.count 8, 2323735333920⟩, ⟨.count 9, 771008958720⟩, ⟨.count 10, 296541907200⟩, ⟨.count 11, 101936280600⟩, ⟨.count 12, 74135476800⟩, ⟨.count 13, 48188059920⟩, ⟨.path 11, 5501839200⟩, ⟨.path 12, 1446367650⟩, ⟨.privateRow 2 25, 363177344930400⟩, ⟨.privateRow 5 19, 13880838371400⟩, ⟨.privateRow 6 17, 4465426885920⟩, ⟨.privateRow 6 18, 13519427922000⟩, ⟨.privateRow 7 15, 1412177867100⟩, ⟨.privateRow 7 16, 4722429872160⟩, ⟨.privateRow 7 17, 9532200602925⟩, ⟨.privateRow 8 13, 437708210940⟩, ⟨.privateRow 8 14, 1663157345850⟩, ⟨.privateRow 8 15, 3588671906820⟩, ⟨.privateRow 8 16, 5842132986690⟩, ⟨.privateRow 9 11, 131178607560⟩, ⟨.privateRow 9 12, 589730066640⟩, ⟨.privateRow 9 13, 1387637651400⟩, ⟨.privateRow 9 14, 2378348468496⟩, ⟨.privateRow 9 15, 3197813198580⟩, ⟨.privateRow 10 9, 36655874640⟩, ⟨.privateRow 10 10, 209896068690⟩, ⟨.privateRow 10 11, 551250223920⟩, ⟨.privateRow 10 12, 1013802645240⟩, ⟨.privateRow 10 13, 1457503473888⟩, ⟨.privateRow 10 14, 1632833876520⟩, ⟨.privateRow 11 7, 8031343320⟩, ⟨.privateRow 11 8, 74478696600⟩, ⟨.privateRow 11 9, 224723164050⟩, ⟨.privateRow 11 10, 452314665000⟩, ⟨.privateRow 11 11, 700683221700⟩, ⟨.privateRow 11 12, 610999887960⟩, ⟨.privateRow 12 6, 25329621240⟩, ⟨.privateRow 12 7, 94042225200⟩, ⟨.privateRow 12 8, 211595006700⟩, ⟨.privateRow 12 9, 351260949600⟩, ⟨.privateRow 13 4, 5728650480⟩, ⟨.privateRow 13 5, 29283513336⟩, ⟨.privateRow 13 6, 124382855520⟩, ⟨.privateRow 13 7, 52358180490⟩, ⟨.privateRow 14 2, 892371480⟩, ⟨.privateRow 14 3, 15089190480⟩, ⟨.privateRow 14 4, 40692139488⟩, ⟨.privateRow 15 1, 6246600360⟩, ⟨.privateRow 15 2, 5962663980⟩, ⟨.privateRow 16 0, 1673196525⟩, ⟨.hall 8 15, 9577798230⟩, ⟨.hall 8 16, 60854393600⟩, ⟨.hall 7 17, 123288165000⟩, ⟨.hall 9 17, 2690500012200⟩, ⟨.hall 7 18, 1360361612610⟩, ⟨.hall 6 19, 5103345012480⟩, ⟨.hall 5 20, 9198727465200⟩, ⟨.hall 4 21, 14797353261600⟩, ⟨.hall 3 22, 20442824151750⟩, ⟨.hall 2 24, 473168197966464⟩, ⟨.assumptionRow 16, 32442453120⟩]
  caps := #[0, 423516767564400, 28578211356420, 0, 0, 338695539000, 85297452240, 2442773190, 0, 62250047262, 732320322, 7578177540, 0, 0, 32442453120, 32442453120, 75189761955, 40378800000, 0, 0, 0, 0, 0] }

theorem case_49_27_16_checked :
    (Witness.linear .conditional case_49_27_16).check 49 27 16 = true := by
  change case_49_27_16.check 49 27 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_27_17 : Certificate := {
  objectiveScale := 54648000000
  eta := 21790640695824000
  rows := #[⟨.count 2, 5603307607497600⟩, ⟨.count 3, 1447521131936880⟩, ⟨.count 4, 383384204723520⟩, ⟨.count 5, 103764955694400⟩, ⟨.count 6, 28591582219200⟩, ⟨.count 7, 8011264961700⟩, ⟨.count 8, 2323735333920⟩, ⟨.count 9, 626444778960⟩, ⟨.count 10, 185338692000⟩, ⟨.count 11, 67957520400⟩, ⟨.count 12, 37067738400⟩, ⟨.path 11, 15285597600⟩, ⟨.privateRow 2 25, 570707256319200⟩, ⟨.privateRow 5 19, 19842772229280⟩, ⟨.privateRow 6 16, 26771144400⟩, ⟨.privateRow 6 17, 6071695549920⟩, ⟨.privateRow 6 18, 19596477700800⟩, ⟨.privateRow 7 15, 1820437819200⟩, ⟨.privateRow 7 16, 6529482119160⟩, ⟨.privateRow 7 17, 14315869467900⟩, ⟨.privateRow 8 13, 516683086920⟩, ⟨.privateRow 8 14, 2166008674830⟩, ⟨.privateRow 8 15, 5164689177648⟩, ⟨.privateRow 8 16, 9355845689190⟩, ⟨.privateRow 9 11, 135863557830⟩, ⟨.privateRow 9 12, 703698652800⟩, ⟨.privateRow 9 13, 1888258051680⟩, ⟨.privateRow 9 14, 3658009170816⟩, ⟨.privateRow 9 15, 5605877637360⟩, ⟨.privateRow 10 9, 29654190720⟩, ⟨.privateRow 10 10, 220089696750⟩, ⟨.privateRow 10 11, 692107629840⟩, ⟨.privateRow 10 12, 1479002762160⟩, ⟨.privateRow 10 13, 2449436153472⟩, ⟨.privateRow 10 14, 3181338648180⟩, ⟨.privateRow 11 7, 3088978200⟩, ⟨.privateRow 11 8, 63152443200⟩, ⟨.privateRow 11 9, 251365601025⟩, ⟨.privateRow 11 10, 613382814000⟩, ⟨.privateRow 11 11, 1115635959900⟩, ⟨.privateRow 11 12, 1608122050920⟩, ⟨.privateRow 11 13, 1498926671550⟩, ⟨.privateRow 12 6, 11429219340⟩, ⟨.privateRow 12 7, 87177829200⟩, ⟨.privateRow 12 8, 257929679700⟩, ⟨.privateRow 12 9, 397595622600⟩, ⟨.privateRow 12 10, 1117180449000⟩, ⟨.privateRow 13 5, 23352675192⟩, ⟨.privateRow 13 6, 107084577600⟩, ⟨.privateRow 13 7, 261327555720⟩, ⟨.privateRow 13 8, 271653568560⟩, ⟨.privateRow 14 3, 1460244240⟩, ⟨.privateRow 14 4, 38015025048⟩, ⟨.privateRow 14 5, 128501493120⟩, ⟨.privateRow 14 6, 46849502700⟩, ⟨.privateRow 15 2, 6814473120⟩, ⟨.privateRow 15 3, 55282413186⟩, ⟨.privateRow 16 1, 14602442400⟩, ⟨.privateRow 17 0, 4867480800⟩, ⟨.hall 9 14, 8188820640⟩, ⟨.hall 8 15, 5366661300⟩, ⟨.hall 9 15, 49172293170⟩, ⟨.hall 8 16, 228848620000⟩, ⟨.hall 7 18, 4754977947720⟩, ⟨.hall 6 19, 8931618661680⟩, ⟨.hall 5 20, 15158494135200⟩, ⟨.hall 4 21, 23468537514240⟩, ⟨.hall 3 22, 31778017681410⟩, ⟨.hall 2 24, 734655886316352⟩, ⟨.assumptionRow 17, 19797725640⟩]
  caps := #[0, 0, 0, 454408751520, 0, 1252059861360, 0, 177118354920, 4356395316, 21191326920, 88820810418, 0, 35842469520, 19797725640, 155759647524, 19797725640, 176795250000, 0, 54648000000, 0, 0, 0, 0] }

theorem case_49_27_17_checked :
    (Witness.linear .conditional case_49_27_17).check 49 27 17 = true := by
  change case_49_27_17.check 49 27 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_28_1_checked :
    (Witness.rising).check 49 28 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_28_2_checked :
    (Witness.rising).check 49 28 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_28_3_checked :
    (Witness.rising).check 49 28 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_28_4_checked :
    (Witness.rising).check 49 28 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_28_5_checked :
    (Witness.rising).check 49 28 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_28_6_checked :
    (Witness.rising).check 49 28 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_28_7_checked :
    (Witness.rising).check 49 28 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_28_8_checked :
    (Witness.rising).check 49 28 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_28_9_checked :
    (Witness.rising).check 49 28 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_28_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_28_10_checked :
    (Witness.linear .positive case_49_28_10).check 49 28 10 = true := by
  change case_49_28_10.check 49 28 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_28_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_28_11_checked :
    (Witness.linear .positive case_49_28_11).check 49 28 11 = true := by
  change case_49_28_11.check 49 28 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_28_12 : Certificate := {
  objectiveScale := 37128000000
  eta := 28016538037488000
  rows := #[⟨.count 2, 5136365306872800⟩, ⟨.count 3, 851964899385600⟩, ⟨.count 4, 147455463355200⟩, ⟨.count 5, 27306567288000⟩, ⟨.count 6, 5421156741000⟩, ⟨.count 7, 1218087070200⟩, ⟨.count 8, 321253732800⟩, ⟨.count 9, 111203215200⟩, ⟨.count 10, 30889782000⟩, ⟨.count 11, 30889782000⟩, ⟨.path 12, 4129944000⟩, ⟨.path 13, 8338512000⟩, ⟨.privateRow 5 19, 1477767170880⟩, ⟨.privateRow 5 20, 2489716429200⟩, ⟨.privateRow 6 17, 1533763481250⟩, ⟨.privateRow 6 18, 635814679500⟩, ⟨.privateRow 6 19, 1438949011500⟩, ⟨.privateRow 7 15, 914043358800⟩, ⟨.privateRow 7 16, 247633085700⟩, ⟨.privateRow 7 17, 396212937120⟩, ⟨.privateRow 7 18, 491919778350⟩, ⟨.privateRow 8 12, 203014511700⟩, ⟨.privateRow 8 15, 383719736400⟩, ⟨.privateRow 9 11, 149643832800⟩, ⟨.privateRow 10 11, 45176306175⟩, ⟨.privateRow 11 3, 374421600⟩, ⟨.privateRow 11 9, 4992288000⟩, ⟨.privateRow 11 11, 3610494000⟩, ⟨.privateRow 12 0, 363409200⟩, ⟨.privateRow 12 6, 842448600⟩, ⟨.privateRow 13 0, 514829700⟩, ⟨.hall 13 4, 9806280⟩, ⟨.hall 6 13, 2332200⟩, ⟨.hall 5 17, 274040000⟩, ⟨.hall 6 18, 473481450⟩, ⟨.hall 4 20, 11863854600⟩, ⟨.hall 3 23, 1419941498976⟩]
  caps := #[0, 0, 20568351367200, 0, 0, 0, 98117019000, 14370337800, 0, 0, 19443817575, 6238218000, 5696378100, 14516468400, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_28_12_checked :
    (Witness.linear .positive case_49_28_12).check 49 28 12 = true := by
  change case_49_28_12.check 49 28 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_28_13 : Certificate := {
  objectiveScale := 272090000000
  eta := 391193882967888000
  rows := #[⟨.count 2, 80936665441632000⟩, ⟨.count 3, 17997758499520800⟩, ⟨.count 4, 3810176355585600⟩, ⟨.count 5, 883983188088000⟩, ⟨.count 6, 195763993425000⟩, ⟨.count 7, 47505395737800⟩, ⟨.count 8, 11136796070400⟩, ⟨.count 9, 3373164194400⟩, ⟨.count 10, 803134332000⟩, ⟨.count 11, 401567166000⟩, ⟨.count 12, 481880599200⟩, ⟨.path 13, 90698244000⟩, ⟨.privateRow 7 21, 1096626388057200⟩, ⟨.privateRow 8 15, 20127438731400⟩, ⟨.privateRow 9 15, 3587333349600⟩, ⟨.privateRow 10 11, 898506533925⟩, ⟨.privateRow 10 14, 7244271674640⟩, ⟨.privateRow 11 12, 3778381971000⟩, ⟨.privateRow 12 6, 36506106000⟩, ⟨.privateRow 12 15, 13251716478000⟩, ⟨.privateRow 13 0, 20078358300⟩, ⟨.privateRow 13 10, 116008292400⟩, ⟨.privateRow 13 14, 80313433200⟩, ⟨.privateRow 16 12, 5220373158000⟩, ⟨.hall 13 2, 6629045280⟩, ⟨.hall 14 2, 13385572200⟩, ⟨.hall 13 4, 701149020⟩, ⟨.hall 14 4, 1390708800⟩, ⟨.hall 10 7, 706629000⟩, ⟨.hall 7 13, 2389902515⟩, ⟨.hall 11 14, 55904448600⟩, ⟨.hall 6 16, 915388500⟩, ⟨.hall 5 18, 137393755200⟩, ⟨.hall 9 18, 2891283595200⟩, ⟨.hall 3 23, 91763719371324⟩]
  caps := #[0, 2998076123952000, 0, 48995850103200, 0, 0, 0, 469650171900, 291381417600, 323581658400, 103848108000, 0, 0, 327259987600, 23120533800, 745767594000, 0, 0, 0, 0, 0, 0] }

theorem case_49_28_13_checked :
    (Witness.linear .positive case_49_28_13).check 49 28 13 = true := by
  change case_49_28_13.check 49 28 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_28_14 : Certificate := {
  objectiveScale := 202800000
  eta := 234599030265600
  rows := #[⟨.count 2, 57867760798848⟩, ⟨.count 3, 14075941815936⟩, ⟨.count 4, 3402371900928⟩, ⟨.count 5, 895785770880⟩, ⟨.count 6, 236051655840⟩, ⟨.count 7, 63552368880⟩, ⟨.count 8, 16947298368⟩, ⟨.count 9, 5028319296⟩, ⟨.count 10, 1396755360⟩, ⟨.count 11, 465585120⟩, ⟨.path 14, 36871744⟩, ⟨.privateRow 11 11, 574423200⟩, ⟨.privateRow 14 7, 12609597⟩, ⟨.privateRow 14 9, 16812796⟩, ⟨.privateRow 14 14, 100876776⟩, ⟨.privateRow 15 7, 28821936⟩, ⟨.hall 14 3, 554268⟩, ⟨.hall 15 3, 1763580⟩, ⟨.hall 11 5, 4687452⟩, ⟨.hall 11 7, 165186⟩, ⟨.hall 10 8, 1320424⟩, ⟨.hall 11 10, 1142280⟩, ⟨.hall 9 15, 74053980⟩]
  caps := #[0, 0, 0, 12765497472, 3766066304, 566325760, 1218016800, 0, 87447360, 0, 170320800, 393397680, 239671744, 202800000, 115686077, 45349200, 0, 0, 0, 0, 0, 0] }

theorem case_49_28_14_checked :
    (Witness.linear .positive case_49_28_14).check 49 28 14 = true := by
  change case_49_28_14.check 49 28 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_28_15 : Certificate := {
  objectiveScale := 592612020000
  eta := 712242655886361600
  rows := #[⟨.count 2, 172125308505870720⟩, ⟨.count 3, 39829359046276800⟩, ⟨.count 4, 10412904325824000⟩, ⟨.count 5, 2725730838230400⟩, ⟨.count 6, 723543719698800⟩, ⟨.count 7, 198304575028560⟩, ⟨.count 8, 58189759467840⟩, ⟨.count 9, 19082471728320⟩, ⟨.count 10, 7067582121600⟩, ⟨.count 11, 1766895530400⟩, ⟨.path 12, 171146976000⟩, ⟨.privateRow 2 26, 4451516599289760⟩, ⟨.privateRow 4 22, 1301613040728000⟩, ⟨.privateRow 5 19, 78403044335616⟩, ⟨.privateRow 5 20, 454798909524960⟩, ⟨.privateRow 5 21, 1073958367722240⟩, ⟨.privateRow 6 17, 52638762676500⟩, ⟨.privateRow 6 18, 172272314214000⟩, ⟨.privateRow 6 19, 391440980630700⟩, ⟨.privateRow 6 20, 615075966304800⟩, ⟨.privateRow 7 15, 25704123073200⟩, ⟨.privateRow 7 16, 68653707442320⟩, ⟨.privateRow 7 17, 148690148534928⟩, ⟨.privateRow 7 18, 232376210506440⟩, ⟨.privateRow 7 19, 294011416258560⟩, ⟨.privateRow 8 13, 11245553844525⟩, ⟨.privateRow 8 14, 28274535380520⟩, ⟨.privateRow 8 15, 59465850684240⟩, ⟨.privateRow 8 16, 92337960418704⟩, ⟨.privateRow 8 17, 116475225776910⟩, ⟨.privateRow 8 18, 114210163867800⟩, ⟨.privateRow 9 10, 141351642432⟩, ⟨.privateRow 9 11, 4580840264000⟩, ⟨.privateRow 9 12, 11955993089040⟩, ⟨.privateRow 9 13, 25174054414080⟩, ⟨.privateRow 9 14, 39303609465120⟩, ⟨.privateRow 9 15, 49991364206784⟩, ⟨.privateRow 9 16, 44702456919120⟩, ⟨.privateRow 10 8, 144564179760⟩, ⟨.privateRow 10 9, 1890578217528⟩, ⟨.privateRow 10 10, 5123997038160⟩, ⟨.privateRow 10 11, 11021010870870⟩, ⟨.privateRow 10 12, 18628127163360⟩, ⟨.privateRow 10 13, 20466539893800⟩, ⟨.privateRow 11 6, 80313433200⟩, ⟨.privateRow 11 7, 846941659200⟩, ⟨.privateRow 11 8, 2296964189520⟩, ⟨.privateRow 11 9, 5282839161600⟩, ⟨.privateRow 11 10, 8954947801800⟩, ⟨.privateRow 12 4, 27183008160⟩, ⟨.privateRow 12 5, 412275623760⟩, ⟨.privateRow 12 6, 1140450751440⟩, ⟨.privateRow 12 7, 2668012250904⟩, ⟨.privateRow 12 8, 588965176800⟩, ⟨.privateRow 13 3, 217464065280⟩, ⟨.privateRow 13 4, 628229521920⟩, ⟨.privateRow 13 5, 321253732800⟩, ⟨.privateRow 14 1, 109379247120⟩, ⟨.privateRow 14 2, 117793035360⟩, ⟨.privateRow 15 0, 54689623560⟩, ⟨.hall 7 20, 161042711509680⟩, ⟨.hall 6 21, 773137264699800⟩, ⟨.hall 5 22, 2075922997948800⟩, ⟨.hall 4 23, 4421145628339440⟩, ⟨.hall 3 24, 7872155670322944⟩, ⟨.hall 2 25, 9816164808690240⟩, ⟨.assumptionRow 15, 736735263264⟩]
  caps := #[0, 23278687986153600, 158745747320160, 189759706840704, 0, 0, 169057608720, 0, 1958636092413, 0, 0, 1459971349200, 3083287326504, 801693154944, 1489725027648, 0, 592612020000, 0, 0, 0, 0, 0] }

theorem case_49_28_15_checked :
    (Witness.linear .conditional case_49_28_15).check 49 28 15 = true := by
  change case_49_28_15.check 49 28 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_28_16 : Certificate := {
  objectiveScale := 28052640000
  eta := 28535362815960000
  rows := #[⟨.count 2, 6962628527094240⟩, ⟨.count 3, 1676077100137440⟩, ⟨.count 4, 440545952246400⟩, ⟨.count 5, 116615105006400⟩, ⟨.count 6, 31804119547200⟩, ⟨.count 7, 8863925910840⟩, ⟨.count 8, 2591446777920⟩, ⟨.count 9, 815490244800⟩, ⟨.count 10, 271830081600⟩, ⟨.count 11, 67957520400⟩, ⟨.count 12, 81549024480⟩, ⟨.path 11, 8991102120⟩, ⟨.privateRow 2 26, 342424353791520⟩, ⟨.privateRow 4 22, 64413158169360⟩, ⟨.privateRow 5 19, 2167391850624⟩, ⟨.privateRow 5 20, 21556125470880⟩, ⟨.privateRow 5 21, 55912427450880⟩, ⟨.privateRow 6 17, 1349711863500⟩, ⟨.privateRow 6 18, 7597650780720⟩, ⟨.privateRow 6 19, 19895979878775⟩, ⟨.privateRow 6 20, 34945267156800⟩, ⟨.privateRow 7 15, 597378965040⟩, ⟨.privateRow 7 16, 2763228287820⟩, ⟨.privateRow 7 17, 7285499237016⟩, ⟨.privateRow 7 18, 13119199313220⟩, ⟨.privateRow 7 19, 18905782175280⟩, ⟨.privateRow 8 13, 228224006010⟩, ⟨.privateRow 8 14, 1022275271160⟩, ⟨.privateRow 8 15, 2760774266250⟩, ⟨.privateRow 8 16, 5126941864044⟩, ⟨.privateRow 8 17, 7542435295395⟩, ⟨.privateRow 8 18, 8765765048040⟩, ⟨.privateRow 9 11, 77521912160⟩, ⟨.privateRow 9 12, 382827364920⟩, ⟨.privateRow 9 13, 1084731468480⟩, ⟨.privateRow 9 14, 2102152631040⟩, ⟨.privateRow 9 15, 3202158361248⟩, ⟨.privateRow 9 16, 3918883676400⟩, ⟨.privateRow 9 17, 3449221702080⟩, ⟨.privateRow 10 9, 23105556936⟩, ⟨.privateRow 10 10, 142710792840⟩, ⟨.privateRow 10 11, 440874413595⟩, ⟨.privateRow 10 12, 910630773360⟩, ⟨.privateRow 10 13, 1459954063260⟩, ⟨.privateRow 10 14, 1889219067120⟩, ⟨.privateRow 10 15, 404347246380⟩, ⟨.privateRow 11 7, 4493059200⟩, ⟨.privateRow 11 8, 52512629400⟩, ⟨.privateRow 11 9, 184652252400⟩, ⟨.privateRow 11 10, 417784301550⟩, ⟨.privateRow 11 11, 720173203200⟩, ⟨.privateRow 11 12, 452020476600⟩, ⟨.privateRow 12 6, 17298277920⟩, ⟨.privateRow 12 7, 79510298868⟩, ⟨.privateRow 12 8, 201607310520⟩, ⟨.privateRow 12 9, 293066806725⟩, ⟨.privateRow 13 4, 3775417800⟩, ⟨.privateRow 13 5, 18945732960⟩, ⟨.privateRow 13 6, 130478439168⟩, ⟨.privateRow 13 7, 21142339680⟩, ⟨.privateRow 14 3, 12270107850⟩, ⟨.privateRow 14 4, 32125373280⟩, ⟨.privateRow 15 1, 4530501360⟩, ⟨.privateRow 15 2, 4908043140⟩, ⟨.hall 7 19, 987989084082⟩, ⟨.hall 8 19, 1378178513712⟩, ⟨.hall 7 20, 147241294200⟩, ⟨.hall 6 21, 59532332359500⟩, ⟨.hall 5 22, 135205918848000⟩, ⟨.hall 4 23, 261323848946160⟩, ⟨.hall 3 24, 439744959605952⟩, ⟨.hall 2 25, 561927144683520⟩, ⟨.assumptionRow 16, 25363794456⟩]
  caps := #[0, 483177214960440, 56167645694160, 953106462000, 0, 802955857704, 34841023932, 42390040836, 0, 0, 20711740203, 53313756372, 0, 25363794456, 98365445178, 25363794456, 283215245544, 28052640000, 0, 0, 0, 0] }

theorem case_49_28_16_checked :
    (Witness.linear .conditional case_49_28_16).check 49 28 16 = true := by
  change case_49_28_16.check 49 28 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_28_17 : Certificate := {
  objectiveScale := 573804000000
  eta := 499109436890064000
  rows := #[⟨.count 2, 121404998162448000⟩, ⟨.count 3, 29818771478496000⟩, ⟨.count 4, 7857009627667200⟩, ⟨.count 5, 2074228268112000⟩, ⟨.count 6, 553359554748000⟩, ⟨.count 7, 148606622564400⟩, ⟨.count 8, 40370885755200⟩, ⟨.count 9, 11565134380800⟩, ⟨.count 10, 4015671660000⟩, ⟨.count 11, 803134332000⟩, ⟨.count 12, 963761198400⟩, ⟨.path 11, 188584869200⟩, ⟨.privateRow 2 26, 10117083180204000⟩, ⟨.privateRow 4 22, 1297668758786400⟩, ⟨.privateRow 5 19, 23387271747840⟩, ⟨.privateRow 5 20, 414149603868000⟩, ⟨.privateRow 5 21, 1167507454713600⟩, ⟨.privateRow 6 17, 13050932895000⟩, ⟨.privateRow 6 18, 135381677230800⟩, ⟨.privateRow 6 19, 401098670973000⟩, ⟨.privateRow 6 20, 775515434694000⟩, ⟨.privateRow 7 15, 4872348280800⟩, ⟨.privateRow 7 16, 44721196720200⟩, ⟨.privateRow 7 17, 139766790683520⟩, ⟨.privateRow 7 18, 284336324672400⟩, ⟨.privateRow 7 19, 458348763272400⟩, ⟨.privateRow 8 13, 1370347953975⟩, ⟨.privateRow 8 14, 14617044842400⟩, ⟨.privateRow 8 15, 49419532562400⟩, ⟨.privateRow 8 16, 107122057202160⟩, ⟨.privateRow 8 17, 179972364622050⟩, ⟨.privateRow 8 18, 245009513548800⟩, ⟨.privateRow 9 11, 214169155200⟩, ⟨.privateRow 9 12, 4604636836800⟩, ⟨.privateRow 9 13, 17638359710400⟩, ⟨.privateRow 9 14, 41566663538400⟩, ⟨.privateRow 9 15, 73995443121600⟩, ⟨.privateRow 9 16, 105853104957600⟩, ⟨.privateRow 9 17, 116793579302400⟩, ⟨.privateRow 10 10, 1240396357200⟩, ⟨.privateRow 10 11, 6264447789600⟩, ⟨.privateRow 10 12, 16590460629600⟩, ⟨.privateRow 10 13, 31964746413600⟩, ⟨.privateRow 10 14, 48862692758880⟩, ⟨.privateRow 10 15, 59191000268400⟩, ⟨.privateRow 10 16, 18552403069200⟩, ⟨.privateRow 11 8, 233639078400⟩, ⟨.privateRow 11 9, 2084904276000⟩, ⟨.privateRow 11 10, 6744503083500⟩, ⟨.privateRow 11 11, 14508569556000⟩, ⟨.privateRow 11 12, 24179210874000⟩, ⟨.privateRow 11 13, 20939902401600⟩, ⟨.privateRow 12 6, 7301221200⟩, ⟨.privateRow 12 7, 594319405680⟩, ⟨.privateRow 12 8, 2677114440000⟩, ⟨.privateRow 12 9, 4758570917100⟩, ⟨.privateRow 12 10, 16980554448000⟩, ⟨.privateRow 13 5, 87614654400⟩, ⟨.privateRow 13 6, 985178113920⟩, ⟨.privateRow 13 7, 3236333900800⟩, ⟨.privateRow 13 8, 4377082109400⟩, ⟨.privateRow 14 4, 268928314200⟩, ⟨.privateRow 14 5, 1461704484240⟩, ⟨.privateRow 14 6, 1005405200800⟩, ⟨.privateRow 15 2, 29002073100⟩, ⟨.privateRow 15 3, 537856628400⟩, ⟨.privateRow 15 4, 174012438600⟩, ⟨.privateRow 16 1, 145010365500⟩, ⟨.hall 8 19, 175822167961440⟩, ⟨.hall 7 20, 684216908575200⟩, ⟨.hall 6 21, 1667197354914000⟩, ⟨.hall 5 22, 3382196545728000⟩, ⟨.hall 4 23, 6082082753947200⟩, ⟨.hall 3 24, 9789076693940544⟩, ⟨.hall 2 25, 12555559639022400⟩, ⟨.assumptionRow 17, 310943112480⟩]
  caps := #[0, 5113589362081200, 215330794053760, 237511533798000, 0, 3208830554160, 1514455389720, 390118004640, 0, 0, 0, 368842323920, 629220760740, 520050273120, 310943112480, 310943112480, 1898207069220, 5427096887520, 573804000000, 0, 0, 0] }

theorem case_49_28_17_checked :
    (Witness.linear .conditional case_49_28_17).check 49 28 17 = true := by
  change case_49_28_17.check 49 28 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_28_18 : Certificate := {
  objectiveScale := 34983000000
  eta := 28327832904571200
  rows := #[⟨.count 2, 7284299889746880⟩, ⟨.count 3, 1959519268586880⟩, ⟨.count 4, 534844631280960⟩, ⟨.count 5, 147562547932800⟩, ⟨.count 6, 41240947948200⟩, ⟨.count 7, 11693635873920⟩, ⟨.count 8, 3341038821120⟩, ⟨.count 9, 963761198400⟩, ⟨.count 10, 240940299600⟩, ⟨.count 11, 80313433200⟩, ⟨.path 11, 205132200⟩, ⟨.path 12, 10544788800⟩, ⟨.privateRow 5 19, 334103882112⟩, ⟨.privateRow 5 20, 30904609095360⟩, ⟨.privateRow 6 17, 116008292400⟩, ⟨.privateRow 6 18, 9431474172120⟩, ⟨.privateRow 6 19, 30169406542275⟩, ⟨.privateRow 7 16, 2871205236900⟩, ⟨.privateRow 7 17, 10155365916696⟩, ⟨.privateRow 7 18, 21299122484640⟩, ⟨.privateRow 8 14, 832773813300⟩, ⟨.privateRow 8 15, 3448346491590⟩, ⟨.privateRow 8 17, 30826303497990⟩, ⟨.privateRow 8 18, 4269105160320⟩, ⟨.privateRow 9 12, 235586070720⟩, ⟨.privateRow 9 13, 1135096522560⟩, ⟨.privateRow 9 14, 3064403662320⟩, ⟨.privateRow 9 16, 18806728941000⟩, ⟨.privateRow 9 17, 8673850785600⟩, ⟨.privateRow 10 11, 490915860435⟩, ⟨.privateRow 10 12, 1070463331080⟩, ⟨.privateRow 10 15, 15723362384730⟩, ⟨.privateRow 10 16, 7993863717840⟩, ⟨.privateRow 11 8, 14602442400⟩, ⟨.privateRow 11 12, 1271629359000⟩, ⟨.privateRow 11 14, 10208932542900⟩, ⟨.privateRow 12 6, 1460244240⟩, ⟨.privateRow 12 8, 86560033560⟩, ⟨.privateRow 12 9, 26101865790⟩, ⟨.privateRow 12 12, 1702644783840⟩, ⟨.privateRow 13 5, 5840976960⟩, ⟨.privateRow 13 6, 17133532416⟩, ⟨.privateRow 13 9, 624150109440⟩, ⟨.privateRow 13 11, 929494133568⟩, ⟨.privateRow 14 4, 12655450080⟩, ⟨.privateRow 14 5, 34802487720⟩, ⟨.privateRow 14 6, 25135130020⟩, ⟨.privateRow 14 8, 454918232340⟩, ⟨.privateRow 15 3, 9491587560⟩, ⟨.privateRow 15 5, 193347154000⟩, ⟨.privateRow 16 2, 23728968900⟩, ⟨.privateRow 16 10, 87006219300⟩, ⟨.hall 11 7, 793718730⟩, ⟨.hall 8 15, 8084664588⟩, ⟨.hall 7 16, 19207812624⟩, ⟨.hall 6 17, 36098957700⟩, ⟨.hall 5 19, 191482462080⟩]
  caps := #[0, 0, 43715824014720, 0, 1999372459968, 668747520480, 0, 76673731680, 264035135520, 0, 21281153400, 0, 158195267490, 2009854080, 217052101240, 2983350240, 0, 1539252000000, 314847000000, 34983000000, 0, 0] }

theorem case_49_28_18_checked :
    (Witness.linear .negative case_49_28_18).check 49 28 18 = true := by
  change case_49_28_18.check 49 28 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_29_1_checked :
    (Witness.rising).check 49 29 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_29_2_checked :
    (Witness.rising).check 49 29 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_29_3_checked :
    (Witness.rising).check 49 29 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_29_4_checked :
    (Witness.rising).check 49 29 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_29_5_checked :
    (Witness.rising).check 49 29 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_29_6_checked :
    (Witness.rising).check 49 29 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_29_7_checked :
    (Witness.rising).check 49 29 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_29_8_checked :
    (Witness.rising).check 49 29 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_29_9_checked :
    (Witness.rising).check 49 29 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_29_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_29_10_checked :
    (Witness.linear .positive case_49_29_10).check 49 29 10 = true := by
  change case_49_29_10.check 49 29 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_29_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_29_11_checked :
    (Witness.linear .positive case_49_29_11).check 49 29 11 = true := by
  change case_49_29_11.check 49 29 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_29_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_29_12_checked :
    (Witness.linear .positive case_49_29_12).check 49 29 12 = true := by
  change case_49_29_12.check 49 29 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_29_13 : Certificate := {
  objectiveScale := 40222000000
  eta := 71628948915844320
  rows := #[⟨.count 2, 15463162923848640⟩, ⟨.count 3, 3173569250211360⟩, ⟨.count 4, 696606594203520⟩, ⟨.count 5, 148780635003000⟩, ⟨.count 6, 33828018063840⟩, ⟨.count 7, 7830559737000⟩, ⟨.count 8, 1927522396800⟩, ⟨.count 9, 433692539280⟩, ⟨.count 10, 131421981600⟩, ⟨.path 13, 14196709800⟩, ⟨.hall 12 3, 35432397⟩, ⟨.hall 12 5, 3893670⟩, ⟨.hall 10 7, 70943040⟩, ⟨.hall 9 15, 1042458417⟩, ⟨.hall 6 18, 13992567264⟩]
  caps := #[0, 370516775854680, 7773258671360, 4508183119440, 0, 782016235000, 359625706440, 0, 0, 138232927560, 20831654480, 54418709800, 40222000000, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_29_13_checked :
    (Witness.linear .positive case_49_29_13).check 49 29 13 = true := by
  change case_49_29_13.check 49 29 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_29_14 : Certificate := {
  objectiveScale := 4258800000
  eta := 11331133161828480
  rows := #[⟨.count 2, 2534595575672160⟩, ⟨.count 3, 617674552054560⟩, ⟨.count 4, 147840967834560⟩, ⟨.count 5, 34715481500700⟩, ⟨.count 6, 8770226905440⟩, ⟨.count 7, 2244760457940⟩, ⟨.count 8, 578256719040⟩, ⟨.count 9, 168658209720⟩, ⟨.count 10, 43807327200⟩, ⟨.count 11, 24094029960⟩, ⟨.path 12, 1742115375⟩, ⟨.hall 11 5, 88112310⟩, ⟨.hall 10 7, 48338640⟩, ⟨.hall 11 7, 43575455⟩, ⟨.hall 9 11, 18999288⟩]
  caps := #[0, 0, 0, 0, 82501154190, 19312593300, 0, 0, 0, 0, 3618403425, 0, 6000915375, 4258800000, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_29_14_checked :
    (Witness.linear .positive case_49_29_14).check 49 29 14 = true := by
  change case_49_29_14.check 49 29 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_29_15 : Certificate := {
  objectiveScale := 754233480000
  eta := 2077374413001888000
  rows := #[⟨.count 2, 431875206913550400⟩, ⟨.count 3, 99313075007546400⟩, ⟨.count 4, 22295865732940800⟩, ⟨.count 5, 5359583108880000⟩, ⟨.count 6, 1339895777220000⟩, ⟨.count 7, 334973944305000⟩, ⟨.count 8, 90700637227200⟩, ⟨.count 9, 24736537425600⟩, ⟨.count 10, 5621940324000⟩, ⟨.path 11, 486119874240⟩, ⟨.privateRow 2 27, 16400324313172800⟩, ⟨.privateRow 4 22, 1071916621776000⟩, ⟨.privateRow 4 23, 3715977622156800⟩, ⟨.privateRow 5 20, 694066012599960⟩, ⟨.privateRow 5 21, 1400191087194900⟩, ⟨.privateRow 5 22, 2760185301073200⟩, ⟨.privateRow 6 17, 44025146965800⟩, ⟨.privateRow 6 18, 281378113216200⟩, ⟨.privateRow 6 19, 561862962580920⟩, ⟨.privateRow 6 20, 1022787109944600⟩, ⟨.privateRow 6 21, 1397957927566200⟩, ⟨.privateRow 7 15, 35890065461250⟩, ⟨.privateRow 7 16, 112113728298000⟩, ⟨.privateRow 7 17, 220444757633100⟩, ⟨.privateRow 7 18, 402351560530920⟩, ⟨.privateRow 7 19, 534522708269550⟩, ⟨.privateRow 7 20, 583811731503000⟩, ⟨.privateRow 8 13, 19697613135200⟩, ⟨.privateRow 8 14, 48571221924225⟩, ⟨.privateRow 8 15, 89080982991000⟩, ⟨.privateRow 8 16, 163364215914900⟩, ⟨.privateRow 8 17, 221185872147240⟩, ⟨.privateRow 8 18, 239119861780800⟩, ⟨.privateRow 8 19, 113719359553800⟩, ⟨.privateRow 9 10, 437262025200⟩, ⟨.privateRow 9 11, 8863925910840⟩, ⟨.privateRow 9 12, 22446117293600⟩, ⟨.privateRow 9 13, 39423856522050⟩, ⟨.privateRow 9 14, 70479499490400⟩, ⟨.privateRow 9 15, 98602586682600⟩, ⟨.privateRow 9 16, 57443736910560⟩, ⟨.privateRow 10 8, 468495027000⟩, ⟨.privateRow 10 9, 3986466775200⟩, ⟨.privateRow 10 10, 10513028405880⟩, ⟨.privateRow 10 11, 19239529108800⟩, ⟨.privateRow 10 12, 34012738960200⟩, ⟨.privateRow 10 13, 25941238923600⟩, ⟨.privateRow 11 6, 302719863600⟩, ⟨.privateRow 11 7, 1920829610700⟩, ⟨.privateRow 11 8, 5161963388400⟩, ⟨.privateRow 11 9, 10063273179960⟩, ⟨.privateRow 11 10, 9994560576000⟩, ⟨.privateRow 12 4, 147241294200⟩, ⟨.privateRow 12 5, 1057116984000⟩, ⟨.privateRow 12 6, 2805764661700⟩, ⟨.privateRow 12 7, 3185766183600⟩, ⟨.privateRow 13 3, 588965176800⟩, ⟨.privateRow 13 4, 951405285600⟩, ⟨.privateRow 14 1, 255218243280⟩, ⟨.hall 6 22, 859863550946400⟩, ⟨.hall 5 23, 3372071039337000⟩, ⟨.hall 4 24, 8626784972053248⟩, ⟨.hall 3 25, 17837104861976400⟩, ⟨.hall 2 26, 27738820134625600⟩, ⟨.assumptionRow 15, 964353089700⟩]
  caps := #[0, 17379666317613600, 935490869913600, 726791951886000, 2248776129600, 12785812799760, 16461576691560, 0, 1603418571755, 4831350924400, 2344286886480, 8020220528040, 964353089700, 8873215520400, 4102076018040, 8840682150300, 754233480000, 0, 0, 0, 0] }

theorem case_49_29_15_checked :
    (Witness.linear .conditional case_49_29_15).check 49 29 15 = true := by
  change case_49_29_15.check 49 29 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_29_16 : Certificate := {
  objectiveScale := 384813000000
  eta := 1068363983829542400
  rows := #[⟨.count 2, 220232926491177600⟩, ⟨.count 3, 50372424676173600⟩, ⟨.count 4, 11392942380019200⟩, ⟨.count 5, 2555372660841000⟩, ⟨.count 6, 620180331170400⟩, ⟨.count 7, 155045082792600⟩, ⟨.count 8, 38871701668800⟩, ⟨.count 9, 10601373182400⟩, ⟨.count 10, 2409402996000⟩, ⟨.path 10, 369900726624⟩, ⟨.privateRow 2 27, 10543065629896800⟩, ⟨.privateRow 4 22, 459392837904000⟩, ⟨.privateRow 4 23, 2051954675971200⟩, ⟨.privateRow 5 20, 287120523690000⟩, ⟨.privateRow 5 21, 742206553738650⟩, ⟨.privateRow 5 22, 1621273890436200⟩, ⟨.privateRow 6 17, 1367240589000⟩, ⟨.privateRow 6 18, 127290098835900⟩, ⟨.privateRow 6 19, 283292250040800⟩, ⟨.privateRow 6 20, 592903881419850⟩, ⟨.privateRow 6 21, 912405219726000⟩, ⟨.privateRow 7 15, 5024609164575⟩, ⟨.privateRow 7 16, 45939283790400⟩, ⟨.privateRow 7 17, 110609763650100⟩, ⟨.privateRow 7 18, 227563523633160⟩, ⟨.privateRow 7 19, 350697211078500⟩, ⟨.privateRow 7 20, 444900087660600⟩, ⟨.privateRow 8 13, 3141147609600⟩, ⟨.privateRow 8 14, 17392877877375⟩, ⟨.privateRow 8 15, 42342389317800⟩, ⟨.privateRow 8 16, 91804946933700⟩, ⟨.privateRow 8 17, 143471917068480⟩, ⟨.privateRow 8 18, 184530151956150⟩, ⟨.privateRow 8 19, 184346100338400⟩, ⟨.privateRow 9 11, 1354619906640⟩, ⟨.privateRow 9 12, 6969421258800⟩, ⟨.privateRow 9 13, 17006369480100⟩, ⟨.privateRow 9 14, 38030322844800⟩, ⟨.privateRow 9 15, 63313756506000⟩, ⟨.privateRow 9 16, 83927537694000⟩, ⟨.privateRow 9 17, 61988584858200⟩, ⟨.privateRow 10 9, 459976935600⟩, ⟨.privateRow 10 10, 2843095535280⟩, ⟨.privateRow 10 11, 7335293565600⟩, ⟨.privateRow 10 12, 16865820972000⟩, ⟨.privateRow 10 13, 29670076893600⟩, ⟨.privateRow 10 14, 38630761369200⟩, ⟨.privateRow 11 7, 100391791500⟩, ⟨.privateRow 11 8, 1138990507200⟩, ⟨.privateRow 11 9, 3349070164440⟩, ⟨.privateRow 11 10, 3828273649200⟩, ⟨.privateRow 11 11, 23913324735300⟩, ⟨.privateRow 12 6, 417183666900⟩, ⟨.privateRow 12 7, 1579497519600⟩, ⟨.privateRow 12 8, 4299445790640⟩, ⟨.privateRow 12 9, 3795553361600⟩, ⟨.privateRow 13 4, 101936280600⟩, ⟨.privateRow 13 5, 736206471000⟩, ⟨.privateRow 13 6, 1967679113400⟩, ⟨.privateRow 14 3, 252413647200⟩, ⟨.privateRow 14 4, 410172176700⟩, ⟨.privateRow 15 1, 136724058900⟩, ⟨.hall 7 21, 127116086397300⟩, ⟨.hall 6 22, 897813394077600⟩, ⟨.hall 5 23, 2578103035633125⟩, ⟨.hall 4 24, 5744248045151616⟩, ⟨.hall 3 25, 10918530930106800⟩, ⟨.hall 2 26, 16313550110457600⟩, ⟨.assumptionRow 16, 374089031316⟩]
  caps := #[0, 0, 1737936801057600, 173705182351272, 8218358885880, 10315457360208, 7490738303334, 861983044065, 868098462660, 951777924240, 888866169048, 2385951985872, 921556411380, 374089031316, 6266764363860, 374089031316, 4243666968684, 384813000000, 0, 0, 0] }

theorem case_49_29_16_checked :
    (Witness.linear .conditional case_49_29_16).check 49 29 16 = true := by
  change case_49_29_16.check 49 29 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_29_17 : Certificate := {
  objectiveScale := 17882956872000000
  eta := 33769182664629122911200
  rows := #[⟨.count 2, 7597194861598708766400⟩, ⟨.count 3, 1707626367974021695200⟩, ⟨.count 4, 379928075467609468800⟩, ⟨.count 5, 84561329746612719000⟩, ⟨.count 6, 19816392425468839200⟩, ⟨.count 7, 4612436167997057400⟩, ⟨.count 8, 1156394252945131200⟩, ⟨.count 9, 315380250803217600⟩, ⟨.count 10, 143354659456008000⟩, ⟨.count 11, 78845062700804400⟩, ⟨.path 9, 9533405304423000⟩, ⟨.path 10, 9476247550955328⟩, ⟨.privateRow 2 27, 906087460557644164800⟩, ⟨.privateRow 3 24, 52919638009776938400⟩, ⟨.privateRow 4 22, 32287053175979401800⟩, ⟨.privateRow 4 23, 101359708383145212000⟩, ⟨.privateRow 5 20, 13803142310154156960⟩, ⟨.privateRow 5 21, 35319302879014504350⟩, ⟨.privateRow 5 22, 80404442829775864800⟩, ⟨.privateRow 6 18, 5096457247354773300⟩, ⟨.privateRow 6 19, 12641491719695638800⟩, ⟨.privateRow 6 20, 28713838737191557950⟩, ⟨.privateRow 6 21, 48174333310191488400⟩, ⟨.privateRow 7 15, 61011060423241500⟩, ⟨.privateRow 7 16, 1659500843512168800⟩, ⟨.privateRow 7 17, 4567694723686680300⟩, ⟨.privateRow 7 18, 10620805398477880320⟩, ⟨.privateRow 7 19, 18309419233014774150⟩, ⟨.privateRow 7 20, 26096464245034497600⟩, ⟨.privateRow 8 13, 24821593813216200⟩, ⟨.privateRow 8 14, 542059806068030250⟩, ⟨.privateRow 8 15, 1623832838957043000⟩, ⟨.privateRow 8 16, 4064901010352582400⟩, ⟨.privateRow 8 17, 7308937312364567880⟩, ⟨.privateRow 8 18, 10752495425822200050⟩, ⟨.privateRow 8 19, 12729097344918754800⟩, ⟨.privateRow 9 12, 174237854610419600⟩, ⟨.privateRow 9 13, 585862618679588250⟩, ⟨.privateRow 9 14, 1585661816538399600⟩, ⟨.privateRow 9 15, 3083718007853683200⟩, ⟨.privateRow 9 16, 4758737562119661120⟩, ⟨.privateRow 9 17, 5972513499585933300⟩, ⟨.privateRow 9 18, 3825445634742732000⟩, ⟨.privateRow 10 10, 42289624539522360⟩, ⟨.privateRow 10 11, 212642744859745200⟩, ⟨.privateRow 10 12, 640616134444035750⟩, ⟨.privateRow 10 13, 1361869264832076000⟩, ⟨.privateRow 10 14, 2275755218864127000⟩, ⟨.privateRow 10 15, 3024783314521768800⟩, ⟨.privateRow 11 8, 7819345061236800⟩, ⟨.privateRow 11 9, 68093463241603800⟩, ⟨.privateRow 11 10, 266798949543126000⟩, ⟨.privateRow 11 11, 557291238635231100⟩, ⟨.privateRow 11 12, 1327054561821331200⟩, ⟨.privateRow 11 13, 643901345389902600⟩, ⟨.privateRow 12 7, 18317539819378800⟩, ⟨.privateRow 12 8, 103374637763276880⟩, ⟨.privateRow 12 9, 312460063295780400⟩, ⟨.privateRow 12 10, 579292196787854550⟩, ⟨.privateRow 13 5, 2190140630577900⟩, ⟨.privateRow 13 6, 37033287026135400⟩, ⟨.privateRow 13 7, 147177450374834880⟩, ⟨.privateRow 13 8, 154769937894171600⟩, ⟨.privateRow 14 4, 8134808056432200⟩, ⟨.privateRow 14 5, 66557520461718000⟩, ⟨.privateRow 14 6, 29285309003155920⟩, ⟨.privateRow 15 3, 18981218798341800⟩, ⟨.privateRow 15 4, 5176696035911400⟩, ⟨.hall 7 21, 17929486720379133900⟩, ⟨.hall 6 22, 64202734679817333600⟩, ⟨.hall 5 23, 154851155609222197125⟩, ⟨.hall 4 24, 314766310581654003072⟩, ⟨.hall 3 25, 569208789324673898400⟩, ⟨.hall 2 26, 851877099669579984000⟩, ⟨.assumptionRow 17, 11541673912883400⟩]
  caps := #[0, 0, 7799732974568106000, 1583012777681072232, 4030094826890807400, 269902026094359582, 88156010880657720, 79642387413076488, 99637986939631140, 28637682957013680, 78926460248124918, 0, 63136479878201730, 96966087790932360, 11541673912883400, 60774912816618000, 1023892109725399200, 185170851679116600, 17882956872000000, 0, 0] }

theorem case_49_29_17_checked :
    (Witness.linear .conditional case_49_29_17).check 49 29 17 = true := by
  change case_49_29_17.check 49 29 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_29_18 : Certificate := {
  objectiveScale := 8862891730192500000
  eta := 70559142057892616538009600
  rows := #[⟨.count 2, 10792763505565811411241600⟩, ⟨.count 3, 1586033346696051139286400⟩, ⟨.count 4, 218449356216385809715200⟩, ⟨.count 5, 26547664817963553264000⟩, ⟨.count 6, 2654766481796355326400⟩, ⟨.count 7, 189626177271168237600⟩, ⟨.path 6, 698818604621769918000⟩, ⟨.path 7, 160357324880568816000⟩, ⟨.privateRow 2 27, 812358543429684729878400⟩, ⟨.privateRow 3 24, 108887564904155272435200⟩, ⟨.privateRow 4 21, 11150019223544692370880⟩, ⟨.privateRow 4 22, 49018366824596989419600⟩, ⟨.privateRow 4 23, 95950845699211128225600⟩, ⟨.privateRow 5 18, 731415255188791773600⟩, ⟨.privateRow 5 19, 6715927111687208415000⟩, ⟨.privateRow 5 20, 16402664333956052552400⟩, ⟨.privateRow 5 21, 32710515579276520986000⟩, ⟨.privateRow 5 22, 67822962737321172981600⟩, ⟨.privateRow 6 16, 675543256528536846450⟩, ⟨.privateRow 6 17, 2438050850629305912000⟩, ⟨.privateRow 6 18, 5636111380004167062000⟩, ⟨.privateRow 6 19, 11105773115514753115440⟩, ⟨.privateRow 6 20, 23600557979540813571300⟩, ⟨.privateRow 6 21, 38367696534533040074400⟩, ⟨.privateRow 7 13, 29798399285469294480⟩, ⟨.privateRow 7 14, 275409447941458630800⟩, ⟨.privateRow 7 15, 848238525114779348550⟩, ⟨.privateRow 7 16, 1962050446458822376800⟩, ⟨.privateRow 7 17, 3914426087954830047600⟩, ⟨.privateRow 7 18, 8443782779346162808560⟩, ⟨.privateRow 7 19, 14296459293551291056200⟩, ⟨.privateRow 7 20, 20538320962060578877200⟩, ⟨.privateRow 8 10, 607776209202462300⟩, ⟨.privateRow 8 11, 15249657612716326800⟩, ⟨.privateRow 8 12, 98459745890798892600⟩, ⟨.privateRow 8 13, 299025894927611451600⟩, ⟨.privateRow 8 14, 703804850256451343400⟩, ⟨.privateRow 8 15, 1436782958554620877200⟩, ⟨.privateRow 8 16, 3171376259618448281400⟩, ⟨.privateRow 8 17, 5586678914989033461600⟩, ⟨.privateRow 8 18, 8363608414835083710300⟩, ⟨.privateRow 8 19, 10254400201663943925600⟩, ⟨.privateRow 9 8, 374016128739976800⟩, ⟨.privateRow 9 9, 6077762092024623000⟩, ⟨.privateRow 9 10, 34477486776576043200⟩, ⟨.privateRow 9 11, 108427275721719274320⟩, ⟨.privateRow 9 12, 264720304452628024000⟩, ⟨.privateRow 9 13, 555507455211050542200⟩, ⟨.privateRow 9 14, 1260701508231393228000⟩, ⟨.privateRow 9 15, 2324946592269152451600⟩, ⟨.privateRow 9 16, 3648602139084221679360⟩, ⟨.privateRow 9 17, 4774689899494543828800⟩, ⟨.privateRow 9 18, 3826559013138702640800⟩, ⟨.privateRow 10 7, 2142092373692594400⟩, ⟨.privateRow 10 8, 12266028949358784600⟩, ⟨.privateRow 10 9, 40866671389018456800⟩, ⟨.privateRow 10 10, 105023728950185485440⟩, ⟨.privateRow 10 11, 228965873721363979200⟩, ⟨.privateRow 10 12, 536555887960464672300⟩, ⟨.privateRow 10 13, 1041712636177976162400⟩, ⟨.privateRow 10 14, 1269036724814741282400⟩, ⟨.privateRow 10 15, 3345642274511590653600⟩, ⟨.privateRow 11 5, 852465332387869200⟩, ⟨.privateRow 11 6, 4896211139868787200⟩, ⟨.privateRow 11 7, 16575714796430790000⟩, ⟨.privateRow 11 8, 44483190980966992800⟩, ⟨.privateRow 11 9, 101841191709270773760⟩, ⟨.privateRow 11 10, 248414712415842772800⟩, ⟨.privateRow 11 11, 509205958546353868800⟩, ⟨.privateRow 11 12, 899635080779997962400⟩, ⟨.privateRow 11 13, 744581108655671086800⟩, ⟨.privateRow 12 3, 324147311574646560⟩, ⟨.privateRow 12 4, 2083804145837013600⟩, ⟨.privateRow 12 5, 7480322574799536000⟩, ⟨.privateRow 12 6, 20664391112883718200⟩, ⟨.privateRow 12 7, 49506134858673292800⟩, ⟨.privateRow 12 8, 126903672481474128240⟩, ⟨.privateRow 12 9, 276065460357740653600⟩, ⟨.privateRow 12 10, 469811009713503357900⟩, ⟨.privateRow 13 1, 455832156901846725⟩, ⟨.privateRow 13 2, 1458662902085909520⟩, ⟨.privateRow 13 3, 4167608291674027200⟩, ⟨.privateRow 13 4, 10659459669089338800⟩, ⟨.privateRow 13 5, 26742153204908341200⟩, ⟨.privateRow 13 6, 72270116512438244400⟩, ⟨.privateRow 13 7, 168475565190922549560⟩, ⟨.privateRow 13 8, 54294674688753298800⟩, ⟨.privateRow 14 0, 846545434246286775⟩, ⟨.privateRow 14 1, 2708945389588117680⟩, ⟨.privateRow 14 2, 7739843970251764800⟩, ⟨.privateRow 14 3, 16670433166696108800⟩, ⟨.privateRow 14 4, 47406544317792059400⟩, ⟨.privateRow 14 5, 34477486776576043200⟩, ⟨.privateRow 15 0, 12641745151411215840⟩, ⟨.privateRow 15 1, 11287272456617157000⟩, ⟨.privateRow 15 2, 7293314510429547600⟩, ⟨.privateRow 16 0, 6772363473970294200⟩, ⟨.hall 7 21, 15402817217435347299600⟩, ⟨.hall 6 22, 52064752585540322628000⟩, ⟨.hall 5 23, 124382920653806915850750⟩, ⟨.hall 4 24, 257406158074974612447744⟩, ⟨.hall 3 25, 489746069375344121340000⟩, ⟨.hall 2 26, 789434845555125725155200⟩]
  caps := #[0, 92797604432473116290400, 15889419966555801151200, 6823688113172378104800, 0, 646069480447269415680, 23789597925125638320, 0, 109620727187062291200, 0, 42664645149482560260, 0, 51414031496924673500, 0, 16865150994137990115, 0, 428057513820248512200, 478596153430395000000, 88628917301925000000, 8862891730192500000, 0] }

theorem case_49_29_18_checked :
    (Witness.linear .negative case_49_29_18).check 49 29 18 = true := by
  change case_49_29_18.check 49 29 18 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_30_1_checked :
    (Witness.rising).check 49 30 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_30_2_checked :
    (Witness.rising).check 49 30 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_30_3_checked :
    (Witness.rising).check 49 30 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_30_4_checked :
    (Witness.rising).check 49 30 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_30_5_checked :
    (Witness.rising).check 49 30 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_30_6_checked :
    (Witness.rising).check 49 30 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_30_7_checked :
    (Witness.rising).check 49 30 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_30_8_checked :
    (Witness.rising).check 49 30 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_30_9_checked :
    (Witness.rising).check 49 30 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_30_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_30_10_checked :
    (Witness.linear .positive case_49_30_10).check 49 30 10 = true := by
  change case_49_30_10.check 49 30 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_30_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_30_11_checked :
    (Witness.linear .positive case_49_30_11).check 49 30 11 = true := by
  change case_49_30_11.check 49 30 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_30_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_30_12_checked :
    (Witness.linear .positive case_49_30_12).check 49 30 12 = true := by
  change case_49_30_12.check 49 30 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_30_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_30_13_checked :
    (Witness.linear .positive case_49_30_13).check 49 30 13 = true := by
  change case_49_30_13.check 49 30 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_30_14 : Certificate := {
  objectiveScale := 1206660000
  eta := 7738681169419200
  rows := #[⟨.count 2, 1640821287705600⟩, ⟨.count 3, 328535484076800⟩, ⟨.count 4, 71345099826000⟩, ⟨.count 5, 14617044842400⟩, ⟨.count 6, 3281377413600⟩, ⟨.count 7, 696049754400⟩, ⟨.count 8, 160626866400⟩, ⟨.count 9, 43807327200⟩, ⟨.count 10, 14602442400⟩, ⟨.path 10, 2037690720⟩, ⟨.path 11, 164542014⟩, ⟨.hall 11 6, 12744875⟩, ⟨.hall 10 9, 7042140⟩, ⟨.hall 11 9, 6568800⟩, ⟨.hall 8 11, 2304600⟩, ⟨.hall 9 16, 241831200⟩]
  caps := #[0, 23505916592340, 2821559830050, 696152898636, 124028046480, 29666274456, 0, 4377331530, 1493977680, 0, 0, 2577862014, 1206660000, 1206660000, 0, 0, 0, 0, 0, 0] }

theorem case_49_30_14_checked :
    (Witness.linear .positive case_49_30_14).check 49 30 14 = true := by
  change case_49_30_14.check 49 30 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_30_15 : Certificate := {
  objectiveScale := 351351000000
  eta := 1672833079943625600
  rows := #[⟨.count 2, 342584552319609600⟩, ⟨.count 3, 69460197091084800⟩, ⟨.count 4, 15757174340107200⟩, ⟨.count 5, 3376537358594400⟩, ⟨.count 6, 826907108227200⟩, ⟨.count 7, 197892299404800⟩, ⟨.count 8, 49473074851200⟩, ⟨.count 9, 13492656777600⟩, ⟨.count 10, 6746328388800⟩, ⟨.path 10, 129898248480⟩, ⟨.path 11, 226099773900⟩, ⟨.privateRow 2 28, 21867099084230400⟩, ⟨.privateRow 3 25, 2429677676025600⟩, ⟨.privateRow 3 26, 9004099622918400⟩, ⟨.privateRow 4 23, 1969646792513400⟩, ⟨.privateRow 4 24, 3483729020772000⟩, ⟨.privateRow 4 25, 5949137250856800⟩, ⟨.privateRow 5 20, 200091102731520⟩, ⟨.privateRow 5 21, 776067634165824⟩, ⟨.privateRow 5 22, 1358654318101080⟩, ⟨.privateRow 5 23, 2301047681412480⟩, ⟨.privateRow 5 24, 2626195723351200⟩, ⟨.privateRow 6 18, 147115087376400⟩, ⟨.privateRow 6 19, 305623846327800⟩, ⟨.privateRow 6 20, 518348252101680⟩, ⟨.privateRow 6 21, 869975186780700⟩, ⟨.privateRow 6 22, 1038738250149600⟩, ⟨.privateRow 6 23, 905386718035800⟩, ⟨.privateRow 7 15, 10405051456800⟩, ⟨.privateRow 7 16, 65375134624800⟩, ⟨.privateRow 7 17, 131759923838400⟩, ⟨.privateRow 7 18, 204665398938000⟩, ⟨.privateRow 7 19, 339950700048960⟩, ⟨.privateRow 7 20, 294188105811600⟩, ⟨.privateRow 7 21, 603100341043200⟩, ⟨.privateRow 8 13, 8966994816780⟩, ⟨.privateRow 8 14, 28630251650000⟩, ⟨.privateRow 8 15, 57460915061550⟩, ⟨.privateRow 8 16, 89228224285200⟩, ⟨.privateRow 8 17, 141891527177400⟩, ⟨.privateRow 8 18, 173980313226720⟩, ⟨.privateRow 8 19, 55399536942750⟩, ⟨.privateRow 9 10, 62466003600⟩, ⟨.privateRow 9 11, 5315289033600⟩, ⟨.privateRow 9 12, 13867452799200⟩, ⟨.privateRow 9 13, 26485585526400⟩, ⟨.privateRow 9 14, 15554034896400⟩, ⟨.privateRow 9 15, 119613473179200⟩, ⟨.privateRow 10 8, 155684501280⟩, ⟨.privateRow 10 9, 2754750758760⟩, ⟨.privateRow 10 10, 7420961227680⟩, ⟨.privateRow 10 11, 13695046629264⟩, ⟨.privateRow 10 12, 21588250844160⟩, ⟨.privateRow 10 13, 9444859744320⟩, ⟨.privateRow 11 6, 107084577600⟩, ⟨.privateRow 11 7, 1441523160000⟩, ⟨.privateRow 11 8, 4185222241200⟩, ⟨.privateRow 11 9, 8177367744000⟩, ⟨.privateRow 11 10, 1274306473440⟩, ⟨.privateRow 12 4, 68712603960⟩, ⟨.privateRow 12 5, 883447765200⟩, ⟨.privateRow 12 6, 2616364535400⟩, ⟨.privateRow 12 7, 257672264850⟩, ⟨.privateRow 13 3, 588965176800⟩, ⟨.privateRow 13 4, 252413647200⟩, ⟨.privateRow 14 1, 239267103075⟩, ⟨.hall 5 24, 658156805770464⟩, ⟨.hall 4 25, 2374707592857600⟩, ⟨.hall 3 26, 5812170126963200⟩, ⟨.hall 2 27, 11454194758406400⟩, ⟨.assumptionRow 15, 469485244800⟩]
  caps := #[0, 0, 0, 343173244685700, 0, 62630161707828, 0, 5908582791540, 0, 3942493671480, 0, 10277216616300, 469485244800, 7544894385600, 0, 4449428755200, 351351000000, 0, 0, 0] }

theorem case_49_30_15_checked :
    (Witness.linear .conditional case_49_30_15).check 49 30 15 = true := by
  change case_49_30_15.check 49 30 15 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_30_16 : Certificate := {
  objectiveScale := 88915235409000000
  eta := 554964539114107131609600
  rows := #[⟨.count 2, 106196917978625438764800⟩, ⟨.count 3, 20251973921920031491200⟩, ⟨.count 4, 4193972211442394581200⟩, ⟨.count 5, 831237735601195322400⟩, ⟨.count 6, 172724724280767859200⟩, ⟨.count 7, 37783533436417969200⟩, ⟨.count 8, 7750468397213942400⟩, ⟨.count 9, 1585323081248306400⟩, ⟨.path 9, 299403403160621760⟩, ⟨.privateRow 2 28, 7279627442083195399200⟩, ⟨.privateRow 3 25, 772463350255656259200⟩, ⟨.privateRow 3 26, 2846359518876820346400⟩, ⟨.privateRow 4 23, 573837414065597907225⟩, ⟨.privateRow 4 24, 1073682075151543958100⟩, ⟨.privateRow 4 25, 1936406088616420921500⟩, ⟨.privateRow 5 20, 49538410505525781840⟩, ⟨.privateRow 5 21, 217633152593767502592⟩, ⟨.privateRow 5 22, 408691886670587700180⟩, ⟨.privateRow 5 23, 746434693888346102640⟩, ⟨.privateRow 5 24, 925696569192240245400⟩, ⟨.privateRow 6 18, 33671040001161591600⟩, ⟨.privateRow 6 19, 82014257102065988700⟩, ⟨.privateRow 6 20, 152933349623596542000⟩, ⟨.privateRow 6 21, 280902578940988354350⟩, ⟨.privateRow 6 22, 373937033295342917400⟩, ⟨.privateRow 6 23, 372887490699886862700⟩, ⟨.privateRow 7 15, 1199477251949776800⟩, ⟨.privateRow 7 16, 14584028702793199650⟩, ⟨.privateRow 7 17, 33572181985891005600⟩, ⟨.privateRow 7 18, 59097321528756310800⟩, ⟨.privateRow 7 19, 109198563667889295600⟩, ⟨.privateRow 7 20, 148642911760853109600⟩, ⟨.privateRow 7 21, 161514225349083406800⟩, ⟨.privateRow 7 22, 107330147179275220200⟩, ⟨.privateRow 8 13, 944588335910449230⟩, ⟨.privateRow 8 14, 5893585343714768700⟩, ⟨.privateRow 8 15, 14108274504303504525⟩, ⟨.privateRow 8 16, 24877619542842966900⟩, ⟨.privateRow 8 17, 45130331604610352100⟩, ⟨.privateRow 8 18, 63408519574706566260⟩, ⟨.privateRow 8 19, 71389080002462797575⟩, ⟨.privateRow 8 20, 14532128244776142000⟩, ⟨.privateRow 9 11, 464387569254554400⟩, ⟨.privateRow 9 12, 2483672827289013360⟩, ⟨.privateRow 9 13, 6126001536181727200⟩, ⟨.privateRow 9 14, 11251390201637285700⟩, ⟨.privateRow 9 15, 20684691631525521600⟩, ⟨.privateRow 9 16, 29739486690824710800⟩, ⟨.privateRow 9 17, 15289560383594777280⟩, ⟨.privateRow 10 9, 184954359478969080⟩, ⟨.privateRow 10 10, 1095314128862466240⟩, ⟨.privateRow 10 11, 2853581546246951520⟩, ⟨.privateRow 10 12, 3945693002218007040⟩, ⟨.privateRow 10 13, 13653595037251038870⟩, ⟨.privateRow 10 14, 7654845735170393760⟩, ⟨.privateRow 11 7, 54199079700796800⟩, ⟨.privateRow 11 8, 499083192244837200⟩, ⟨.privateRow 11 9, 1457216165591877600⟩, ⟨.privateRow 11 10, 2959269751663505280⟩, ⟨.privateRow 11 11, 4442819005473648800⟩, ⟨.privateRow 12 6, 223571203765786800⟩, ⟨.privateRow 12 7, 807340458043119000⟩, ⟨.privateRow 12 8, 1739451714147447300⟩, ⟨.privateRow 13 4, 88972213743527400⟩, ⟨.privateRow 13 5, 447142407531573600⟩, ⟨.privateRow 13 6, 207601832068230600⟩, ⟨.privateRow 14 3, 128515419851761800⟩, ⟨.hall 6 23, 38908043360120884950⟩, ⟨.hall 5 24, 311840095961902972464⟩, ⟨.hall 4 25, 903898376825076032400⟩, ⟨.hall 3 26, 2015121783275625024000⟩, ⟨.hall 2 27, 3792747070665194241600⟩, ⟨.assumptionRow 16, 91588408450689150⟩]
  caps := #[0, 0, 651667256962703982000, 0, 0, 30925830590092646208, 1220662275652719900, 2576829546731312730, 877561992517099890, 744775313825366460, 748746305855648100, 1190819391870525200, 800755117780764300, 91588408450689150, 6079187268215919000, 6720133468500351900, 1064309651866310850, 88915235409000000, 0, 0] }

theorem case_49_30_16_checked :
    (Witness.linear .conditional case_49_30_16).check 49 30 16 = true := by
  change case_49_30_16.check 49 30 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_30_17 : Certificate := {
  objectiveScale := 13244395164000000
  eta := 95918247964401284822400
  rows := #[⟨.count 2, 17209376000898955473600⟩, ⟨.count 3, 3006116739482200344000⟩, ⟨.count 4, 554975398058252371200⟩, ⟨.count 5, 97634560769507361600⟩, ⟨.count 6, 17067695773616888400⟩, ⟨.count 7, 3261073386026055600⟩, ⟨.count 8, 592922433822919200⟩, ⟨.count 9, 323412236630683200⟩, ⟨.count 10, 161706118315341600⟩, ⟨.path 8, 123710309594791920⟩, ⟨.privateRow 2 28, 1135644101582164574400⟩, ⟨.privateRow 3 25, 114763431079947249600⟩, ⟨.privateRow 3 26, 449632845649047060000⟩, ⟨.privateRow 4 23, 83101784865493519125⟩, ⟨.privateRow 4 24, 165721820253505916400⟩, ⟨.privateRow 4 25, 316991156182578177300⟩, ⟨.privateRow 5 20, 6209215487534459400⟩, ⟨.privateRow 5 21, 30163940616684642768⟩, ⟨.privateRow 5 22, 61278533535598699320⟩, ⟨.privateRow 5 23, 121186757446362207600⟩, ⟨.privateRow 5 24, 163280956234268232360⟩, ⟨.privateRow 6 18, 3814669331891332200⟩, ⟨.privateRow 6 19, 10797305749259429400⟩, ⟨.privateRow 6 20, 22188004505701954920⟩, ⟨.privateRow 6 21, 44848582308361581750⟩, ⟨.privateRow 6 22, 66527308795012065000⟩, ⟨.privateRow 6 23, 74648228558265261900⟩, ⟨.privateRow 7 15, 32940135212384400⟩, ⟨.privateRow 7 16, 1551127438483172550⟩, ⟨.privateRow 7 17, 4132306350010753200⟩, ⟨.privateRow 7 18, 8265621071507599800⟩, ⟨.privateRow 7 19, 17110047376032811200⟩, ⟨.privateRow 7 20, 26332108802100000900⟩, ⟨.privateRow 7 21, 33020132683614476400⟩, ⟨.privateRow 7 22, 27973233395717009400⟩, ⟨.privateRow 8 12, 8983673239741200⟩, ⟨.privateRow 8 14, 551747264807438700⟩, ⟨.privateRow 8 15, 1618184142308383650⟩, ⟨.privateRow 8 16, 3299895688240651500⟩, ⟨.privateRow 8 17, 6868018191782147400⟩, ⟨.privateRow 8 18, 11058003390797443080⟩, ⟨.privateRow 8 19, 13563100673699276700⟩, ⟨.privateRow 8 20, 16330072031539566300⟩, ⟨.privateRow 9 12, 174283260850979280⟩, ⟨.privateRow 9 13, 638838985937152000⟩, ⟨.privateRow 9 14, 1399207107089691900⟩, ⟨.privateRow 9 15, 2995413334507994400⟩, ⟨.privateRow 9 16, 5006900552282428800⟩, ⟨.privateRow 9 17, 6956956556855585280⟩, ⟨.privateRow 9 18, 3463206033920232600⟩, ⟨.privateRow 10 10, 47041779873553920⟩, ⟨.privateRow 10 11, 247410361022472648⟩, ⟨.privateRow 10 12, 621670188190091040⟩, ⟨.privateRow 10 13, 1423013841175006080⟩, ⟨.privateRow 10 14, 2513375096101309440⟩, ⟨.privateRow 10 15, 2886454211928847560⟩, ⟨.privateRow 11 8, 8983673239741200⟩, ⟨.privateRow 11 9, 89836732397412000⟩, ⟨.privateRow 11 10, 282087339727873680⟩, ⟨.privateRow 11 11, 443194546493899200⟩, ⟨.privateRow 11 12, 1978654031052999300⟩, ⟨.privateRow 12 7, 28822618310836350⟩, ⟨.privateRow 12 8, 123525507046441500⟩, ⟨.privateRow 12 9, 392811112407683970⟩, ⟨.privateRow 12 10, 422731735225599800⟩, ⟨.privateRow 13 5, 3257815570455600⟩, ⟨.privateRow 13 6, 52939503019903500⟩, ⟨.privateRow 13 7, 211758012079614000⟩, ⟨.privateRow 13 8, 38116442174330520⟩, ⟨.privateRow 14 4, 14117200805307600⟩, ⟨.privateRow 14 5, 76468171028749500⟩, ⟨.privateRow 15 3, 19764081127430640⟩, ⟨.hall 6 23, 17687087958949759350⟩, ⟨.hall 5 24, 69577471201006825056⟩, ⟨.hall 4 25, 171947505808646568000⟩, ⟨.hall 3 26, 352283766051380363200⟩, ⟨.hall 2 27, 627100176972568899600⟩, ⟨.assumptionRow 17, 9704398673970000⟩]
  caps := #[0, 204326744932975064400, 0, 5040705413306362800, 1226411125720981200, 0, 694879114957232634, 0, 61040250220469520, 91595027587743680, 0, 39775394803544400, 54659358752618620, 171223777218888240, 9704398673970000, 184843742677754160, 893661244866390000, 149228343294030000, 13244395164000000, 0] }

theorem case_49_30_17_checked :
    (Witness.linear .conditional case_49_30_17).check 49 30 17 = true := by
  change case_49_30_17.check 49 30 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_30_18 : Certificate := {
  objectiveScale := 16254361819970754480000
  eta := 99027656539978287744976953600
  rows := #[⟨.count 2, 19871221295750203676852755200⟩, ⟨.count 3, 3753023565094289804792073600⟩, ⟨.count 4, 753502800713911466599180800⟩, ⟨.count 5, 142489311673464027337665600⟩, ⟨.count 6, 25875782991549157506840000⟩, ⟨.count 7, 4458596453928470216563200⟩, ⟨.count 8, 743099408988078369427200⟩, ⟨.count 9, 151997606383925121019200⟩, ⟨.path 8, 12016326203040496296960⟩, ⟨.path 9, 57621323281331607557760⟩, ⟨.privateRow 2 28, 2217037086715931815186051200⟩, ⟨.privateRow 3 25, 210916382251116243855753600⟩, ⟨.privateRow 3 26, 685880754495996334981305600⟩, ⟨.privateRow 4 23, 123168727039773989732558400⟩, ⟨.privateRow 4 24, 252073252642674709379133000⟩, ⟨.privateRow 4 25, 493580560563800179442973000⟩, ⟨.privateRow 5 20, 7567228981528598062000320⟩, ⟨.privateRow 5 21, 43278109579465684235440128⟩, ⟨.privateRow 5 22, 91048255086264302214067680⟩, ⟨.privateRow 5 23, 187892685562635615709667520⟩, ⟨.privateRow 5 24, 264692009481553515189968640⟩, ⟨.privateRow 6 18, 4830146158422509401276800⟩, ⟨.privateRow 6 19, 14979203265107901178959600⟩, ⟨.privateRow 6 20, 32258476129464616358527200⟩, ⟨.privateRow 6 21, 68419882860154563974336100⟩, ⟨.privateRow 6 22, 107643257244844495228454400⟩, ⟨.privateRow 6 23, 128775146687942973859040400⟩, ⟨.privateRow 7 15, 75194583052365073096800⟩, ⟨.privateRow 7 16, 2010349293958819160146800⟩, ⟨.privateRow 7 17, 5527749685227644197065600⟩, ⟨.privateRow 7 18, 11650737162348800149233600⟩, ⟨.privateRow 7 19, 25525464698740491989824320⟩, ⟨.privateRow 7 20, 41968529567447229694747800⟩, ⟨.privateRow 7 21, 56979801110621580684292800⟩, ⟨.privateRow 7 22, 54060482003882701375828800⟩, ⟨.privateRow 8 13, 71987755245720092038260⟩, ⟨.privateRow 8 14, 709556727332366498585000⟩, ⟨.privateRow 8 15, 2098675283978049457405725⟩, ⟨.privateRow 8 16, 4458596453928470216563200⟩, ⟨.privateRow 8 17, 9919603048106483650218300⟩, ⟨.privateRow 8 18, 17216684431992540721666440⟩, ⟨.privateRow 8 19, 24568724209668341089186800⟩, ⟨.privateRow 8 20, 27695934222493170893859600⟩, ⟨.privateRow 8 21, 14954875605885077184722400⟩, ⟨.privateRow 9 11, 33777245863094471337600⟩, ⟨.privateRow 9 12, 248262757093744364331360⟩, ⟨.privateRow 9 13, 795641791441780880396800⟩, ⟨.privateRow 9 14, 1809193731541997621020200⟩, ⟨.privateRow 9 15, 4137712618229072738856000⟩, ⟨.privateRow 9 16, 7523881516004293490450400⟩, ⟨.privateRow 9 17, 11440353173830097442045120⟩, ⟨.privateRow 9 18, 13705117508950581745231200⟩, ⟨.privateRow 10 9, 10133173758928341401280⟩, ⟨.privateRow 10 10, 88434970987010979502080⟩, ⟨.privateRow 10 11, 308555140959367995668976⟩, ⟨.privateRow 10 12, 763365756505935052229760⟩, ⟨.privateRow 10 13, 1869570558522278988536160⟩, ⟨.privateRow 10 14, 3593657693791372504096800⟩, ⟨.privateRow 10 15, 5824041617944064220385680⟩, ⟨.privateRow 10 16, 3574983702149918846371584⟩, ⟨.privateRow 11 7, 2598249681776497795200⟩, ⟨.privateRow 11 8, 30962475374503265392800⟩, ⟨.privateRow 11 9, 124361677950484189924800⟩, ⟨.privateRow 11 10, 339461320924099436942880⟩, ⟨.privateRow 11 11, 904479583667307510262400⟩, ⟨.privateRow 11 12, 1899970079799064012740000⟩, ⟨.privateRow 11 13, 2859002596269067752504000⟩, ⟨.privateRow 12 6, 8931483281106711171000⟩, ⟨.privateRow 12 7, 50314022483567806263300⟩, ⟨.privateRow 12 8, 160441917849698738853600⟩, ⟨.privateRow 12 9, 283306649676704878344120⟩, ⟨.privateRow 12 10, 1483618611694948133405000⟩, ⟨.privateRow 12 11, 319300527299564924363250⟩, ⟨.privateRow 13 4, 2843492636433973352400⟩, ⟨.privateRow 13 5, 18373337035419520123200⟩, ⟨.privateRow 13 6, 79617793820151253867200⟩, ⟨.privateRow 13 7, 271424297114152001820000⟩, ⟨.privateRow 13 8, 437897866010831896269600⟩, ⟨.privateRow 14 3, 6160900712273608930200⟩, ⟨.privateRow 14 4, 39808896910075626933600⟩, ⟨.privateRow 14 5, 165317502446008506293700⟩, ⟨.privateRow 14 6, 54888024527528515923600⟩, ⟨.privateRow 15 2, 17250521994366105004560⟩, ⟨.privateRow 15 3, 55732455674105877707040⟩, ⟨.hall 6 23, 40172153094380067029369100⟩, ⟨.hall 5 24, 127612461505522698381733056⟩, ⟨.hall 4 25, 292038067732314799184889600⟩, ⟨.hall 3 26, 573714027039295838884988800⟩, ⟨.hall 2 27, 1008810526230529820666668800⟩, ⟨.assumptionRow 18, 4616173804376909174400⟩]
  caps := #[0, 0, 0, 0, 0, 328458048344282263767360, 115324877769199323825600, 128924749905718739664120, 41340674874668804790155, 0, 55686501011882895511392, 0, 248339416772610216330970, 90179424569638456826400, 4616173804376909174400, 0, 4081995393914993966611200, 1001139432645576131107200, 174181806215301390105600, 16254361819970754480000] }

theorem case_49_30_18_checked :
    (Witness.linear .conditional case_49_30_18).check 49 30 18 = true := by
  change case_49_30_18.check 49 30 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_30_19 : Certificate := {
  objectiveScale := 4837607684515105500000
  eta := 55425927167898295379651280000
  rows := #[⟨.count 2, 7841742288198944012972884800⟩, ⟨.count 3, 1217196831922472369121753600⟩, ⟨.count 4, 228224405985463569210328800⟩, ⟨.count 5, 42867547155999770936331600⟩, ⟨.count 6, 7245219237633764101915200⟩, ⟨.count 7, 1253980252667382248408400⟩, ⟨.count 8, 185774852247019592356800⟩, ⟨.path 3, 71621272128105517024247040⟩, ⟨.path 8, 11077550718427957523760⟩, ⟨.path 9, 14541131618494125765120⟩, ⟨.privateRow 5 20, 1952184072362430883016040⟩, ⟨.privateRow 8 13, 9288742612350979617840⟩, ⟨.privateRow 8 14, 82566600998675374380800⟩, ⟨.privateRow 8 15, 255440421839651939490600⟩, ⟨.privateRow 9 11, 5373652750946847712800⟩, ⟨.privateRow 9 12, 36310539302826556687920⟩, ⟨.privateRow 9 13, 121035131009421855626400⟩, ⟨.privateRow 9 14, 293439823435633219745400⟩, ⟨.privateRow 9 15, 322090165908793708826400⟩, ⟨.privateRow 9 16, 537621163320920335456800⟩, ⟨.privateRow 9 17, 672167192675579979618240⟩, ⟨.privateRow 10 9, 633323359933021337580⟩, ⟨.privateRow 10 11, 2279964095758876815288⟩, ⟨.privateRow 10 12, 283728865249993559235840⟩, ⟨.privateRow 10 13, 294495362368854921974700⟩, ⟨.privateRow 10 18, 13545520022247460368161040⟩, ⟨.privateRow 11 10, 4222155732886808917200⟩, ⟨.privateRow 11 16, 1707861993952714207007400⟩, ⟨.privateRow 12 8, 3166616799665106687900⟩, ⟨.privateRow 15 5, 10977604905505703184720⟩, ⟨.privateRow 15 12, 60376826980281367515960⟩, ⟨.hall 13 5, 90601481062847190150⟩, ⟨.hall 13 6, 156810255685697059875⟩, ⟨.hall 11 7, 82033231374457925100⟩, ⟨.hall 12 7, 194516197508696580825⟩, ⟨.hall 10 8, 135409297141086830400⟩, ⟨.hall 14 8, 65677978067128138712⟩, ⟨.hall 10 9, 30919573418973416100⟩, ⟨.hall 11 9, 118902099407922161100⟩, ⟨.hall 8 12, 130673802272892527880⟩, ⟨.hall 7 16, 1313258253936198570000⟩, ⟨.hall 6 18, 5453749273123002787650⟩, ⟨.hall 5 19, 7222377637364544160506⟩, ⟨.hall 8 19, 22477952901749773187760⟩, ⟨.hall 9 20, 1469310195044609503185600⟩, ⟨.hall 4 22, 177404887436542459635942⟩]
  caps := #[0, 0, 0, 0, 0, 0, 102524401895301289599696, 42093842369977672564290, 0, 73092013327280288905200, 54324021447019495403232, 656265850995663400800, 0, 41152561050633099467400, 525801514273020622837200, 0, 3081556095036122203500000, 1006222398379141944000000, 261230814963815697000000, 48376076845151055000000] }

theorem case_49_30_19_checked :
    (Witness.linear .negative case_49_30_19).check 49 30 19 = true := by
  change case_49_30_19.check 49 30 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_31_1_checked :
    (Witness.rising).check 49 31 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_31_2_checked :
    (Witness.rising).check 49 31 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_31_3_checked :
    (Witness.rising).check 49 31 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_31_4_checked :
    (Witness.rising).check 49 31 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_31_5_checked :
    (Witness.rising).check 49 31 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_31_6_checked :
    (Witness.rising).check 49 31 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_31_7_checked :
    (Witness.rising).check 49 31 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_31_8_checked :
    (Witness.rising).check 49 31 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_31_9_checked :
    (Witness.rising).check 49 31 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_31_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_31_10_checked :
    (Witness.linear .positive case_49_31_10).check 49 31 10 = true := by
  change case_49_31_10.check 49 31 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_31_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_31_11_checked :
    (Witness.linear .positive case_49_31_11).check 49 31 11 = true := by
  change case_49_31_11.check 49 31 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_31_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_31_12_checked :
    (Witness.linear .positive case_49_31_12).check 49 31 12 = true := by
  change case_49_31_12.check 49 31 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_31_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_49_31_13_checked :
    (Witness.linear .positive case_49_31_13).check 49 31 13 = true := by
  change case_49_31_13.check 49 31 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_31_14 : Certificate := {
  objectiveScale := 28
  eta := 13520780
  rows := #[⟨.assumptionRow 14, 109⟩]
  caps := #[0, 0, 3875354, 1125332, 331942, 99814, 30745, 9768, 3234, 1134, 433, 190, 5776, 1927, 339, 28, 0, 0, 0] }

theorem case_49_31_14_checked :
    (Witness.linear .conditional case_49_31_14).check 49 31 14 = true := by
  change case_49_31_14.check 49 31 14 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_31_15 : Certificate := {
  objectiveScale := 12537470000
  eta := 548215952308424400
  rows := #[⟨.count 2, 53746661991022000⟩, ⟨.count 3, 6276842311094355⟩, ⟨.count 4, 967439915838396⟩, ⟨.count 5, 189210187621455⟩, ⟨.count 6, 36702979538610⟩, ⟨.count 7, 7382783240525⟩, ⟨.count 8, 1610789070660⟩, ⟨.count 9, 483236721198⟩, ⟨.path 3, 1050457675559292⟩, ⟨.path 8, 155507587074⟩]
  caps := #[0, 0, 55173568765700, 6290161917963, 0, 0, 0, 172897608511, 199664556414, 43337018802, 175524580000, 62687350000, 25074940000, 12537470000, 12537470000, 0, 0, 0, 0] }

theorem case_49_31_15_checked :
    (Witness.linear .positive case_49_31_15).check 49 31 15 = true := by
  change case_49_31_15.check 49 31 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_31_16 : Certificate := {
  objectiveScale := 49133279245050000
  eta := 861313360257070205284800
  rows := #[⟨.count 2, 117628973922397082745600⟩, ⟨.count 3, 18335239158084485036400⟩, ⟨.count 4, 3117876417220163639040⟩, ⟨.count 5, 531456207480709711200⟩, ⟨.count 6, 99283027771121594400⟩, ⟨.count 7, 17033852803868901000⟩, ⟨.count 8, 4955302633852771200⟩, ⟨.count 9, 2229886185233747040⟩, ⟨.path 3, 703045822592228955840⟩, ⟨.path 8, 674275521981952800⟩, ⟨.privateRow 2 29, 10274820011293721083200⟩, ⟨.privateRow 3 26, 1933910088332582560200⟩, ⟨.privateRow 3 27, 3277313279464376552400⟩, ⟨.privateRow 4 23, 283443310656378512640⟩, ⟨.privateRow 4 24, 786112306898549781150⟩, ⟨.privateRow 4 25, 1251874622065671764160⟩, ⟨.privateRow 4 26, 2001818381510673245520⟩, ⟨.privateRow 5 20, 28922786801671276800⟩, ⟨.privateRow 5 21, 153953583913062733800⟩, ⟨.privateRow 5 22, 289517095884729480768⟩, ⟨.privateRow 5 23, 461228065777901642220⟩, ⟨.privateRow 5 24, 765971803797594313920⟩, ⟨.privateRow 5 25, 833880096975684999240⟩, ⟨.privateRow 6 18, 23969064302586953550⟩, ⟨.privateRow 6 19, 63268596128655918000⟩, ⟨.privateRow 6 20, 113559018692459340000⟩, ⟨.privateRow 6 21, 173842634901199183920⟩, ⟨.privateRow 6 22, 288358793894066395500⟩, ⟨.privateRow 6 23, 337756967025286208400⟩, ⟨.privateRow 6 24, 276921778440040133400⟩, ⟨.privateRow 7 15, 1022031168232134060⟩, ⟨.privateRow 7 16, 11788507654741017200⟩, ⟨.privateRow 7 17, 26645812600337780850⟩, ⟨.privateRow 7 18, 46721424833468985600⟩, ⟨.privateRow 7 19, 70731045928446103200⟩, ⟨.privateRow 7 20, 115148844954153770760⟩, ⟨.privateRow 7 21, 138582559597190558850⟩, ⟨.privateRow 7 22, 107069931910033092000⟩, ⟨.privateRow 8 13, 788343600840213600⟩, ⟨.privateRow 8 14, 5326950331391729040⟩, ⟨.privateRow 8 15, 12044138346169930000⟩, ⟨.privateRow 8 16, 20866469684739403725⟩, ⟨.privateRow 8 17, 31457322970261788600⟩, ⟨.privateRow 8 18, 51049940675837403300⟩, ⟨.privateRow 8 19, 61755459074390161080⟩, ⟨.privateRow 9 11, 433588980462117480⟩, ⟨.privateRow 9 12, 2477651316926385600⟩, ⟨.privateRow 9 13, 5896810134284797728⟩, ⟨.privateRow 9 14, 10378606072013859680⟩, ⟨.privateRow 9 15, 12976698772401944580⟩, ⟨.privateRow 9 16, 31076826518019522240⟩, ⟨.privateRow 10 9, 209647419124540320⟩, ⟨.privateRow 10 10, 1238825658463192800⟩, ⟨.privateRow 10 11, 3153374403360854400⟩, ⟨.privateRow 10 12, 5847257107946270016⟩, ⟨.privateRow 10 13, 9112250954473707040⟩, ⟨.privateRow 10 14, 1114943092616873520⟩, ⟨.privateRow 11 7, 88487547033085200⟩, ⟨.privateRow 11 8, 690883540296780600⟩, ⟨.privateRow 11 9, 1909856223464088900⟩, ⟨.privateRow 11 10, 3660166718186706000⟩, ⟨.privateRow 12 5, 32445433912131240⟩, ⟨.privateRow 12 6, 417155578870258800⟩, ⟨.privateRow 12 7, 1310296369528377000⟩, ⟨.privateRow 12 8, 40556792390164050⟩, ⟨.privateRow 13 4, 259563471297049920⟩, ⟨.privateRow 13 5, 139051859623419600⟩, ⟨.privateRow 14 2, 158171490321639795⟩, ⟨.hall 5 25, 122157058679174118600⟩, ⟨.hall 4 26, 602317035144804339360⟩, ⟨.hall 3 27, 1632329780119322684400⟩, ⟨.hall 2 28, 3616345687684829299200⟩, ⟨.assumptionRow 16, 53128261513847520⟩]
  caps := #[0, 463833294708331875600, 528995180197838565120, 87041444991791370990, 26343364687476741450, 3232411131970599774, 0, 7876581446061269760, 0, 0, 1686334276226610864, 163379766810340080, 53128261513847520, 16545829084601010480, 0, 4312937118777487200, 634737647916852480, 49133279245050000, 0] }

theorem case_49_31_16_checked :
    (Witness.linear .conditional case_49_31_16).check 49 31 16 = true := by
  change case_49_31_16.check 49 31 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_31_17 : Certificate := {
  objectiveScale := 1118201089986230250000
  eta := 21466491293369557336666564800
  rows := #[⟨.count 2, 2799165772824196117502160000⟩, ⟨.count 3, 394215846339407619881554200⟩, ⟨.count 4, 58471462810105430010045120⟩, ⟨.count 5, 8664084534932035601792400⟩, ⟨.count 6, 1230402537505141150550400⟩, ⟨.count 7, 239244937848221890384800⟩, ⟨.count 8, 86998159217535232867200⟩, ⟨.count 9, 39149171647890854790240⟩, ⟨.path 3, 16078484626836594081078960⟩, ⟨.path 7, 50681816253671572569600⟩, ⟨.privateRow 2 29, 255035103746204535150196800⟩, ⟨.privateRow 3 26, 44579306752385345575034400⟩, ⟨.privateRow 3 27, 79698469920688917234436500⟩, ⟨.privateRow 4 23, 5847146281010543001004512⟩, ⟨.privateRow 4 24, 17611417987352233905951090⟩, ⟨.privateRow 4 25, 30065113856259884225023200⟩, ⟨.privateRow 4 26, 51395793773244267601914660⟩, ⟨.privateRow 5 20, 469701286142835629694240⟩, ⟨.privateRow 5 21, 3028726986997609026609480⟩, ⟨.privateRow 5 22, 6291458308442955083147712⟩, ⟨.privateRow 5 23, 10930075874837337220722720⟩, ⟨.privateRow 5 24, 19801506022571165127515280⟩, ⟨.privateRow 5 25, 23815124670377287602875520⟩, ⟨.privateRow 6 18, 348186829189822929756450⟩, ⟨.privateRow 6 19, 1186459589737100395173600⟩, ⟨.privateRow 6 20, 2392449378482218903848000⟩, ⟨.privateRow 6 21, 4060328373766965796816320⟩, ⟨.privateRow 6 22, 7446498690525906338226900⟩, ⟨.privateRow 6 23, 9888790764393171469238400⟩, ⟨.privateRow 6 24, 9595430900126899389361800⟩, ⟨.privateRow 7 16, 163294163928151448992800⟩, ⟨.privateRow 7 17, 467809298113933874948850⟩, ⟨.privateRow 7 18, 949655926764880768976400⟩, ⟨.privateRow 7 19, 1616327407486499080873500⟩, ⟨.privateRow 7 20, 2958092767251943516114920⟩, ⟨.privateRow 7 21, 4082116752035286004690650⟩, ⟨.privateRow 7 22, 4428879504214107613671000⟩, ⟨.privateRow 7 23, 2422354995713246640146100⟩, ⟨.privateRow 8 14, 64161142422932234239560⟩, ⟨.privateRow 8 15, 196350012122909379735000⟩, ⟨.privateRow 8 16, 401686813262213458004025⟩, ⟨.privateRow 8 17, 694431735182825876636400⟩, ⟨.privateRow 8 18, 1281410386808279367439800⟩, ⟨.privateRow 8 19, 1831311251529116651854560⟩, ⟨.privateRow 8 20, 1947943158730124823417150⟩, ⟨.privateRow 9 12, 22935878339168379574080⟩, ⟨.privateRow 9 13, 86128177625359880538528⟩, ⟨.privateRow 9 14, 186079396104172581410400⟩, ⟨.privateRow 9 15, 327874312551085908868260⟩, ⟨.privateRow 9 16, 615201268752570575275200⟩, ⟨.privateRow 9 17, 919280549065288960630080⟩, ⟨.privateRow 9 18, 274914183127411335860352⟩, ⟨.privateRow 10 10, 7974831261607396346160⟩, ⟨.privateRow 10 11, 39149171647890854790240⟩, ⟨.privateRow 10 12, 94393002751025727660912⟩, ⟨.privateRow 10 13, 101981175527221856305440⟩, ⟨.privateRow 10 14, 479577352686662971180440⟩, ⟨.privateRow 10 15, 164053671667352153406720⟩, ⟨.privateRow 11 8, 2509562285121208640400⟩, ⟨.privateRow 11 9, 18124616503653173514000⟩, ⟨.privateRow 11 10, 51902310896824996881000⟩, ⟨.privateRow 11 11, 104941529556151874646060⟩, ⟨.privateRow 11 12, 129288931059392637733200⟩, ⟨.privateRow 12 6, 610318719000566046900⟩, ⟨.privateRow 12 7, 8544462066007924656600⟩, ⟨.privateRow 12 8, 30617655736528396686150⟩, ⟨.privateRow 12 9, 59811234462055472596200⟩, ⟨.privateRow 13 5, 3661912314003396281400⟩, ⟨.privateRow 13 6, 18403456757555530029600⟩, ⟨.privateRow 13 7, 7120385055006603880500⟩, ⟨.privateRow 14 3, 2962080182882747214288⟩, ⟨.privateRow 14 4, 6347314677605886887760⟩, ⟨.hall 5 25, 5656433887697246122669200⟩, ⟨.hall 4 26, 19029719574920049325570240⟩, ⟨.hall 3 27, 45403135303249609644008250⟩, ⟨.hall 2 28, 93520021222325632738003200⟩, ⟨.assumptionRow 17, 904103919576952399305⟩]
  caps := #[0, 47030910766993855551454605, 0, 943101225702879425942760, 0, 181723446795232866517708, 100082109017207001120150, 60284164099280478374160, 0, 39081677663790576597510, 10254670761635436236100, 23339585284598025120720, 904103919576952399305, 259507197024346614897180, 0, 397981671957938260472280, 87980643224683388909730, 13632510250244040850695, 1118201089986230250000] }

theorem case_49_31_17_checked :
    (Witness.linear .conditional case_49_31_17).check 49 31 17 = true := by
  change case_49_31_17.check 49 31 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_31_18 : Certificate := {
  objectiveScale := 1626939019653731784000000
  eta := 39078531317560196619532655280000
  rows := #[⟨.count 2, 4752336563943543415527067180800⟩, ⟨.count 3, 635177366616690502329865140000⟩, ⟨.count 4, 90497651472244665855759833280⟩, ⟨.count 5, 12444291264326997596666745600⟩, ⟨.count 6, 1595421956964999691880352000⟩, ⟨.count 7, 186132561645916630719374400⟩, ⟨.count 8, 33842283935621205585340800⟩, ⟨.path 3, 40054266157355574261011915040⟩, ⟨.path 7, 66251167299558355456742400⟩, ⟨.path 8, 5270506663869589016609280⟩, ⟨.privateRow 2 29, 450068534059826413079447299200⟩, ⟨.privateRow 3 26, 74608135126404916146682572000⟩, ⟨.privateRow 3 27, 137621762766949608838137447000⟩, ⟨.privateRow 4 23, 9194948545308281557537095360⟩, ⟨.privateRow 4 24, 28915693451693148582254813040⟩, ⟨.privateRow 4 25, 51298133989614623426259584640⟩, ⟨.privateRow 4 26, 91163075380128817810581596760⟩, ⟨.privateRow 5 20, 740731622876606999801592000⟩, ⟨.privateRow 5 21, 4666609224122624098750029600⟩, ⟨.privateRow 5 22, 10100616409545413049294508512⟩, ⟨.privateRow 5 23, 18329404008081640210090394040⟩, ⟨.privateRow 5 24, 34959240459229732137302690880⟩, ⟨.privateRow 5 25, 44713029862241587198023431760⟩, ⟨.privateRow 6 18, 551750093450395726775288400⟩, ⟨.privateRow 6 19, 1775856583050327037985868000⟩, ⟨.privateRow 6 20, 3727082960576568724642711200⟩, ⟨.privateRow 6 21, 6663545706923815379753603520⟩, ⟨.privateRow 6 22, 12982746174802684992676364400⟩, ⟨.privateRow 6 23, 18591097526300482520661324000⟩, ⟨.privateRow 6 24, 19796527449340704510082034400⟩, ⟨.privateRow 7 15, 15289460420914580380520040⟩, ⟨.privateRow 7 16, 242267778650240693952201600⟩, ⟨.privateRow 7 17, 679716229581963410394858300⟩, ⟨.privateRow 7 18, 1428282513854380676540505600⟩, ⟨.privateRow 7 19, 2574833769435180058284679200⟩, ⟨.privateRow 7 20, 5053499048686636524031014960⟩, ⟨.privateRow 7 21, 7588225682814779784505924200⟩, ⟨.privateRow 7 22, 9175892116377866283439635600⟩, ⟨.privateRow 7 23, 7066389751057477801953392400⟩, ⟨.privateRow 8 13, 8460570983905301396335200⟩, ⟨.privateRow 8 14, 95604452118129905778587760⟩, ⟨.privateRow 8 15, 273558461812938078481504800⟩, ⟨.privateRow 8 16, 581664255143489470998045000⟩, ⟨.privateRow 8 17, 1065427617473217597267068400⟩, ⟨.privateRow 8 18, 2123603316960230650480135200⟩, ⟨.privateRow 8 19, 3326696510871564509039000640⟩, ⟨.privateRow 8 20, 4292682202958952295965572100⟩, ⟨.privateRow 8 21, 2229360454259046917934325200⟩, ⟨.privateRow 9 11, 2820190327968433798778400⟩, ⟨.privateRow 9 12, 37534169455870791649196160⟩, ⟨.privateRow 9 13, 116755879577893159269425760⟩, ⟨.privateRow 9 14, 257953408664846078128264320⟩, ⟨.privateRow 9 15, 481829517533406914521289640⟩, ⟨.privateRow 9 16, 978525466938533144353282560⟩, ⟨.privateRow 9 17, 1607508486942007265303688000⟩, ⟨.privateRow 9 18, 2031890727494697183343861632⟩, ⟨.privateRow 10 9, 520650522086480085928320⟩, ⟨.privateRow 10 10, 14947008738232699133525520⟩, ⟨.privateRow 10 11, 53224682916931532420581440⟩, ⟨.privateRow 10 12, 125893296240510884777467776⟩, ⟨.privateRow 10 13, 244040469713535138054290880⟩, ⟨.privateRow 10 14, 229281473663833667840683920⟩, ⟨.privateRow 10 15, 1424760153689652755142847680⟩, ⟨.privateRow 10 16, 68248605936836097930437280⟩, ⟨.privateRow 11 8, 5857318373472900966693600⟩, ⟨.privateRow 11 9, 26086760533708012638700200⟩, ⟨.privateRow 11 10, 68453710687961074933984800⟩, ⟨.privateRow 11 11, 89682052429396194801153120⟩, ⟨.privateRow 11 12, 402817185178157960925514800⟩, ⟨.privateRow 11 13, 216802131462573348281089500⟩, ⟨.privateRow 12 6, 2374139816912201922441000⟩, ⟨.privateRow 12 7, 13806536166043266564349200⟩, ⟨.privateRow 12 8, 41547446795963533642717500⟩, ⟨.privateRow 12 9, 93066280822958315359687200⟩, ⟨.privateRow 12 10, 138269902936966639962963840⟩, ⟨.privateRow 13 4, 886345531647222051044640⟩, ⟨.privateRow 13 5, 7597247414119046151811200⟩, ⟨.privateRow 13 6, 27613072332086533128698400⟩, ⟨.privateRow 13 7, 59828323386187488445513200⟩, ⟨.privateRow 14 3, 4608996764565554665432128⟩, ⟨.privateRow 14 4, 19752843276709519994709120⟩, ⟨.privateRow 14 5, 5318073189883332306267840⟩, ⟨.privateRow 15 1, 7561635316865363122974585⟩, ⟨.privateRow 15 2, 8065744337989720664506224⟩, ⟨.hall 6 24, 1308246004711299747341888640⟩, ⟨.hall 5 25, 13195469102398018284927078000⟩, ⟨.hall 4 26, 37944846141164974770577058240⟩, ⟨.hall 3 27, 84517478170220858677361647200⟩, ⟨.hall 2 28, 167211223999980002189694547200⟩, ⟨.assumptionRow 18, 703363022215508648243250⟩]
  caps := #[0, 0, 4700211360086911861829628810, 0, 0, 167803429345422677535330576, 141078032432941844153791800, 0, 57091503940289560069162380, 3999965158070337401946000, 1292943495689549740186794, 97416621109562824163182200, 0, 58543241709917359276013880, 546058918286272823318058744, 0, 506125984879410346058107500, 116130585224535734940837750, 18819905213629272759756750] }

theorem case_49_31_18_checked :
    (Witness.linear .conditional case_49_31_18).check 49 31 18 = true := by
  change case_49_31_18.check 49 31 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_31_19 : Certificate := {
  objectiveScale := 33885020169000000
  eta := 912821851538418990168000
  rows := #[⟨.count 2, 127182968272969841232000⟩, ⟨.count 3, 19173657140575604667000⟩, ⟨.count 4, 2987150407563989066400⟩, ⟨.count 5, 490877038929226950000⟩, ⟨.count 6, 69477980894598276000⟩, ⟨.count 7, 8810613519242535000⟩, ⟨.count 8, 1281543784617096000⟩, ⟨.path 3, 803845495885851619200⟩, ⟨.path 8, 691416681740366400⟩, ⟨.privateRow 6 20, 126788924072147337000⟩, ⟨.privateRow 6 22, 348019234010080132500⟩, ⟨.privateRow 7 15, 125865907417750500⟩, ⟨.privateRow 7 16, 2489347946706621000⟩, ⟨.privateRow 7 18, 41643634511358594000⟩, ⟨.privateRow 7 21, 566396583379877250⟩, ⟨.privateRow 7 22, 866628727873684776000⟩, ⟨.privateRow 8 13, 189318968182071000⟩, ⟨.privateRow 8 14, 1345620973847950800⟩, ⟨.privateRow 8 15, 2652083665388157000⟩, ⟨.privateRow 8 18, 104419119617447134500⟩, ⟨.privateRow 8 21, 417783273785173296000⟩, ⟨.privateRow 8 22, 248379204756100918500⟩, ⟨.privateRow 9 11, 96115783846282200⟩, ⟨.privateRow 9 12, 594170300140653600⟩, ⟨.privateRow 9 13, 1537852541540515200⟩, ⟨.privateRow 9 14, 2591566320003460800⟩, ⟨.privateRow 9 15, 2867454218080752300⟩, ⟨.privateRow 9 19, 241538964805707168600⟩, ⟨.privateRow 10 9, 39432116449756800⟩, ⟨.privateRow 10 10, 213590630769516000⟩, ⟨.privateRow 10 11, 617471096224600800⟩, ⟨.privateRow 10 12, 1243097471078583120⟩, ⟨.privateRow 10 16, 576694703077693200⟩, ⟨.privateRow 11 8, 123225363905490000⟩, ⟨.privateRow 11 10, 1339795774826964000⟩, ⟨.privateRow 12 6, 17980843916821500⟩, ⟨.privateRow 12 8, 608351885852460750⟩, ⟨.privateRow 12 16, 25047315576132349500⟩, ⟨.privateRow 15 12, 916303806001223640⟩, ⟨.hall 12 5, 5109108041037000⟩, ⟨.hall 13 5, 2750011422572700⟩, ⟨.hall 11 6, 616989742243875⟩, ⟨.hall 10 7, 141897800369325⟩, ⟨.hall 10 8, 1483924292350500⟩, ⟨.hall 9 9, 1509759675496800⟩, ⟨.hall 8 11, 261127917666000⟩, ⟨.hall 6 16, 889964384268960⟩, ⟨.hall 5 19, 14863690501043670⟩, ⟨.hall 4 22, 431944229421312608⟩, ⟨.hall 3 24, 3097140428526113970⟩]
  caps := #[0, 0, 0, 49661594402015887200, 1845870368657023800, 0, 101012608357118640, 1421603873051475360, 0, 102324152865841200, 1135182402954600, 2087400091607838000, 0, 0, 0, 30444499224537357960, 30835368353790000000, 9250610506137000000, 2202526310985000000] }

theorem case_49_31_19_checked :
    (Witness.linear .negative case_49_31_19).check 49 31 19 = true := by
  change case_49_31_19.check 49 31 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_31_20 : Certificate := {
  objectiveScale := 3856967503489450350000
  eta := 164541184494990301555926969600
  rows := #[⟨.count 2, 14407088162340259669704220800⟩, ⟨.count 3, 1345449594311216334984443400⟩, ⟨.count 4, 164096177910825351450299040⟩, ⟨.count 5, 26819593242084046544540400⟩, ⟨.count 6, 3667636682678160211219200⟩, ⟨.count 7, 534863682890565030802800⟩, ⟨.path 3, 355824910567900057795711200⟩, ⟨.path 7, 12078293861259206380800⟩, ⟨.path 8, 34076551706053377262560⟩, ⟨.privateRow 6 18, 248329567056333764301300⟩, ⟨.privateRow 7 16, 157063144975800842378600⟩, ⟨.privateRow 10 11, 3536288812499603509440⟩, ⟨.hall 14 5, 112366319934992653530⟩, ⟨.hall 13 6, 96313988515707988740⟩, ⟨.hall 10 9, 118114909729237769040⟩, ⟨.hall 12 9, 120761742440257102800⟩, ⟨.hall 11 10, 118693904384773248300⟩, ⟨.hall 9 11, 2233265099922562860⟩, ⟨.hall 13 11, 137336613253879909870⟩, ⟨.hall 14 11, 168549479902488980295⟩, ⟨.hall 9 14, 231829460076405895704⟩, ⟨.hall 7 16, 87177854716918115150⟩, ⟨.hall 8 16, 567133601835407443200⟩]
  caps := #[0, 219611885042097585496040400, 0, 4404297705291057166833240, 514633665256391125186560, 282053450445507082463940, 213684061628853430201860, 0, 34076551706053377262560, 10147611374998862244480, 944919277833902152320, 63120558850439351461200, 139529656406234355861600, 493249574839582854493200, 449465279739970614120, 0, 6317712770715719673300000, 2456888299722779872950000, 802249240725805672800000] }

theorem case_49_31_20_checked :
    (Witness.linear .negative case_49_31_20).check 49 31 20 = true := by
  change case_49_31_20.check 49 31 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_32_1_checked :
    (Witness.rising).check 49 32 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_32_2_checked :
    (Witness.rising).check 49 32 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_32_3_checked :
    (Witness.rising).check 49 32 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_32_4_checked :
    (Witness.rising).check 49 32 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_32_5_checked :
    (Witness.rising).check 49 32 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_32_6_checked :
    (Witness.rising).check 49 32 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_32_7_checked :
    (Witness.rising).check 49 32 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_32_8_checked :
    (Witness.rising).check 49 32 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_32_9_checked :
    (Witness.rising).check 49 32 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_32_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_32_10_checked :
    (Witness.linear .positive case_49_32_10).check 49 32 10 = true := by
  change case_49_32_10.check 49 32 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_32_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_32_11_checked :
    (Witness.linear .positive case_49_32_11).check 49 32 11 = true := by
  change case_49_32_11.check 49 32 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_32_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_49_32_12_checked :
    (Witness.linear .positive case_49_32_12).check 49 32 12 = true := by
  change case_49_32_12.check 49 32 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_32_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_49_32_13_checked :
    (Witness.linear .positive case_49_32_13).check 49 32 13 = true := by
  change case_49_32_13.check 49 32 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_32_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_49_32_14_checked :
    (Witness.linear .positive case_49_32_14).check 49 32 14 = true := by
  change case_49_32_14.check 49 32 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_32_15 : Certificate := {
  objectiveScale := 189977661969480000
  eta := 11641769279401746207602880
  rows := #[⟨.count 2, 1639959703612829504745840⟩, ⟨.count 3, 226223690340267785437272⟩, ⟨.count 4, 30743456894379412511328⟩, ⟨.count 5, 4131419137798901588640⟩, ⟨.count 6, 569850915558469184640⟩, ⟨.count 7, 90658100202483733920⟩, ⟨.count 8, 18131620040496746784⟩, ⟨.path 6, 56522522864578666896⟩, ⟨.path 7, 14235324416599628160⟩, ⟨.hall 13 9, 501205772901834⟩, ⟨.hall 11 13, 29170706359366⟩, ⟨.hall 12 15, 2756631750960087⟩]
  caps := #[0, 0, 317248259418413714160, 0, 59254381259612989632, 0, 0, 5077641199022814240, 6945431339474613216, 7979061802718160000, 2659687267572720000, 949888309847400000, 6079556579683316400, 42585164733884273424, 189977661969480000, 0, 0, 0] }

theorem case_49_32_15_checked :
    (Witness.linear .positive case_49_32_15).check 49 32 15 = true := by
  change case_49_32_15.check 49 32 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_32_16 : Certificate := {
  objectiveScale := 82562922414624960000
  eta := 2467056393376720435338048000
  rows := #[⟨.count 2, 379128519276275419842391200⟩, ⟨.count 3, 58773990548092457430112320⟩, ⟨.count 4, 9018231353940112515731520⟩, ⟨.count 5, 1435262284446702257145600⟩, ⟨.count 6, 219276182346023955952800⟩, ⟨.count 7, 38056196936086802272800⟩, ⟨.count 8, 10148319182956480606080⟩, ⟨.path 7, 3188730361789393948800⟩, ⟨.path 8, 1122099734704880574720⟩, ⟨.privateRow 2 30, 30838204917209005441725600⟩, ⟨.privateRow 3 26, 634904218883714817917880⟩, ⟨.privateRow 3 27, 6369197878325520078160320⟩, ⟨.privateRow 3 28, 9977066296744089995852400⟩, ⟨.privateRow 4 23, 112295984292357722897040⟩, ⟨.privateRow 4 24, 1290540004098326446216752⟩, ⟨.privateRow 4 25, 2597924405840506550868060⟩, ⟨.privateRow 4 26, 3809425313302288907507280⟩, ⟨.privateRow 4 27, 5727095198910243867749040⟩, ⟨.privateRow 5 21, 233514895485376160884800⟩, ⟨.privateRow 5 22, 600683844972138352064640⟩, ⟨.privateRow 5 23, 980762561038579875716160⟩, ⟨.privateRow 5 24, 1417321505891118478931280⟩, ⟨.privateRow 5 25, 2184788144102202324766080⟩, ⟨.privateRow 5 26, 2093090831484774125004000⟩, ⟨.privateRow 6 18, 24733172082800681900400⟩, ⟨.privateRow 6 19, 127911106368513974305800⟩, ⟨.privateRow 6 20, 249177479938663586310000⟩, ⟨.privateRow 6 21, 393146690569891436178000⟩, ⟨.privateRow 6 22, 547525982585223453651840⟩, ⟨.privateRow 6 23, 836405740994114104713900⟩, ⟨.privateRow 6 24, 858277986455396797290000⟩, ⟨.privateRow 6 25, 451841830288776636508800⟩, ⟨.privateRow 7 15, 988472647690566292800⟩, ⟨.privateRow 7 16, 19752978409683149751120⟩, ⟨.privateRow 7 17, 60003950724623635329600⟩, ⟨.privateRow 7 18, 110091141136536820860600⟩, ⟨.privateRow 7 19, 169311243511569855009600⟩, ⟨.privateRow 7 20, 185146418427152458676400⟩, ⟨.privateRow 7 21, 442539204371066529286560⟩, ⟨.privateRow 7 22, 244646980303415157468000⟩, ⟨.privateRow 8 13, 1057116581557966729800⟩, ⟨.privateRow 8 14, 11532180889723273416000⟩, ⟨.privateRow 8 15, 29556979620360749765208⟩, ⟨.privateRow 8 16, 53419624588062585412560⟩, ⟨.privateRow 8 17, 81503688438119234867580⟩, ⟨.privateRow 8 18, 111087851056291475205840⟩, ⟨.privateRow 8 19, 137425155602535674874000⟩, ⟨.privateRow 9 11, 693902166355998673920⟩, ⟨.privateRow 9 12, 6577614285249570763200⟩, ⟨.privateRow 9 13, 16298815657475559761280⟩, ⟨.privateRow 9 14, 29430125630573793757632⟩, ⟨.privateRow 9 15, 45228928704287524676480⟩, ⟨.privateRow 9 16, 42566561017400793653280⟩, ⟨.privateRow 10 9, 453049963524842884200⟩, ⟨.privateRow 10 10, 4000779677896304854320⟩, ⟨.privateRow 10 11, 10359742499268073952040⟩, ⟨.privateRow 10 12, 19143420276940633870560⟩, ⟨.privateRow 10 13, 10655735142104304636384⟩, ⟨.privateRow 11 7, 241626647213249538240⟩, ⟨.privateRow 11 8, 2718299781149057305200⟩, ⟨.privateRow 11 9, 7666999382728110348000⟩, ⟨.privateRow 11 10, 2567283126640776343800⟩, ⟨.privateRow 12 5, 207647899948886321925⟩, ⟨.privateRow 12 6, 2214910932788120767200⟩, ⟨.privateRow 12 7, 1186559428279350411000⟩, ⟨.privateRow 13 4, 498354959877327172620⟩, ⟨.hall 4 27, 1006961793214987932791040⟩, ⟨.hall 3 28, 3615513679948642017305760⟩, ⟨.hall 2 29, 9251461475162701632517680⟩, ⟨.assumptionRow 16, 94099816702895732960⟩]
  caps := #[0, 0, 0, 0, 48540189909536347191788, 0, 18604223217133428083300, 10145696253534686095280, 0, 13350570040742973981376, 822019899352790501440, 5612162736569280035760, 94099816702895732960, 67241189594447837984400, 42035742306005424530400, 8319390700094038512640, 1144344019516478667040, 82562922414624960000] }

theorem case_49_32_16_checked :
    (Witness.linear .conditional case_49_32_16).check 49 32 16 = true := by
  change case_49_32_16.check 49 32 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_32_17 : Certificate := {
  objectiveScale := 160419372798346200000
  eta := 5098005959278332604318214400
  rows := #[⟨.count 2, 752858180933249339243895600⟩, ⟨.count 3, 109968048900362263035625200⟩, ⟨.count 4, 16112534637415716195696000⟩, ⟨.count 5, 2230966334411406857865600⟩, ⟨.count 6, 309856435334917619148000⟩, ⟨.count 7, 59154410382120636382800⟩, ⟨.count 8, 15774509435232169702080⟩, ⟨.path 6, 2430683397712489439520⟩, ⟨.path 7, 12610634010812393774400⟩, ⟨.privateRow 2 30, 66262798696372132854799800⟩, ⟨.privateRow 3 26, 657928497694475077990920⟩, ⟨.privateRow 3 27, 12719950955426518174491120⟩, ⟨.privateRow 3 28, 21335681282377977529134120⟩, ⟨.privateRow 4 24, 2247698581919492409299592⟩, ⟨.privateRow 4 25, 5145940749824644360000410⟩, ⟨.privateRow 4 26, 8163684216290629539152640⟩, ⟨.privateRow 4 27, 13151856397790578344736860⟩, ⟨.privateRow 5 21, 267361838488986059950560⟩, ⟨.privateRow 5 22, 1049380461000921003514560⟩, ⟨.privateRow 5 23, 1913673344628451215858048⟩, ⟨.privateRow 5 24, 3036593066282192667650400⟩, ⟨.privateRow 5 25, 5127091150008436871502240⟩, ⟨.privateRow 5 26, 5552627321201723735132160⟩, ⟨.privateRow 6 18, 17214246407495423286000⟩, ⟨.privateRow 6 19, 167838902473080377038500⟩, ⟨.privateRow 6 20, 420519447954531054558000⟩, ⟨.privateRow 6 21, 756566129609423853419700⟩, ⟨.privateRow 6 22, 1172290180350438325776600⟩, ⟨.privateRow 6 23, 1988245460065721389533000⟩, ⟨.privateRow 6 24, 2361794607108372074839200⟩, ⟨.privateRow 6 25, 1890124255542997476802800⟩, ⟨.privateRow 7 16, 14084383424314437234000⟩, ⟨.privateRow 7 17, 78872547176160848510400⟩, ⟨.privateRow 7 18, 177815340731969770079250⟩, ⟨.privateRow 7 19, 317099832524565044011200⟩, ⟨.privateRow 7 20, 491544981508573859466600⟩, ⟨.privateRow 7 21, 702529045204804129231920⟩, ⟨.privateRow 7 22, 1283791549126260953879100⟩, ⟨.privateRow 7 23, 480746954216599457587200⟩, ⟨.privateRow 8 14, 7528743139542626448720⟩, ⟨.privateRow 8 15, 36478553068974392436060⟩, ⟨.privateRow 8 16, 82158903308500883865000⟩, ⟨.privateRow 8 17, 146160688985823072395835⟩, ⟨.privateRow 8 18, 227603636136921305701440⟩, ⟨.privateRow 8 19, 386146845549954154165500⟩, ⟨.privateRow 8 20, 438925725035335121960376⟩, ⟨.privateRow 9 12, 3505446541162704378240⟩, ⟨.privateRow 9 13, 17845909664101040471040⟩, ⟨.privateRow 9 14, 42065358493952452538880⟩, ⟨.privateRow 9 15, 76340835785321117570560⟩, ⟨.privateRow 9 16, 119842453625999955931080⟩, ⟨.privateRow 9 17, 205569400735327163895360⟩, ⟨.privateRow 9 18, 17235112160716629859680⟩, ⟨.privateRow 10 10, 1668457728726479487720⟩, ⟨.privateRow 10 11, 9530432783786102528340⟩, ⟨.privateRow 10 12, 24378787308995171357760⟩, ⟨.privateRow 10 13, 46140440098054096378584⟩, ⟨.privateRow 10 14, 74271648590884799013960⟩, ⟨.privateRow 10 15, 12816788916126137882940⟩, ⟨.privateRow 11 8, 804821909960824984800⟩, ⟨.privateRow 11 9, 5633753369725774893600⟩, ⟨.privateRow 11 10, 15962301214223028865200⟩, ⟨.privateRow 11 11, 32778201423859053926400⟩, ⟨.privateRow 11 12, 563375336972577489360⟩, ⟨.privateRow 12 6, 344284928149908465720⟩, ⟨.privateRow 12 7, 3688767087320447847000⟩, ⟨.privateRow 12 8, 12314807045362110504600⟩, ⟨.privateRow 12 9, 860712320374771164300⟩, ⟨.privateRow 13 5, 3305135310239121270912⟩, ⟨.privateRow 13 6, 1770608201913814966560⟩, ⟨.hall 5 26, 394780050945228374025600⟩, ⟨.hall 4 27, 3141944254296064658160720⟩, ⟨.hall 3 28, 9100804046926532113293120⟩, ⟨.hall 2 29, 21053711926223202495709440⟩, ⟨.assumptionRow 17, 141772224904266437712⟩]
  caps := #[0, 0, 0, 407904608326108380686640, 2633960401635060777312, 39074622988780645449696, 3347656141639381335972, 15822182978444531934900, 0, 7820318937702274858736, 1712508888496905354240, 548441751722985988560, 53948165191668979900812, 141772224904266437712, 265986087447960224596944, 70397244038692626712272, 14557031397464008234320, 2104098994272580362288] }

theorem case_49_32_17_checked :
    (Witness.linear .conditional case_49_32_17).check 49 32 17 = true := by
  change case_49_32_17.check 49 32 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_32_18 : Certificate := {
  objectiveScale := 530842288169072880000
  eta := 19625067188372342326357728000
  rows := #[⟨.count 2, 2780217851686081829567344800⟩, ⟨.count 3, 384606201795113145591263520⟩, ⟨.count 4, 51560110839730291826227200⟩, ⟨.count 5, 6321071280832319430619200⟩, ⟨.count 6, 681684157736818762125600⟩, ⟨.count 7, 78872547176160848510400⟩, ⟨.count 8, 31549018870464339404160⟩, ⟨.path 6, 70302842887684309943040⟩, ⟨.path 7, 33034811539388420361600⟩, ⟨.privateRow 2 30, 256592114100845280416458800⟩, ⟨.privateRow 3 26, 2067775278468350245114320⟩, ⟨.privateRow 3 27, 46368294123229672163169600⟩, ⟨.privateRow 3 28, 81019195001805359604024720⟩, ⟨.privateRow 4 24, 7556778744947970895781424⟩, ⟨.privateRow 4 25, 18408570823247455753582680⟩, ⟨.privateRow 4 26, 30640670035485553632148560⟩, ⟨.privateRow 4 27, 51882361532478606150141120⟩, ⟨.privateRow 5 21, 846350720514803554015680⟩, ⟨.privateRow 5 22, 3449734980062082826514400⟩, ⟨.privateRow 5 23, 6682983597303503209784064⟩, ⟨.privateRow 5 24, 11260182860070906279838320⟩, ⟨.privateRow 5 25, 20260479451765813390690560⟩, ⟨.privateRow 5 26, 23772185718894879741034560⟩, ⟨.privateRow 6 18, 58528437785484439172400⟩, ⟨.privateRow 6 19, 499643501977554660876150⟩, ⟨.privateRow 6 20, 1341235712949714837169200⟩, ⟨.privateRow 6 21, 2570086988639066696599800⟩, ⟨.privateRow 6 22, 4267755969346265341065120⟩, ⟨.privateRow 6 23, 7808382170439924002529600⟩, ⟨.privateRow 6 24, 10218376667489283262569600⟩, ⟨.privateRow 6 25, 9435128455948241503056600⟩, ⟨.privateRow 7 16, 42816525609915889191360⟩, ⟨.privateRow 7 17, 224098189595758601323200⟩, ⟨.privateRow 7 18, 544361419349752999094100⟩, ⟨.privateRow 7 19, 1043854017219190005285600⟩, ⟨.privateRow 7 20, 1745524585720035921200400⟩, ⟨.privateRow 7 21, 3204478916700020759479680⟩, ⟨.privateRow 7 22, 3957711742232356862754000⟩, ⟨.privateRow 7 23, 5637509205305592076862400⟩, ⟨.privateRow 8 14, 21152183106334045736880⟩, ⟨.privateRow 8 15, 98985046706081864880552⟩, ⟨.privateRow 8 16, 240123088069645249909440⟩, ⟨.privateRow 8 17, 461897354400391969089030⟩, ⟨.privateRow 8 18, 780274841707019822763600⟩, ⟨.privateRow 8 19, 1449940325588423598449520⟩, ⟨.privateRow 8 20, 2101953382244686612802160⟩, ⟨.privateRow 8 21, 1419705849170895273187200⟩, ⟨.privateRow 9 12, 9347857443100545008640⟩, ⟨.privateRow 9 13, 46526835909977712656640⟩, ⟨.privateRow 9 14, 117081914474834326233216⟩, ⟨.privateRow 9 15, 229412001416092542087040⟩, ⟨.privateRow 9 16, 392171831792577552315600⟩, ⟨.privateRow 9 17, 738146885953403750503680⟩, ⟨.privateRow 9 18, 1008400121674471292807040⟩, ⟨.privateRow 10 10, 4246983309485584150560⟩, ⟨.privateRow 10 11, 23661764152848254553120⟩, ⟨.privateRow 10 12, 64173572475149054015280⟩, ⟨.privateRow 10 13, 131322791048307812769816⟩, ⟨.privateRow 10 14, 229168567628511798727440⟩, ⟨.privateRow 10 15, 436756729987990698626340⟩, ⟨.privateRow 10 16, 70985292458544763659360⟩, ⟨.privateRow 11 8, 2012054774902062462000⟩, ⟨.privateRow 11 9, 13434334958576847823200⟩, ⟨.privateRow 11 10, 40375232483034720070800⟩, ⟨.privateRow 11 11, 88091416326621207427200⟩, ⟨.privateRow 11 12, 159998595700212006978240⟩, ⟨.privateRow 11 13, 43818081764533804728000⟩, ⟨.privateRow 12 6, 1377139712599633862880⟩, ⟨.privateRow 12 7, 8853041009569074832800⟩, ⟨.privateRow 12 8, 30191139853145819301600⟩, ⟨.privateRow 12 9, 70578410270731235472600⟩, ⟨.privateRow 12 10, 9389588949542958156000⟩, ⟨.privateRow 13 4, 1549282176674588095740⟩, ⟨.privateRow 13 5, 6610270620478242541824⟩, ⟨.privateRow 13 6, 26559123028707224498400⟩, ⟨.privateRow 13 7, 3813617665660524543360⟩, ⟨.privateRow 14 3, 5035167074192411311155⟩, ⟨.privateRow 14 4, 5370844879138572065232⟩, ⟨.hall 5 26, 3222506927483143239139200⟩, ⟨.hall 4 27, 14765987099860259913627120⟩, ⟨.hall 3 28, 38231155462088807980201440⟩, ⟨.hall 2 29, 83462929421813409893705280⟩, ⟨.assumptionRow 18, 297449601042693524040⟩]
  caps := #[0, 0, 3416815282411349422342200, 0, 182465335591832284508880, 75695056274985238082376, 6249209791963718099520, 27358753428241627744440, 0, 5946832138739574094320, 1551304919129781788280, 91889971280274762711360, 2986308316171474705620, 0, 135925724650551671589831, 740619306920198618922240, 202635848285951940699840, 43611511520618849863440] }

theorem case_49_32_18_checked :
    (Witness.linear .conditional case_49_32_18).check 49 32 18 = true := by
  change case_49_32_18.check 49 32 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_32_19 : Certificate := {
  objectiveScale := 229510044469168320000
  eta := 13218723416535853566948998400
  rows := #[⟨.count 2, 1892014379798540474279602800⟩, ⟨.count 3, 262795439936250331151801760⟩, ⟨.count 4, 35125325509566261306617280⟩, ⟨.count 5, 4214047520554879620412800⟩, ⟨.count 6, 433799009468884666807200⟩, ⟨.count 7, 19718136794040212127600⟩, ⟨.path 6, 29043550341897950738880⟩, ⟨.path 7, 27613169098491205756800⟩, ⟨.privateRow 3 26, 845908068464325100274040⟩, ⟨.privateRow 3 27, 30076731323176003565299200⟩, ⟨.privateRow 4 24, 4922379331730501297785128⟩, ⟨.privateRow 4 25, 12074330643913402324149690⟩, ⟨.privateRow 5 21, 602006788650697088630400⟩, ⟨.privateRow 5 23, 8896597971336154680977376⟩, ⟨.privateRow 5 24, 5307840737287138816005240⟩, ⟨.privateRow 6 19, 462202516041252115229100⟩, ⟨.privateRow 6 20, 428634735546636039821400⟩, ⟨.privateRow 6 21, 1649124805838061550798800⟩, ⟨.privateRow 6 22, 1316889850173399881379000⟩, ⟨.privateRow 6 23, 9326678703581020336354800⟩, ⟨.privateRow 6 25, 162674628550831750052700⟩, ⟨.privateRow 7 15, 4865514273854078317200⟩, ⟨.privateRow 7 16, 18873073788581345893560⟩, ⟨.privateRow 7 17, 179028162637952402174400⟩, ⟨.privateRow 7 18, 291194627297700989812950⟩, ⟨.privateRow 7 19, 543657200178537277232400⟩, ⟨.privateRow 7 20, 1127220153392632126627800⟩, ⟨.privateRow 7 21, 1488437640281549726889120⟩, ⟨.privateRow 7 22, 4690099680296707598922000⟩, ⟨.privateRow 7 23, 2390589346553637146517600⟩, ⟨.privateRow 7 24, 1174637577587824065315600⟩, ⟨.privateRow 8 13, 164317806617001767730⟩, ⟨.privateRow 8 14, 20793671528260587334560⟩, ⟨.privateRow 8 17, 757669406310995151003030⟩, ⟨.privateRow 8 21, 5474740680865264897228140⟩, ⟨.privateRow 9 11, 269649733935592644480⟩, ⟨.privateRow 9 12, 10370279350939667118960⟩, ⟨.privateRow 9 13, 10835016581775631714560⟩, ⟨.privateRow 9 14, 10866884277604383572544⟩, ⟨.privateRow 9 15, 109642577926366809163840⟩, ⟨.privateRow 9 18, 1429637947704189602258880⟩, ⟨.privateRow 9 20, 1241804437206888025991520⟩, ⟨.privateRow 10 9, 140843834243144372340⟩, ⟨.privateRow 10 10, 5460407112195751050720⟩, ⟨.privateRow 10 11, 10187704010254109599260⟩, ⟨.privateRow 10 12, 12727161021607773282360⟩, ⟨.privateRow 10 13, 29774386559000720312676⟩, ⟨.privateRow 10 16, 435770823148288688019960⟩, ⟨.privateRow 10 19, 1071187781336234523831870⟩, ⟨.privateRow 11 8, 201205477490206246200⟩, ⟨.privateRow 11 9, 433365643825059607200⟩, ⟨.hall 11 5, 4821917761203199800⟩, ⟨.hall 12 5, 43168853220034962420⟩, ⟨.hall 13 5, 24249170635945565310⟩, ⟨.hall 11 6, 29121845426214061950⟩, ⟨.hall 10 7, 11479320855495982125⟩, ⟨.hall 14 7, 5906849257473919755⟩, ⟨.hall 10 8, 7170583924315571760⟩, ⟨.hall 5 19, 22034654112361122540⟩, ⟨.hall 3 25, 28450994148663987520620⟩, ⟨.hall 4 25, 127123111089256678247280⟩, ⟨.hall 2 27, 278496827138090611830780⟩]
  caps := #[0, 3813908886703847072232000, 240557974337388531751200, 57656573491803156018720, 26980438580431391294694, 23502945593778192671184, 0, 40421422024663213677780, 0, 4367197285386596196032, 80355245988471874875, 7078280592549367588200, 23950255871297980224000, 0, 0, 1056422045434315452750, 289182656031152083200000, 80328515564208912000000] }

theorem case_49_32_19_checked :
    (Witness.linear .negative case_49_32_19).check 49 32 19 = true := by
  change case_49_32_19.check 49 32 19 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_32_20 : Certificate := {
  objectiveScale := 3005292355480800000
  eta := 200150385340370024676916800
  rows := #[⟨.count 2, 25434787685771487696472800⟩, ⟨.count 3, 3018895360834559754628080⟩, ⟨.count 4, 319208283372833089915680⟩, ⟨.count 5, 27427880322542941441200⟩, ⟨.count 6, 1306089539168711497200⟩, ⟨.path 5, 2067285930720261451200⟩, ⟨.path 6, 1525030194313623357360⟩, ⟨.hall 13 6, 62579846709395730⟩, ⟨.hall 12 7, 94351153500319716⟩, ⟨.hall 8 8, 50226189963040⟩, ⟨.hall 14 8, 90538985682124980⟩, ⟨.hall 10 9, 38789161183509750⟩, ⟨.hall 12 9, 35770492261110222⟩, ⟨.hall 11 10, 87019313471644950⟩, ⟨.hall 13 10, 64330331932036170⟩, ⟨.hall 9 11, 86675363616025800⟩, ⟨.hall 10 11, 60677877188642175⟩, ⟨.hall 8 12, 77031107238891960⟩, ⟨.hall 6 17, 221057011291349772⟩, ⟨.hall 7 18, 1160924567220709200⟩, ⟨.hall 5 19, 104277725219938116⟩]
  caps := #[0, 0, 21145335866364689179200, 2706288827946480010080, 1293042584027094405120, 207289121206701885120, 218940655144911860160, 135226442186659523700, 74585892095114400, 0, 271524128284568250, 0, 768753784531988640, 1516388883808775044068, 0, 0, 7657484921765078400000, 2734816043487528000000] }

theorem case_49_32_20_checked :
    (Witness.linear .negative case_49_32_20).check 49 32 20 = true := by
  change case_49_32_20.check 49 32 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_33_1_checked :
    (Witness.rising).check 49 33 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_33_2_checked :
    (Witness.rising).check 49 33 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_33_3_checked :
    (Witness.rising).check 49 33 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_33_4_checked :
    (Witness.rising).check 49 33 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_33_5_checked :
    (Witness.rising).check 49 33 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_33_6_checked :
    (Witness.rising).check 49 33 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_33_7_checked :
    (Witness.rising).check 49 33 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_33_8_checked :
    (Witness.rising).check 49 33 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_33_9_checked :
    (Witness.rising).check 49 33 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_33_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_33_10_checked :
    (Witness.linear .positive case_49_33_10).check 49 33 10 = true := by
  change case_49_33_10.check 49 33 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_33_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_49_33_11_checked :
    (Witness.linear .positive case_49_33_11).check 49 33 11 = true := by
  change case_49_33_11.check 49 33 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_33_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_49_33_12_checked :
    (Witness.linear .positive case_49_33_12).check 49 33 12 = true := by
  change case_49_33_12.check 49 33 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_33_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_49_33_13_checked :
    (Witness.linear .positive case_49_33_13).check 49 33 13 = true := by
  change case_49_33_13.check 49 33 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_33_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_49_33_14_checked :
    (Witness.linear .positive case_49_33_14).check 49 33 14 = true := by
  change case_49_33_14.check 49 33 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_33_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_49_33_15_checked :
    (Witness.linear .positive case_49_33_15).check 49 33 15 = true := by
  change case_49_33_15.check 49 33 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_33_16 : Certificate := {
  objectiveScale := 702120582240000
  eta := 66201374024973157370400
  rows := #[⟨.count 2, 8255162702250538794720⟩, ⟨.count 3, 989835496154298874080⟩, ⟨.count 4, 116096470988394536640⟩, ⟨.count 5, 11936325480408529200⟩, ⟨.count 6, 1370678524066051200⟩, ⟨.count 7, 239868741711558960⟩, ⟨.path 6, 577269669763987200⟩, ⟨.privateRow 2 30, 114337433549176437600⟩, ⟨.privateRow 3 28, 273320912579459865120⟩, ⟨.privateRow 3 29, 152722143383542813080⟩, ⟨.privateRow 4 25, 46061651801239650576⟩, ⟨.privateRow 4 26, 70015972357448977860⟩, ⟨.privateRow 4 27, 81292658798150719920⟩, ⟨.privateRow 4 28, 106861524432499516680⟩, ⟨.privateRow 5 20, 167527375163628480⟩, ⟨.privateRow 5 24, 78000745876185420288⟩, ⟨.privateRow 5 26, 47368365327515952720⟩, ⟨.privateRow 5 27, 46488846607906903200⟩, ⟨.privateRow 6 25, 73198040625471762000⟩, ⟨.privateRow 7 15, 5711160516941880⟩, ⟨.privateRow 7 21, 8132692576125237120⟩, ⟨.privateRow 7 24, 22102191200565075600⟩, ⟨.privateRow 7 25, 6065252468992276560⟩, ⟨.privateRow 8 13, 2050160185568880⟩, ⟨.privateRow 8 21, 12387887905281400512⟩, ⟨.privateRow 9 11, 1903720172313960⟩, ⟨.privateRow 9 17, 59967185427889740⟩, ⟨.privateRow 9 19, 1887855837544677000⟩, ⟨.privateRow 9 20, 1572472862331330960⟩, ⟨.privateRow 10 10, 4895280443093040⟩, ⟨.privateRow 10 11, 10543680954354240⟩, ⟨.privateRow 10 13, 59188390811943120⟩, ⟨.privateRow 10 14, 10280088930495384⟩, ⟨.privateRow 10 15, 19037201723139600⟩, ⟨.privateRow 11 8, 3807440344627920⟩, ⟨.privateRow 11 21, 913785682710700800⟩, ⟨.privateRow 12 7, 8376368758181424⟩, ⟨.privateRow 12 13, 13960614596969040⟩, ⟨.privateRow 12 15, 35898723249348960⟩, ⟨.privateRow 12 16, 20940921895453560⟩, ⟨.privateRow 12 17, 25129106274544272⟩, ⟨.privateRow 12 21, 376936594118164080⟩, ⟨.privateRow 13 5, 23558537132385255⟩, ⟨.privateRow 14 4, 102086994240336105⟩, ⟨.privateRow 15 3, 714608959682352735⟩, ⟨.hall 12 6, 34731736889850⟩, ⟨.hall 10 9, 5101808853960⟩, ⟨.hall 9 11, 7344458196075⟩, ⟨.hall 10 11, 4477426707600⟩, ⟨.hall 11 12, 8743654042200⟩, ⟨.hall 11 13, 9851183554212⟩, ⟨.hall 12 13, 59275497625344⟩, ⟨.hall 7 15, 858947849991⟩, ⟨.hall 15 15, 210179105788927275⟩, ⟨.hall 8 17, 19467115184608⟩, ⟨.hall 3 27, 216042230175607836⟩, ⟨.hall 4 27, 1039825087222521600⟩, ⟨.hall 2 29, 6073407760569157008⟩, ⟨.assumptionRow 16, 947185741176840⟩]
  caps := #[0, 107873472297197970000, 0, 6908098471800843240, 0, 280596914881620480, 99785569401975600, 711772460633520, 426046198944239544, 26507659856008320, 479665404507502836, 93864410235204840, 343712116378158528, 1192250900113680, 1743450917093009685, 10083209556555332010, 8180381827943160] }

theorem case_49_33_16_checked :
    (Witness.linear .conditional case_49_33_16).check 49 33 16 = true := by
  change case_49_33_16.check 49 33 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_33_17 : Certificate := {
  objectiveScale := 73046823141600000
  eta := 6085417977105744059382600
  rows := #[⟨.count 2, 705463598390326465369680⟩, ⟨.count 3, 77628233799707738467320⟩, ⟨.count 4, 8101552065466574594880⟩, ⟨.count 5, 756610465884091018200⟩, ⟨.count 6, 95237681020375093200⟩, ⟨.count 7, 22222125571420855080⟩, ⟨.path 5, 133253790426595238400⟩, ⟨.path 6, 25629350582515680000⟩, ⟨.privateRow 2 30, 9003664544020683116580⟩, ⟨.privateRow 2 31, 60377515177550463252360⟩, ⟨.privateRow 3 27, 5258442737894432576490⟩, ⟨.privateRow 3 28, 12912818617755153377280⟩, ⟨.privateRow 3 29, 18536956414160229945900⟩, ⟨.privateRow 4 24, 1111635376798933726740⟩, ⟨.privateRow 4 25, 3024113831333643792744⟩, ⟨.privateRow 4 26, 4871407384192186017180⟩, ⟨.privateRow 4 27, 6995736769174441568280⟩, ⟨.privateRow 4 28, 10388843704639249749900⟩, ⟨.privateRow 5 21, 157142173683618903780⟩, ⟨.privateRow 5 22, 633557335168876215240⟩, ⟨.privateRow 5 23, 1196996557565343995460⟩, ⟨.privateRow 5 24, 1850785601162622644520⟩, ⟨.privateRow 5 25, 2616126187806914712930⟩, ⟨.privateRow 5 26, 4050776032733287297440⟩, ⟨.privateRow 5 27, 3742311765872850190020⟩, ⟨.privateRow 6 18, 11111062785710427540⟩, ⟨.privateRow 6 19, 105819645578194548000⟩, ⟨.privateRow 6 20, 284390297491397847750⟩, ⟨.privateRow 6 21, 492061351938604648200⟩, ⟨.privateRow 6 22, 753964974744636154500⟩, ⟨.privateRow 6 23, 1048672687679907970680⟩, ⟨.privateRow 6 24, 1345232244412798191450⟩, ⟨.privateRow 6 25, 2193993984987900295200⟩, ⟨.privateRow 7 16, 8369371968457205160⟩, ⟨.privateRow 7 17, 57460067548959639564⟩, ⟨.privateRow 7 18, 131569092668888554680⟩, ⟨.privateRow 7 19, 224205374068799698575⟩, ⟨.privateRow 7 20, 338774036772477117240⟩, ⟨.privateRow 7 21, 468251931683510874900⟩, ⟨.privateRow 7 22, 718727032767097370016⟩, ⟨.privateRow 7 23, 386506255474355586570⟩, ⟨.privateRow 8 14, 5144010548940012750⟩, ⟨.privateRow 8 15, 31425228080797168800⟩, ⟨.privateRow 8 16, 68147851752357288912⟩, ⟨.privateRow 8 17, 116323225213363488320⟩, ⟨.privateRow 8 18, 174690598242002832990⟩, ⟨.privateRow 8 19, 240210595462501623960⟩, ⟨.privateRow 8 20, 207818026177176515100⟩, ⟨.privateRow 9 12, 3228855852257731080⟩, ⟨.privateRow 9 13, 18518437976184045900⟩, ⟨.privateRow 9 14, 41301728334761993280⟩, ⟨.privateRow 9 15, 70863889322197615644⟩, ⟨.privateRow 9 16, 106721072188675464520⟩, ⟨.privateRow 9 17, 53394829497997332345⟩, ⟨.privateRow 10 10, 2267563833818454600⟩, ⟨.privateRow 10 11, 12454158287279819880⟩, ⟨.privateRow 10 12, 27513107850330582480⟩, ⟨.privateRow 10 13, 56276811512039827800⟩, ⟨.privateRow 11 8, 1763660759636575800⟩, ⟨.privateRow 11 9, 9826109946546636600⟩, ⟨.privateRow 11 10, 20349931841960490000⟩, ⟨.privateRow 12 6, 1455020126700175035⟩, ⟨.privateRow 12 7, 7760107342400933520⟩, ⟨.privateRow 13 4, 2054146061223776520⟩, ⟨.hall 4 28, 1155988404109380441600⟩, ⟨.hall 3 29, 5296273261188637127400⟩, ⟨.hall 2 30, 15102921170615339421360⟩, ⟨.assumptionRow 17, 68916720976972440⟩]
  caps := #[0, 23796948548250526829400, 1003022179152975730980, 131838264507834937800, 0, 26938103852583771540, 9252500671604619000, 13586677510005491190, 14299555492733185904, 3256513466551230600, 867006657548248800, 271536781743262200, 52328375098859228985, 93953109850862217120, 157351571533007192880, 39126286410989520600, 7589904418218840960] }

theorem case_49_33_17_checked :
    (Witness.linear .conditional case_49_33_17).check 49 33 17 = true := by
  change case_49_33_17.check 49 33 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_33_18 : Certificate := {
  objectiveScale := 230097492896040000
  eta := 18589919146772116317174000
  rows := #[⟨.count 2, 2110035267257553031556160⟩, ⟨.count 3, 223351409528983668572640⟩, ⟨.count 4, 21511017553135387717440⟩, ⟨.count 5, 1862425762176224044800⟩, ⟨.count 6, 126983574693833457600⟩, ⟨.count 7, 44444251142841710160⟩, ⟨.path 5, 539729499983690016000⟩, ⟨.path 6, 53052755705807457600⟩, ⟨.privateRow 2 30, 52962732611886371274000⟩, ⟨.privateRow 2 31, 216087949056496394797920⟩, ⟨.privateRow 3 27, 17931668041452957131340⟩, ⟨.privateRow 3 28, 45396627953045461092000⟩, ⟨.privateRow 3 29, 66279076811446373194320⟩, ⟨.privateRow 4 24, 3235964761781189277840⟩, ⟨.privateRow 4 25, 9679957898910924472848⟩, ⟨.privateRow 4 26, 16499928236779984896900⟩, ⟨.privateRow 4 27, 25119467467351821804240⟩, ⟨.privateRow 4 28, 39425225353067942748360⟩, ⟨.privateRow 5 21, 395765474462447609520⟩, ⟨.privateRow 5 22, 1799236316673816443280⟩, ⟨.privateRow 5 23, 3728731578023648556360⟩, ⟨.privateRow 5 24, 6164629272803301588288⟩, ⟨.privateRow 5 25, 9352869374428725124980⟩, ⟨.privateRow 5 26, 15628856187595480109280⟩, ⟨.privateRow 5 27, 16109982842824337987520⟩, ⟨.privateRow 6 17, 7695974223868694400⟩, ⟨.privateRow 6 18, 14814750380947236720⟩, ⟨.privateRow 6 19, 257494470906940066800⟩, ⟨.privateRow 6 20, 787033613987821950750⟩, ⟨.privateRow 6 21, 1489033584207451854000⟩, ⟨.privateRow 6 22, 2467361402731569544200⟩, ⟨.privateRow 6 23, 3718502345617756416720⟩, ⟨.privateRow 6 24, 6256586544810752650500⟩, ⟨.privateRow 6 25, 7255700365144872841200⟩, ⟨.privateRow 6 26, 4380933326937254287200⟩, ⟨.privateRow 7 16, 15007149736543954080⟩, ⟨.privateRow 7 17, 135237507048932632344⟩, ⟨.privateRow 7 18, 351321223319605899360⟩, ⟨.privateRow 7 19, 656346351698751683970⟩, ⟨.privateRow 7 20, 1080267410431111771440⟩, ⟨.privateRow 7 21, 1627506148992632148240⟩, ⟨.privateRow 7 22, 2746654720627617687888⟩, ⟨.privateRow 7 23, 3403159801794736663680⟩, ⟨.privateRow 7 24, 372485152435244808960⟩, ⟨.privateRow 8 14, 7818896034388819380⟩, ⟨.privateRow 8 15, 70482297266930792880⟩, ⟨.privateRow 8 16, 174320229482479152072⟩, ⟨.privateRow 8 17, 326473202839392809200⟩, ⟨.privateRow 8 18, 535800138777591728040⟩, ⟨.privateRow 8 19, 805640235001987825440⟩, ⟨.privateRow 8 20, 1367072243486297788440⟩, ⟨.privateRow 8 21, 773329969885445756784⟩, ⟨.privateRow 9 12, 4178519338215887280⟩, ⟨.privateRow 9 13, 39506001015859297920⟩, ⟨.privateRow 9 14, 100111798028825266320⟩, ⟨.privateRow 9 15, 189628804876124630016⟩, ⟨.privateRow 9 16, 312207146916999173840⟩, ⟨.privateRow 9 17, 470368324595074765860⟩, ⟨.privateRow 9 18, 407758367627976324960⟩, ⟨.privateRow 10 10, 2267563833818454600⟩, ⟨.privateRow 10 11, 24908316574559639760⟩, ⟨.privateRow 10 12, 68253671397935483460⟩, ⟨.privateRow 10 13, 132755555361734978400⟩, ⟨.privateRow 10 14, 220951419967270216224⟩, ⟨.privateRow 10 15, 101586859755066766080⟩, ⟨.privateRow 11 8, 2116392911563890960⟩, ⟨.privateRow 11 9, 18140510670547636800⟩, ⟨.privateRow 11 10, 52909822789097274000⟩, ⟨.privateRow 11 11, 119047101275468866500⟩, ⟨.privateRow 12 6, 1455020126700175035⟩, ⟨.privateRow 12 7, 17072236153282053744⟩, ⟨.privateRow 12 8, 46560644054405601120⟩, ⟨.privateRow 13 4, 4108292122447553040⟩, ⟨.privateRow 13 5, 17460241520402100420⟩, ⟨.hall 4 28, 6213437672087919873600⟩, ⟨.hall 3 29, 21881174673367912246344⟩, ⟨.hall 2 30, 56721378152084758912800⟩, ⟨.assumptionRow 18, 151031611527572160⟩]
  caps := #[0, 0, 0, 587350485925626806460, 0, 0, 24754721913001256220, 0, 57127507181322806452, 3215228967400665600, 6134577603562100880, 2952130485098318040, 85720666736296727289, 0, 1344666870219449810880, 416204815615933417920, 107200274363664672960] }

theorem case_49_33_18_checked :
    (Witness.linear .conditional case_49_33_18).check 49 33 18 = true := by
  change case_49_33_18.check 49 33 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_33_19 : Certificate := {
  objectiveScale := 222172030080000
  eta := 18914678292849473534400
  rows := #[⟨.count 2, 2384752185454251412800⟩, ⟨.count 3, 285610242171820325760⟩, ⟨.count 4, 31662673905925782720⟩, ⟨.count 5, 2871897859947916800⟩, ⟨.count 6, 195811217723721600⟩, ⟨.path 6, 175143775890283200⟩, ⟨.privateRow 2 30, 119237609272712570640⟩, ⟨.privateRow 2 31, 311977854398467136880⟩, ⟨.privateRow 3 27, 26775960203608155540⟩, ⟨.privateRow 3 28, 67202409922781253120⟩, ⟨.privateRow 3 29, 94853401505592289560⟩, ⟨.privateRow 4 24, 4496315086980957240⟩, ⟨.privateRow 4 25, 13688183174976758448⟩, ⟨.privateRow 4 26, 23370068835326172960⟩, ⟨.privateRow 4 27, 36060267503971030320⟩, ⟨.privateRow 4 28, 57402058475708987040⟩, ⟨.privateRow 5 20, 37893096763201680⟩, ⟨.privateRow 5 21, 576623242192667670⟩, ⟨.privateRow 5 22, 2489832876794131440⟩, ⟨.privateRow 5 23, 5169416147906250240⟩, ⟨.privateRow 5 24, 8586974601244271232⟩, ⟨.privateRow 5 25, 13246628879009766240⟩, ⟨.privateRow 5 26, 22753807419545682480⟩, ⟨.privateRow 5 27, 24393182447932618320⟩, ⟨.privateRow 6 17, 11125637370666000⟩, ⟨.privateRow 6 18, 70165686351000240⟩, ⟨.privateRow 6 19, 374398300555078800⟩, ⟨.privateRow 6 20, 1077981547572779850⟩, ⟨.privateRow 6 21, 2026879212033046800⟩, ⟨.privateRow 6 22, 3381822906103441800⟩, ⟨.privateRow 6 23, 5190629029826320080⟩, ⟨.privateRow 6 24, 9017514516214304100⟩, ⟨.privateRow 6 25, 10995343795236200400⟩, ⟨.privateRow 6 26, 8330135553996656400⟩, ⟨.privateRow 7 14, 1882800170420400⟩, ⟨.privateRow 7 15, 8566740775412820⟩, ⟨.privateRow 7 16, 50287880915410320⟩, ⟨.privateRow 7 17, 195321689679412296⟩, ⟨.privateRow 7 18, 476473963127722560⟩, ⟨.privateRow 7 19, 878090929479814050⟩, ⟨.privateRow 7 20, 1453898291598632880⟩, ⟨.privateRow 7 21, 2233063762124275080⟩, ⟨.privateRow 7 22, 2671844065840181232⟩, ⟨.privateRow 7 23, 7554641543803333980⟩, ⟨.privateRow 7 24, 781613110747188720⟩, ⟨.privateRow 8 11, 253829356308528⟩, ⟨.privateRow 8 12, 1087840098465120⟩, ⟨.privateRow 8 13, 6443360583216480⟩, ⟨.privateRow 8 14, 31411382843180340⟩, ⟨.privateRow 8 15, 104531544007057440⟩, ⟨.privateRow 8 16, 235680557332468248⟩, ⟨.privateRow 8 17, 431932954651678480⟩, ⟨.privateRow 8 18, 709611694230028590⟩, ⟨.privateRow 8 19, 971441207929352160⟩, ⟨.privateRow 8 20, 2131532019600863880⟩, ⟨.privateRow 8 21, 1842801126799913280⟩, ⟨.privateRow 9 9, 237965021539245⟩, ⟨.privateRow 9 10, 1015317425234112⟩, ⟨.privateRow 9 11, 4895280443093040⟩, ⟨.privateRow 9 12, 21380241935218320⟩, ⟨.privateRow 9 13, 63457339077132000⟩, ⟨.privateRow 9 14, 137413983347025840⟩, ⟨.privateRow 9 15, 249768086607591552⟩, ⟨.privateRow 9 16, 408665263656730080⟩, ⟨.privateRow 9 17, 622040566303586430⟩, ⟨.privateRow 9 18, 985039209160166160⟩, ⟨.privateRow 10 7, 287957673123120⟩, ⟨.privateRow 10 8, 917865083079945⟩, ⟨.privateRow 10 9, 4568928413553504⟩, ⟨.privateRow 10 10, 16783818662033280⟩, ⟨.privateRow 10 11, 45940324158257760⟩, ⟨.privateRow 10 12, 97905608861860800⟩, ⟨.privateRow 10 13, 176675121446176080⟩, ⟨.privateRow 10 14, 288821546142489360⟩, ⟨.privateRow 10 15, 304595227570233600⟩, ⟨.privateRow 11 5, 453266707693800⟩, ⟨.privateRow 11 6, 1439788365615600⟩, ⟨.privateRow 11 7, 4589325415399725⟩, ⟨.privateRow 11 8, 16317601476976800⟩, ⟨.privateRow 11 9, 41959546655083200⟩, ⟨.privateRow 11 10, 87864007952952000⟩, ⟨.privateRow 11 11, 159096614400523800⟩, ⟨.privateRow 11 12, 27443238847642800⟩, ⟨.privateRow 12 3, 944703243403920⟩, ⟨.privateRow 12 4, 1994373513852720⟩, ⟨.privateRow 12 5, 6335068808708640⟩, ⟨.privateRow 12 6, 12340186116963705⟩, ⟨.privateRow 12 7, 64617701848828128⟩, ⟨.privateRow 12 8, 34616625990443640⟩, ⟨.privateRow 13 2, 5668219460423520⟩, ⟨.privateRow 13 3, 8974680812337240⟩, ⟨.privateRow 13 4, 25340275234834560⟩, ⟨.privateRow 14 0, 11667085056038412⟩, ⟨.hall 4 28, 10064021379903691200⟩, ⟨.hall 3 29, 32854511517804168192⟩, ⟨.hall 2 30, 82618016500050071040⟩, ⟨.assumptionRow 19, 31064048578332⟩]
  caps := #[0, 0, 1341623032686284040, 154193574262168980, 0, 248934528967905528, 0, 532986903428364, 49579056091237582, 1532490503720253, 5255291827066662, 82537876347436218, 0, 0, 88634939818834332, 1154015816670862992, 360793608709387392] }

theorem case_49_33_19_checked :
    (Witness.linear .conditional case_49_33_19).check 49 33 19 = true := by
  change case_49_33_19.check 49 33 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_33_20 : Certificate := {
  objectiveScale := 26742692548000000
  eta := 1865654968134836046168000
  rows := #[⟨.count 2, 233719413590517922267200⟩, ⟨.count 3, 27384417507159681368400⟩, ⟨.count 4, 2883756018853508198400⟩, ⟨.count 5, 244067892220674522000⟩, ⟨.count 6, 10240610862405924000⟩, ⟨.path 5, 24241593532220064000⟩, ⟨.path 6, 13035142823150448000⟩, ⟨.privateRow 7 15, 170676847706765400⟩, ⟨.privateRow 7 16, 837868161469575600⟩, ⟨.privateRow 8 13, 122537223994600800⟩, ⟨.privateRow 8 14, 597368966973678900⟩, ⟨.privateRow 9 11, 113784565137843600⟩, ⟨.privateRow 9 12, 367611671983802400⟩, ⟨.privateRow 9 13, 199122988991226300⟩, ⟨.privateRow 10 9, 68270739082706160⟩, ⟨.privateRow 10 10, 292588881783026400⟩, ⟨.hall 12 5, 2214294942974400⟩, ⟨.hall 11 6, 2516244253380000⟩, ⟨.hall 10 7, 2687309080092000⟩, ⟨.hall 11 7, 1100856860853750⟩, ⟨.hall 10 8, 233225010837000⟩, ⟨.hall 12 8, 719645856466680⟩, ⟨.hall 13 8, 387501615020520⟩, ⟨.hall 9 9, 1169344951722675⟩, ⟨.hall 9 10, 52214554665000⟩, ⟨.hall 13 10, 264205646604900⟩, ⟨.hall 8 11, 754428374856156⟩, ⟨.hall 7 12, 160490939489496⟩, ⟨.hall 7 13, 486138389753016⟩, ⟨.hall 6 15, 732058767081180⟩, ⟨.hall 5 20, 10484012096797250⟩, ⟨.hall 4 22, 38800392365306880⟩]
  caps := #[0, 0, 0, 34213873196134231600, 0, 0, 2794531960744524000, 1821373998663923600, 6019641128734764300, 8185414662058725, 703387284014812540, 6439546766134482000, 10017439203246675200, 0, 0, 267319954709808000000, 101836173222784000000] }

theorem case_49_33_20_checked :
    (Witness.linear .negative case_49_33_20).check 49 33 20 = true := by
  change case_49_33_20.check 49 33 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_33_21 : Certificate := {
  objectiveScale := 622
  eta := 5194090
  rows := #[⟨.assumptionRow 21, 245⟩]
  caps := #[0, 0, 2734424, 1067605, 623770, 306945, 137394, 78132, 35020, 18991, 10530, 4560, 14407092, 14247530, 9972948, 5798700, 2915976] }

theorem case_49_33_21_checked :
    (Witness.linear .conditional case_49_33_21).check 49 33 21 = true := by
  change case_49_33_21.check 49 33 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_34_1_checked :
    (Witness.rising).check 49 34 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_34_2_checked :
    (Witness.rising).check 49 34 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_34_3_checked :
    (Witness.rising).check 49 34 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_34_4_checked :
    (Witness.rising).check 49 34 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_34_5_checked :
    (Witness.rising).check 49 34 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_34_6_checked :
    (Witness.rising).check 49 34 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_34_7_checked :
    (Witness.rising).check 49 34 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_34_8_checked :
    (Witness.rising).check 49 34 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_34_9_checked :
    (Witness.rising).check 49 34 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_34_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0, 0] }

theorem case_49_34_10_checked :
    (Witness.linear .positive case_49_34_10).check 49 34 10 = true := by
  change case_49_34_10.check 49 34 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_34_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_49_34_11_checked :
    (Witness.linear .positive case_49_34_11).check 49 34 11 = true := by
  change case_49_34_11.check 49 34 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_34_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_49_34_12_checked :
    (Witness.linear .positive case_49_34_12).check 49 34 12 = true := by
  change case_49_34_12.check 49 34 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_34_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_49_34_13_checked :
    (Witness.linear .positive case_49_34_13).check 49 34 13 = true := by
  change case_49_34_13.check 49 34 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_34_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_49_34_14_checked :
    (Witness.linear .positive case_49_34_14).check 49 34 14 = true := by
  change case_49_34_14.check 49 34 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_34_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_49_34_15_checked :
    (Witness.linear .positive case_49_34_15).check 49 34 15 = true := by
  change case_49_34_15.check 49 34 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_34_16 : Certificate := {
  objectiveScale := 736
  eta := 2142226440
  rows := #[⟨.assumptionRow 16, 1997⟩]
  caps := #[0, 0, 608732260, 174819228, 50831802, 14998828, 4504422, 1382238, 435721, 142164, 48546, 17710, 2465309, 1189440, 359710, 75926] }

theorem case_49_34_16_checked :
    (Witness.linear .conditional case_49_34_16).check 49 34 16 = true := by
  change case_49_34_16.check 49 34 16 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_34_17 : Certificate := {
  objectiveScale := 5171151242400000
  eta := 1056336171177890141098560
  rows := #[⟨.count 2, 106743561227902155997440⟩, ⟨.count 3, 10245637939505925116160⟩, ⟨.count 4, 853803161625493759680⟩, ⟨.count 5, 57800987730932846400⟩, ⟨.count 6, 4954370376937101120⟩, ⟨.path 5, 39395888493326164800⟩, ⟨.privateRow 2 31, 472316642601336973440⟩, ⟨.privateRow 2 32, 7438987120971057331680⟩, ⟨.privateRow 3 28, 985506840812405031120⟩, ⟨.privateRow 3 29, 1689440298535551481920⟩, ⟨.privateRow 3 30, 2316168151218094773600⟩, ⟨.privateRow 4 24, 61634726713086555600⟩, ⟨.privateRow 4 25, 176361823279024863480⟩, ⟨.privateRow 4 26, 482307956194826794032⟩, ⟨.privateRow 4 27, 652841513210982595500⟩, ⟨.privateRow 4 28, 865913844769117784640⟩, ⟨.privateRow 4 29, 1194416125039919461680⟩, ⟨.privateRow 5 21, 16881558321415307520⟩, ⟨.privateRow 5 22, 38809234619340625440⟩, ⟨.privateRow 5 23, 103569933117875590080⟩, ⟨.privateRow 5 24, 185788889135141292000⟩, ⟨.privateRow 5 25, 257957550959191731648⟩, ⟨.privateRow 5 26, 330291358462473408000⟩, ⟨.privateRow 5 27, 467362272224399872320⟩, ⟨.privateRow 5 28, 341851556008659977280⟩, ⟨.privateRow 6 18, 2327052752803789920⟩, ⟨.privateRow 6 19, 8670148159639926960⟩, ⟨.privateRow 6 20, 24221366287248049920⟩, ⟨.privateRow 6 21, 48408327224656258860⟩, ⟨.privateRow 6 22, 78090314036484784320⟩, ⟨.privateRow 6 23, 110097119487491136000⟩, ⟨.privateRow 6 24, 139548098950395014880⟩, ⟨.privateRow 6 25, 195078333591898356600⟩, ⟨.privateRow 6 26, 41836905405246631680⟩, ⟨.privateRow 7 8, 27524279871872784⟩, ⟨.privateRow 7 15, 84690091913454720⟩, ⟨.privateRow 7 16, 1284466394020729920⟩, ⟨.privateRow 7 17, 5955253281368838720⟩, ⟨.privateRow 7 18, 13541945696961409728⟩, ⟨.privateRow 7 19, 24466026552775808000⟩, ⟨.privateRow 7 20, 37777074124145396040⟩, ⟨.privateRow 7 21, 52846617353995745280⟩, ⟨.privateRow 7 22, 67342738086515411520⟩, ⟨.privateRow 7 23, 30827193456497518080⟩, ⟨.privateRow 8 14, 1074505541151956760⟩, ⟨.privateRow 8 15, 4094236630941076620⟩, ⟨.privateRow 8 16, 8451205024295484360⟩, ⟨.privateRow 8 17, 14402079442957434228⟩, ⟨.privateRow 8 18, 20872578902836861200⟩, ⟨.privateRow 8 19, 31850752614232787235⟩, ⟨.privateRow 9 12, 904369195790105760⟩, ⟨.privateRow 9 13, 3218223492711279360⟩, ⟨.privateRow 9 14, 5091991776296465040⟩, ⟨.privateRow 9 15, 12911389467169415040⟩, ⟨.privateRow 9 16, 5449807414630811232⟩, ⟨.privateRow 10 10, 880776955899929088⟩, ⟨.privateRow 10 11, 3008010585997525680⟩, ⟨.privateRow 10 12, 5081405514807283200⟩, ⟨.privateRow 11 8, 1032160495195229400⟩, ⟨.privateRow 11 9, 1761553911799858176⟩, ⟨.privateRow 12 6, 801442266857472240⟩, ⟨.hall 3 30, 407856554901402647040⟩, ⟨.hall 2 31, 1542409035994991053890⟩, ⟨.assumptionRow 17, 5191517622677760⟩]
  caps := #[0, 552585987843500318400, 0, 39657918717384995610, 0, 7268500482881132352, 1183566629166888288, 1056638705896433688, 7839540724020682821, 208373528216832000, 67632293756755200, 6471543310458122160, 5191517622677760, 50111901912268627200, 14227173611548128000, 3337468012788180480] }

theorem case_49_34_17_checked :
    (Witness.linear .conditional case_49_34_17).check 49 34 17 = true := by
  change case_49_34_17.check 49 34 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_34_18 : Certificate := {
  objectiveScale := 7057100519040000
  eta := 1259668485817765708164480
  rows := #[⟨.count 2, 128942443430164993749120⟩, ⟨.count 3, 12480058979504557721280⟩, ⟨.count 4, 1017297384064418096640⟩, ⟨.count 5, 57800987730932846400⟩, ⟨.count 6, 4954370376937101120⟩, ⟨.path 5, 47359166821196630400⟩, ⟨.privateRow 2 31, 2597741534307353353920⟩, ⟨.privateRow 2 32, 11689836904383090092640⟩, ⟨.privateRow 3 28, 1353368841299984789280⟩, ⟨.privateRow 3 29, 2634073583738225428800⟩, ⟨.privateRow 3 30, 3814865190241567862400⟩, ⟨.privateRow 3 31, 5903958032516712168000⟩, ⟨.privateRow 4 24, 55795647340267829280⟩, ⟨.privateRow 4 25, 219506131978185452400⟩, ⟨.privateRow 4 26, 658518395934556357200⟩, ⟨.privateRow 4 27, 977559204999401764740⟩, ⟨.privateRow 4 28, 1385159384551997854800⟩, ⟨.privateRow 4 29, 2070926817559708268160⟩, ⟨.privateRow 5 21, 13578644736790573440⟩, ⟨.privateRow 5 22, 40047827213574900720⟩, ⟨.privateRow 5 23, 127634017805855795520⟩, ⟨.privateRow 5 24, 253223374821229612800⟩, ⟨.privateRow 5 25, 381486519024156786240⟩, ⟨.privateRow 5 26, 532594815520738370400⟩, ⟨.privateRow 5 27, 823526453766433697280⟩, ⟨.privateRow 5 28, 727466717013597681120⟩, ⟨.privateRow 6 18, 1426258138815226080⟩, ⟨.privateRow 6 19, 7183837046558796624⟩, ⟨.privateRow 6 20, 24955347083831324160⟩, ⟨.privateRow 6 21, 59039580325167121680⟩, ⟨.privateRow 6 22, 104867506311835307040⟩, ⟨.privateRow 6 23, 161154658649815150320⟩, ⟨.privateRow 6 24, 223772395358325733920⟩, ⟨.privateRow 6 25, 347012358484636124280⟩, ⟨.privateRow 6 26, 282123868686696036000⟩, ⟨.privateRow 7 13, 36699039829163712⟩, ⟨.privateRow 7 15, 84690091913454720⟩, ⟨.privateRow 7 16, 550485597437455680⟩, ⟨.privateRow 7 17, 4804237941272340480⟩, ⟨.privateRow 7 18, 13817188495680137568⟩, ⟨.privateRow 7 19, 28992241465039332480⟩, ⟨.privateRow 7 20, 49612514469050693160⟩, ⟨.privateRow 7 21, 75809730847101039360⟩, ⟨.privateRow 7 22, 84224296407930719040⟩, ⟨.privateRow 7 23, 208634041428795702720⟩, ⟨.privateRow 8 14, 407571067333500840⟩, ⟨.privateRow 8 15, 3251305559864972610⟩, ⟨.privateRow 8 16, 8319839143088818800⟩, ⟨.privateRow 8 17, 16425114013540083852⟩, ⟨.privateRow 8 18, 27562508038361496200⟩, ⟨.privateRow 8 19, 22458092107956199695⟩, ⟨.privateRow 8 20, 96954275848671881640⟩, ⟨.privateRow 9 12, 314563198535688960⟩, ⟨.privateRow 9 13, 2413667619533459520⟩, ⟨.privateRow 9 14, 5963593972239103200⟩, ⟨.privateRow 9 15, 11309976820078634880⟩, ⟨.privateRow 9 16, 18716510312873493120⟩, ⟨.privateRow 9 17, 24588356685539687040⟩, ⟨.privateRow 10 10, 275242798718727840⟩, ⟨.privateRow 10 11, 2123301590115900480⟩, ⟨.privateRow 10 12, 5271958221612556320⟩, ⟨.privateRow 10 13, 9839930054194520280⟩, ⟨.privateRow 10 14, 4954370376937101120⟩, ⟨.privateRow 11 8, 309648148558568820⟩, ⟨.privateRow 11 9, 2312039509237313856⟩, ⟨.privateRow 11 10, 5072331576387984480⟩, ⟨.privateRow 12 6, 534294844571648160⟩, ⟨.privateRow 12 7, 1986908953250816595⟩, ⟨.privateRow 13 4, 1009223595302002080⟩, ⟨.hall 4 29, 87802452791274180960⟩, ⟨.hall 3 30, 734844999779251320960⟩, ⟨.assumptionRow 18, 5251821201781440⟩]
  caps := #[0, 308806981036107016320, 303169117416561807840, 0, 16055465224954781340, 3184874164398738240, 0, 488203936301170672, 9363943033264420739, 120299837390990400, 58417172379045480, 303744313626828360, 15190682696802311985, 0, 55763636879847124800, 16324037889827690880] }

theorem case_49_34_18_checked :
    (Witness.linear .conditional case_49_34_18).check 49 34 18 = true := by
  change case_49_34_18.check 49 34 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_34_19 : Certificate := {
  objectiveScale := 21507537922510640000
  eta := 4846434327005076030898632960
  rows := #[⟨.count 2, 497404628702659461710646720⟩, ⟨.count 3, 47915497951131181859167680⟩, ⟨.count 4, 3796360901617637498745600⟩, ⟨.count 5, 209539400413960511294400⟩, ⟨.path 5, 173675414584529664206400⟩, ⟨.path 6, 2059907614479968853600⟩, ⟨.privateRow 2 31, 11545004670455065464935280⟩, ⟨.privateRow 2 32, 47942614814714164984158720⟩, ⟨.privateRow 3 28, 5260671535098726248261760⟩, ⟨.privateRow 3 29, 10557498888308096663178240⟩, ⟨.privateRow 3 30, 15592196560215296869848000⟩, ⟨.privateRow 3 31, 24757696451263593116819520⟩, ⟨.privateRow 4 24, 229524881041678593674160⟩, ⟨.privateRow 4 25, 824804600649070051810800⟩, ⟨.privateRow 4 26, 2532715058650623874163136⟩, ⟨.privateRow 4 27, 3867542668522968201847080⟩, ⟨.privateRow 4 28, 5653866057051981560631840⟩, ⟨.privateRow 4 29, 8738409289616312028362640⟩, ⟨.privateRow 5 21, 64094404832505568160640⟩, ⟨.privateRow 5 22, 151607919123042016995360⟩, ⟨.privateRow 5 23, 472256026815329488480320⟩, ⟨.privateRow 5 24, 960183487779266107637280⟩, ⟨.privateRow 5 25, 1487976259880783113144704⟩, ⟨.privateRow 5 26, 2155174362492999729401520⟩, ⟨.privateRow 5 27, 3491501617093796911725120⟩, ⟨.privateRow 5 28, 3326746127748702470491680⟩, ⟨.privateRow 6 17, 616292354158707386160⟩, ⟨.privateRow 6 18, 10084783977142484500800⟩, ⟨.privateRow 6 19, 30937876178767110785232⟩, ⟨.privateRow 6 20, 92032991554366969666560⟩, ⟨.privateRow 6 21, 214931958512849200923300⟩, ⟨.privateRow 6 22, 390553269006860852143680⟩, ⟨.privateRow 6 23, 618552092790622646575920⟩, ⟨.privateRow 6 24, 893870430471789192886464⟩, ⟨.privateRow 6 25, 1462769902595691981050760⟩, ⟨.privateRow 6 26, 1594553750993295577124640⟩, ⟨.privateRow 6 27, 39442710666157272714240⟩, ⟨.privateRow 7 14, 117389019839753787840⟩, ⟨.privateRow 7 15, 1453817861092335372480⟩, ⟨.privateRow 7 16, 5272723474468940970480⟩, ⟨.privateRow 7 17, 20318972161353746549760⟩, ⟨.privateRow 7 18, 49960766843799212104704⟩, ⟨.privateRow 7 19, 103811023211622266379840⟩, ⟨.privateRow 7 20, 180984521337940402402320⟩, ⟨.privateRow 7 21, 285490096250281212026880⟩, ⟨.privateRow 7 22, 415381046702968778271840⟩, ⟨.privateRow 7 23, 685152753196706958106944⟩, ⟨.privateRow 7 24, 419284231612640591717520⟩, ⟨.privateRow 8 12, 239669248839497316840⟩, ⟨.privateRow 8 13, 924438531238061079240⟩, ⟨.privateRow 8 14, 4148121614529761253000⟩, ⟨.privateRow 8 15, 13481395247221724072250⟩, ⟨.privateRow 8 16, 30067596672591481567200⟩, ⟨.privateRow 8 17, 58023925144042300406964⟩, ⟨.privateRow 8 18, 98743730521872894538080⟩, ⟨.privateRow 8 19, 153777781786642465917465⟩, ⟨.privateRow 8 20, 223611409167250996611720⟩, ⟨.privateRow 8 21, 257045269380360872310900⟩, ⟨.privateRow 9 9, 48336655228133912640⟩, ⟨.privateRow 9 10, 205430784719569128720⟩, ⟨.privateRow 9 11, 931286224062046716864⟩, ⟨.privateRow 9 12, 3580365105112490529120⟩, ⟨.privateRow 9 13, 10429562916531971150400⟩, ⟨.privateRow 9 14, 21775663180274327644320⟩, ⟨.privateRow 9 15, 39816221183829216584640⟩, ⟨.privateRow 9 16, 65984368051925604144864⟩, ⟨.privateRow 9 17, 101528458936960387171840⟩, ⟨.privateRow 9 18, 71079051512970918537120⟩, ⟨.privateRow 10 7, 68476928239856376240⟩, ⟨.privateRow 10 8, 217514948526602606880⟩, ⟨.privateRow 10 9, 1078511619777737925780⟩, ⟨.privateRow 10 10, 3697754124952244316960⟩, ⟨.privateRow 10 11, 9860677666539318178560⟩, ⟨.privateRow 10 12, 19910983749742854014400⟩, ⟨.privateRow 10 13, 35025948794686536446760⟩, ⟨.privateRow 10 14, 44933315275934847609120⟩, ⟨.privateRow 11 5, 129745758770254186560⟩, ⟨.privateRow 11 6, 410861569439138257440⟩, ⟨.privateRow 11 7, 1595109622528419117120⟩, ⟨.privateRow 11 8, 4930338833269659089280⟩, ⟨.privateRow 11 9, 12161502455398492420224⟩, ⟨.privateRow 11 10, 21834357690194204538240⟩, ⟨.privateRow 12 3, 338960794787289062388⟩, ⟨.privateRow 12 4, 713601673236398026080⟩, ⟨.privateRow 12 5, 1129869315957630207960⟩, ⟨.privateRow 12 6, 11963322168963143378400⟩, ⟨.privateRow 13 2, 4067529537447468748656⟩, ⟨.hall 4 29, 575781403412008353976416⟩, ⟨.hall 3 30, 3306507882054071369875200⟩, ⟨.assumptionRow 19, 7362425267286213696⟩]
  caps := #[0, 2058708484024468937918400, 501011524458279713701680, 48793452035542281052128, 16512112289328452267328, 15879142739401016714496, 3606600698941476004700, 5582217299386781347488, 6714191602503299914333, 0, 10787239611642927525932, 188131350216868570512, 0, 75367493575435663073472, 421703211001903692054336, 145323863723301458065728] }

theorem case_49_34_19_checked :
    (Witness.linear .conditional case_49_34_19).check 49 34 19 = true := by
  change case_49_34_19.check 49 34 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_34_20 : Certificate := {
  objectiveScale := 2298234052291136960000
  eta := 620437363970919687601244035200
  rows := #[⟨.count 2, 64481935627724104952131269600⟩, ⟨.count 3, 6228201227739564147942067200⟩, ⟨.count 4, 489527179831802863900749600⟩, ⟨.count 5, 26808717405903771297960000⟩, ⟨.path 5, 22560542278094753556624000⟩, ⟨.path 6, 239512842910052982270000⟩, ⟨.privateRow 5 21, 4587269422787978644317600⟩, ⟨.privateRow 5 23, 56987673571406873844806400⟩, ⟨.privateRow 5 25, 241600161262004786937215520⟩, ⟨.privateRow 5 26, 167554483786898570612250000⟩, ⟨.privateRow 6 23, 97941180922901777808547200⟩, ⟨.privateRow 6 26, 886385559830531691681550800⟩, ⟨.privateRow 7 16, 134043587029518856489800⟩, ⟨.privateRow 7 17, 292458735337132050523200⟩, ⟨.privateRow 7 18, 965113826612535766726560⟩, ⟨.privateRow 7 19, 2541863576263468686028800⟩, ⟨.privateRow 7 20, 5853236633622323400054600⟩, ⟨.privateRow 7 23, 188018471406738449369692800⟩, ⟨.privateRow 8 14, 120295526821363076337000⟩, ⟨.privateRow 8 15, 234576277301657998857150⟩, ⟨.privateRow 8 16, 710837203944418178355000⟩, ⟨.privateRow 8 17, 1720226033545491991619100⟩, ⟨.privateRow 8 18, 3683716354663073759830800⟩, ⟨.privateRow 8 24, 231969874220528465536515000⟩, ⟨.privateRow 9 12, 102128447260585795420800⟩, ⟨.privateRow 9 13, 192472842914180922139200⟩, ⟨.privateRow 9 14, 491493152441569140462600⟩, ⟨.privateRow 10 10, 89362391353012570993200⟩, ⟨.privateRow 10 11, 172341754752238529772600⟩, ⟨.hall 12 7, 138331875159462184200⟩, ⟨.hall 10 8, 185171521952587060800⟩, ⟨.hall 11 8, 126303016449943733400⟩, ⟨.hall 9 9, 98942830548839038944⟩, ⟨.hall 9 10, 29525380468818015600⟩, ⟨.hall 8 11, 85821280408295100900⟩, ⟨.hall 7 12, 26115217717534662255⟩, ⟨.hall 5 18, 24021252519576444000⟩, ⟨.hall 6 18, 113269950321685264080⟩, ⟨.hall 4 23, 3701667092280236109888⟩, ⟨.hall 3 25, 34312621162031258389200⟩, ⟨.hall 2 29, 15401572116469396847544555⟩]
  caps := #[0, 394767048140665071566494800, 83116000392969491095948800, 2585516001656629746479775, 6855076059782170421401200, 0, 239512842910052982270000, 479040084844558068936720, 1316526907379926706982350, 6113722115743250430240, 2312607711725589528118440, 236017146000038310107200, 414995625478386552600, 0, 89079551866804468569600000, 35631820746721787427840000] }

theorem case_49_34_20_checked :
    (Witness.linear .negative case_49_34_20).check 49 34 20 = true := by
  change case_49_34_20.check 49 34 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_34_21 : Certificate := {
  objectiveScale := 18
  eta := 139150
  rows := #[⟨.assumptionRow 21, 7⟩]
  caps := #[0, 0, 70840, 29183, 16758, 7923, 3774, 2108, 900, 525, 286, 1456084, 1442518, 1017450, 600780, 310080] }

theorem case_49_34_21_checked :
    (Witness.linear .conditional case_49_34_21).check 49 34 21 = true := by
  change case_49_34_21.check 49 34 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_34_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58786, 58786, 41990, 25194] }

theorem case_49_34_22_checked :
    (Witness.linear .negative case_49_34_22).check 49 34 22 = true := by
  change case_49_34_22.check 49 34 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_35_1_checked :
    (Witness.rising).check 49 35 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_35_2_checked :
    (Witness.rising).check 49 35 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_35_3_checked :
    (Witness.rising).check 49 35 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_35_4_checked :
    (Witness.rising).check 49 35 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_35_5_checked :
    (Witness.rising).check 49 35 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_35_6_checked :
    (Witness.rising).check 49 35 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_35_7_checked :
    (Witness.rising).check 49 35 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_35_8_checked :
    (Witness.rising).check 49 35 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_35_9_checked :
    (Witness.rising).check 49 35 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_35_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0, 0] }

theorem case_49_35_10_checked :
    (Witness.linear .positive case_49_35_10).check 49 35 10 = true := by
  change case_49_35_10.check 49 35 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_35_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_49_35_11_checked :
    (Witness.linear .positive case_49_35_11).check 49 35 11 = true := by
  change case_49_35_11.check 49 35 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_35_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_49_35_12_checked :
    (Witness.linear .positive case_49_35_12).check 49 35 12 = true := by
  change case_49_35_12.check 49 35 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_35_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_49_35_13_checked :
    (Witness.linear .positive case_49_35_13).check 49 35 13 = true := by
  change case_49_35_13.check 49 35 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_35_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_49_35_14_checked :
    (Witness.linear .positive case_49_35_14).check 49 35 14 = true := by
  change case_49_35_14.check 49 35 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_35_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_49_35_15_checked :
    (Witness.linear .positive case_49_35_15).check 49 35 15 = true := by
  change case_49_35_15.check 49 35 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_35_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_49_35_16_checked :
    (Witness.linear .positive case_49_35_16).check 49 35 16 = true := by
  change case_49_35_16.check 49 35 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_35_17 : Certificate := {
  objectiveScale := 614
  eta := 3035981025
  rows := #[⟨.assumptionRow 17, 1215⟩]
  caps := #[0, 0, 864364150, 248485192, 72232490, 21269550, 6358170, 1934920, 601601, 192005, 63300, 17974132, 11196262, 4661041, 1497370] }

theorem case_49_35_17_checked :
    (Witness.linear .conditional case_49_35_17).check 49 35 17 = true := by
  change case_49_35_17.check 49 35 17 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_35_18 : Certificate := {
  objectiveScale := 9833947323200000
  eta := 2919556599881786612748000
  rows := #[⟨.count 2, 246511957848723639072000⟩, ⟨.count 3, 18044231148836752860000⟩, ⟨.count 4, 958994103015100152000⟩, ⟨.count 5, 50473373842900008000⟩, ⟨.path 4, 630949736503245519360⟩, ⟨.path 5, 12051920524499856000⟩, ⟨.privateRow 2 32, 19848654263720428146000⟩, ⟨.privateRow 2 33, 29425976950410704664000⟩, ⟨.privateRow 3 28, 2109787026633220334400⟩, ⟨.privateRow 3 29, 3898016600742298534500⟩, ⟨.privateRow 3 30, 8065925547727881834000⟩, ⟨.privateRow 3 31, 9137783722808355615000⟩, ⟨.privateRow 3 32, 12816030841609693698000⟩, ⟨.privateRow 4 24, 110410505281343767500⟩, ⟨.privateRow 4 25, 517352081889725082000⟩, ⟨.privateRow 4 26, 855944298085845969000⟩, ⟨.privateRow 4 27, 1912940868645910303200⟩, ⟨.privateRow 4 28, 2681397985404062925000⟩, ⟨.privateRow 4 29, 3461632222725558882000⟩, ⟨.privateRow 4 30, 4555221989321725722000⟩, ⟨.privateRow 5 21, 34321894213172005440⟩, ⟨.privateRow 5 22, 104311639275326683200⟩, ⟨.privateRow 5 23, 203155329717672532200⟩, ⟨.privateRow 5 24, 460749798365901501600⟩, ⟨.privateRow 5 25, 754576938951355119600⟩, ⟨.privateRow 5 26, 1055902980793468167360⟩, ⟨.privateRow 5 27, 1356471922027937715000⟩, ⟨.privateRow 5 28, 1896116410698276967200⟩, ⟨.privateRow 5 29, 688961552955585109200⟩, ⟨.privateRow 6 18, 6776517784463427000⟩, ⟨.privateRow 6 19, 22942442655863640000⟩, ⟨.privateRow 6 20, 47388889885833896400⟩, ⟨.privateRow 6 21, 121198410030173476000⟩, ⟨.privateRow 6 22, 218016934238081979000⟩, ⟨.privateRow 6 23, 335687994288493704000⟩, ⟨.privateRow 6 24, 470617476479632482000⟩, ⟨.privateRow 6 25, 601754779260352317600⟩, ⟨.privateRow 6 26, 670875260661879273000⟩, ⟨.privateRow 7 15, 1201746996259524000⟩, ⟨.privateRow 7 16, 5338529925691347000⟩, ⟨.privateRow 7 17, 12618343460725002000⟩, ⟨.privateRow 7 18, 33457728873134475000⟩, ⟨.privateRow 7 19, 70452417655714594500⟩, ⟨.privateRow 7 20, 117537532606382889000⟩, ⟨.privateRow 7 21, 175868161983854715375⟩, ⟨.privateRow 7 22, 243654203491618491000⟩, ⟨.privateRow 7 23, 260779098188316708000⟩, ⟨.privateRow 8 12, 262882155431770875⟩, ⟨.privateRow 8 13, 1261834346072500200⟩, ⟨.privateRow 8 14, 3755459363311012500⟩, ⟨.privateRow 8 15, 11000607119606412000⟩, ⟨.privateRow 8 16, 25061432151162156750⟩, ⟨.privateRow 8 17, 48179129577313644000⟩, ⟨.privateRow 8 18, 77392506559113345600⟩, ⟨.privateRow 8 19, 113097745092424092000⟩, ⟨.privateRow 8 20, 52050666775490633250⟩, ⟨.privateRow 9 10, 329891332306536000⟩, ⟨.privateRow 9 11, 1226783392014930750⟩, ⟨.privateRow 9 12, 4299583697728519200⟩, ⟨.privateRow 9 13, 11016014132378970000⟩, ⟨.privateRow 9 14, 23079705133291884000⟩, ⟨.privateRow 9 15, 41593798814982414000⟩, ⟨.privateRow 9 16, 34668580013305056000⟩, ⟨.privateRow 10 7, 265649336015263200⟩, ⟨.privateRow 10 8, 560815264921111200⟩, ⟨.privateRow 10 9, 2078315393531176800⟩, ⟨.privateRow 10 10, 5993713143844375950⟩, ⟨.privateRow 10 11, 14132544676012002240⟩, ⟨.privateRow 10 12, 16584108548381431200⟩, ⟨.privateRow 11 6, 1328246680076316000⟩, ⟨.privateRow 11 7, 4206114486908334000⟩, ⟨.privateRow 11 8, 7422554976897060000⟩, ⟨.privateRow 12 3, 2203202826475794000⟩, ⟨.privateRow 12 4, 2313362967799583700⟩, ⟨.hall 3 31, 910886668571086081875⟩, ⟨.assumptionRow 18, 8024669597685312⟩]
  caps := #[0, 657412531751358240, 220754452336614939600, 60028545901656463560, 115126291714463017560, 9408077132728903200, 8689941586488168000, 466605795813893021, 8024669597685312, 34091646210486110800, 0, 40473462476406177504, 0, 322151951738395851072, 103899982373219672640] }

theorem case_49_35_18_checked :
    (Witness.linear .conditional case_49_35_18).check 49 35 18 = true := by
  change case_49_35_18.check 49 35 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_35_19 : Certificate := {
  objectiveScale := 6941609875200000
  eta := 2487216821555658014222400
  rows := #[⟨.count 2, 206092880075329312665600⟩, ⟨.count 3, 14490905630296592296800⟩, ⟨.count 4, 686437884263440108800⟩, ⟨.count 5, 10094674768580001600⟩, ⟨.path 4, 569313606174315754752⟩, ⟨.path 5, 5789427242610211200⟩, ⟨.privateRow 2 32, 17322461902883282745600⟩, ⟨.privateRow 2 33, 26316817121688064171200⟩, ⟨.privateRow 3 28, 1706336525048972937120⟩, ⟨.privateRow 3 29, 3252588332726214682200⟩, ⟨.privateRow 3 30, 6989440646711808885600⟩, ⟨.privateRow 3 31, 8244825617237716306800⟩, ⟨.privateRow 3 32, 11992473625073041900800⟩, ⟨.privateRow 4 24, 97792161820618765500⟩, ⟨.privateRow 4 25, 404508038940955778400⟩, ⟨.privateRow 4 26, 678866878187005107600⟩, ⟨.privateRow 4 27, 1583854471190202251040⟩, ⟨.privateRow 4 28, 2323037031119472868200⟩, ⟨.privateRow 4 29, 3136078961438853830400⟩, ⟨.privateRow 4 30, 4353328493950125690000⟩, ⟨.privateRow 5 20, 2569553577456727680⟩, ⟨.privateRow 5 21, 30284024305740004800⟩, ⟨.privateRow 5 22, 80533072042671568320⟩, ⟨.privateRow 5 23, 154448523959274024480⟩, ⟨.privateRow 5 24, 361100937436061771520⟩, ⟨.privateRow 5 25, 618467074155001431360⟩, ⟨.privateRow 5 26, 906501794218484143680⟩, ⟨.privateRow 5 27, 1228521919336186194720⟩, ⟨.privateRow 5 28, 1835211872927844290880⟩, ⟨.privateRow 5 29, 1089215407529782172640⟩, ⟨.privateRow 6 17, 776513443736923200⟩, ⟨.privateRow 6 18, 7664475287255186400⟩, ⟨.privateRow 6 19, 18455920536494750400⟩, ⟨.privateRow 6 20, 35443524743014227840⟩, ⟨.privateRow 6 21, 90353570459512360000⟩, ⟨.privateRow 6 22, 168244579476333360000⟩, ⟨.privateRow 6 23, 270793656490479408000⟩, ⟨.privateRow 6 24, 398552714937269692800⟩, ⟨.privateRow 6 25, 539952937066045863360⟩, ⟨.privateRow 6 26, 822155178374349019200⟩, ⟨.privateRow 6 27, 139456062543716318400⟩, ⟨.privateRow 7 14, 224326105968444480⟩, ⟨.privateRow 7 15, 2103057243454167000⟩, ⟨.privateRow 7 16, 5306175198868975200⟩, ⟨.privateRow 7 17, 9884369044234584900⟩, ⟨.privateRow 7 18, 24548413641774094800⟩, ⟨.privateRow 7 19, 51735208188972508200⟩, ⟨.privateRow 7 20, 89263096333276866000⟩, ⟨.privateRow 7 21, 139222389516665855400⟩, ⟨.privateRow 7 22, 202374194170103841600⟩, ⟨.privateRow 7 23, 274939683627574765800⟩, ⟨.privateRow 7 24, 170095269850573026960⟩, ⟨.privateRow 8 11, 98967399691960800⟩, ⟨.privateRow 8 12, 683493604122604275⟩, ⟨.privateRow 8 13, 1906771900731778080⟩, ⟨.privateRow 8 14, 3785503038217500600⟩, ⟨.privateRow 8 15, 8671066788395642400⟩, ⟨.privateRow 8 16, 18226496109936114000⟩, ⟨.privateRow 8 17, 35025462454618490400⟩, ⟨.privateRow 8 18, 57707890760382342480⟩, ⟨.privateRow 8 19, 87487181327693347200⟩, ⟨.privateRow 8 20, 125131905985522936500⟩, ⟨.privateRow 8 21, 20910397734915717600⟩, ⟨.privateRow 9 8, 59033185781169600⟩, ⟨.privateRow 9 9, 311564036067284000⟩, ⟨.privateRow 9 10, 857717463996993600⟩, ⟨.privateRow 9 11, 1892751519108750300⟩, ⟨.privateRow 9 12, 4411746750712741440⟩, ⟨.privateRow 9 13, 8652578373068572800⟩, ⟨.privateRow 9 14, 16824457947633336000⟩, ⟨.privateRow 9 15, 9720797925299260800⟩, ⟨.privateRow 9 16, 88506845445731731200⟩, ⟨.privateRow 10 6, 201893495371600032⟩, ⟨.privateRow 10 7, 531298672030526400⟩, ⟨.privateRow 10 8, 1233793582826444640⟩, ⟨.privateRow 10 9, 3087782870389176960⟩, ⟨.privateRow 10 10, 2649852126752250420⟩, ⟨.privateRow 10 11, 18305010247025069568⟩, ⟨.privateRow 10 12, 16872527827483716960⟩, ⟨.privateRow 10 13, 3571961841189846720⟩, ⟨.privateRow 11 4, 721048197755714400⟩, ⟨.privateRow 11 5, 757100607643500120⟩, ⟨.privateRow 11 7, 11777120563343335200⟩, ⟨.privateRow 11 8, 2375217592607059200⟩, ⟨.privateRow 12 2, 2523668692145000400⟩, ⟨.privateRow 12 3, 2643843391770952800⟩, ⟨.hall 3 31, 1016723024347917036150⟩, ⟨.assumptionRow 19, 3344722163566784⟩]
  caps := #[0, 0, 34088768913541934592, 0, 19267339527548690292, 0, 8249481118493130080, 109695109304706891, 233516040012340085, 6003134233520592480, 132065669904730848, 48774795332769263472, 0, 504435735602970435264, 187381109759934714624] }

theorem case_49_35_19_checked :
    (Witness.linear .conditional case_49_35_19).check 49 35 19 = true := by
  change case_49_35_19.check 49 35 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_35_20 : Certificate := {
  objectiveScale := 9516723216000000
  eta := 5122155748783126245192000
  rows := #[⟨.count 2, 434171961796625868816000⟩, ⟨.count 3, 31184132805938388276000⟩, ⟨.count 4, 1581499047077533584000⟩, ⟨.count 5, 33648915895266672000⟩, ⟨.path 4, 1065563476002109244160⟩, ⟨.path 5, 27670608805471632000⟩, ⟨.privateRow 2 32, 39604774008728872944000⟩, ⟨.privateRow 2 33, 65329370210660243688000⟩, ⟨.privateRow 3 28, 3263384026575946072800⟩, ⟨.privateRow 3 29, 6909244063828089984000⟩, ⟨.privateRow 3 30, 15381293332569676512000⟩, ⟨.privateRow 3 31, 15900514798675805298000⟩, ⟨.privateRow 4 26, 858047355329300136000⟩, ⟨.privateRow 4 28, 17388077288879052756000⟩, ⟨.privateRow 5 21, 37013807484793339200⟩, ⟨.privateRow 5 24, 1007544681663984921600⟩, ⟨.privateRow 5 26, 3623315263602315240960⟩, ⟨.privateRow 5 27, 4936295961835620782400⟩, ⟨.privateRow 5 28, 2484411623600522616000⟩, ⟨.privateRow 6 18, 1557820180336420000⟩, ⟨.privateRow 6 19, 3228936373788216000⟩, ⟨.privateRow 6 24, 3005658255941088748000⟩, ⟨.privateRow 6 25, 320786331534875606400⟩, ⟨.privateRow 6 28, 8150515183520149440000⟩, ⟨.privateRow 7 15, 500727915108135000⟩, ⟨.privateRow 7 16, 1402038162302778000⟩, ⟨.privateRow 7 17, 1986220729928935500⟩, ⟨.privateRow 7 18, 5608152649211112000⟩, ⟨.privateRow 7 19, 8692636606277223600⟩, ⟨.privateRow 7 22, 205298445194335350000⟩, ⟨.privateRow 7 25, 2175612718353335761500⟩, ⟨.privateRow 8 12, 87627385143923625⟩, ⟨.privateRow 8 13, 280407632460555600⟩, ⟨.privateRow 8 14, 300436749064881000⟩, ⟨.privateRow 8 15, 970641804671154000⟩, ⟨.privateRow 8 16, 1752547702878472500⟩, ⟨.privateRow 8 17, 4333572501663132000⟩, ⟨.privateRow 8 23, 674380356067636218000⟩, ⟨.privateRow 9 10, 109963777435512000⟩, ⟨.privateRow 9 11, 116836513525231500⟩, ⟨.privateRow 9 12, 249251228853827200⟩, ⟨.privateRow 9 13, 534109776115344000⟩, ⟨.privateRow 9 14, 1006591501140456000⟩, ⟨.hall 11 5, 12336774720055500⟩, ⟨.hall 12 5, 5499986252904000⟩, ⟨.hall 9 6, 657690663808800⟩, ⟨.hall 10 6, 4892487771333240⟩, ⟨.hall 9 7, 2951569545693048⟩, ⟨.hall 8 9, 1017490334297920⟩, ⟨.hall 7 10, 463887729411600⟩, ⟨.hall 6 14, 122273565614200⟩, ⟨.hall 10 17, 132221891736480⟩, ⟨.hall 12 18, 5499986252904000⟩, ⟨.hall 4 28, 7523283754114128000⟩, ⟨.hall 2 29, 3177199383928069500⟩, ⟨.hall 3 30, 392245616112792316875⟩]
  caps := #[0, 1023743521171332561600, 134230401503434716480, 84001526858395866720, 8740196882096153760, 0, 14898425724671944000, 4308955868716527600, 54032592087776775, 100175697325441920, 127679680867415040, 47673747442903021440, 0, 0, 590189106963456000000] }

theorem case_49_35_20_checked :
    (Witness.linear .negative case_49_35_20).check 49 35 20 = true := by
  change case_49_35_20.check 49 35 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_35_21 : Certificate := {
  objectiveScale := 81
  eta := 11297715
  rows := #[⟨.assumptionRow 21, 44⟩]
  caps := #[0, 0, 5163730, 1846900, 894102, 328776, 159885, 60588, 29852, 11690, 7874740, 14560840, 12094412, 7823706, 4335306] }

theorem case_49_35_21_checked :
    (Witness.linear .conditional case_49_35_21).check 49 35 21 = true := by
  change case_49_35_21.check 49 35 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_35_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208012, 208012, 149226, 90440] }

theorem case_49_35_22_checked :
    (Witness.linear .negative case_49_35_22).check 49 35 22 = true := by
  change case_49_35_22.check 49 35 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_36_1_checked :
    (Witness.rising).check 49 36 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_36_2_checked :
    (Witness.rising).check 49 36 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_36_3_checked :
    (Witness.rising).check 49 36 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_36_4_checked :
    (Witness.rising).check 49 36 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_36_5_checked :
    (Witness.rising).check 49 36 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_36_6_checked :
    (Witness.rising).check 49 36 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_36_7_checked :
    (Witness.rising).check 49 36 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_36_8_checked :
    (Witness.rising).check 49 36 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_36_9_checked :
    (Witness.rising).check 49 36 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_36_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0, 0] }

theorem case_49_36_10_checked :
    (Witness.linear .positive case_49_36_10).check 49 36 10 = true := by
  change case_49_36_10.check 49 36 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_36_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_49_36_11_checked :
    (Witness.linear .positive case_49_36_11).check 49 36 11 = true := by
  change case_49_36_11.check 49 36 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_36_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_49_36_12_checked :
    (Witness.linear .positive case_49_36_12).check 49 36 12 = true := by
  change case_49_36_12.check 49 36 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_36_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_49_36_13_checked :
    (Witness.linear .positive case_49_36_13).check 49 36 13 = true := by
  change case_49_36_13.check 49 36 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_36_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_49_36_14_checked :
    (Witness.linear .positive case_49_36_14).check 49 36 14 = true := by
  change case_49_36_14.check 49 36 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_36_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_49_36_15_checked :
    (Witness.linear .positive case_49_36_15).check 49 36 15 = true := by
  change case_49_36_15.check 49 36 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_36_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_49_36_16_checked :
    (Witness.linear .positive case_49_36_16).check 49 36 16 = true := by
  change case_49_36_16.check 49 36 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_36_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_49_36_17_checked :
    (Witness.linear .positive case_49_36_17).check 49 36 17 = true := by
  change case_49_36_17.check 49 36 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_36_18 : Certificate := {
  objectiveScale := 379
  eta := 2641370025
  rows := #[⟨.assumptionRow 18, 576⟩]
  caps := #[0, 0, 759265650, 220084125, 64394572, 19040850, 5823690, 1848444, 597272, 197340, 71124625, 52858025, 27116540, 11224598] }

theorem case_49_36_18_checked :
    (Witness.linear .conditional case_49_36_18).check 49 36 18 = true := by
  change case_49_36_18.check 49 36 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_36_19 : Certificate := {
  objectiveScale := 4301897600000
  eta := 2853567272943603216000
  rows := #[⟨.count 2, 226879930935885427200⟩, ⟨.count 3, 14989955211673041600⟩, ⟨.count 4, 657093927087037440⟩, ⟨.path 4, 633946037558193360⟩, ⟨.privateRow 2 33, 18572029744751683200⟩, ⟨.privateRow 2 34, 26101230992623987200⟩, ⟨.privateRow 3 28, 239565494250482400⟩, ⟨.privateRow 3 29, 2062544826689867520⟩, ⟨.privateRow 3 30, 3736080922239666000⟩, ⟨.privateRow 3 31, 7696516831158355200⟩, ⟨.privateRow 3 32, 8236489849945156800⟩, ⟨.privateRow 3 33, 10609329031092792000⟩, ⟨.privateRow 4 24, 13689456814313280⟩, ⟨.privateRow 4 25, 190796804349491340⟩, ⟨.privateRow 4 26, 526066269007181760⟩, ⟨.privateRow 4 27, 845323958283845040⟩, ⟨.privateRow 4 28, 1897358714463820608⟩, ⟨.privateRow 4 29, 2609552705228469000⟩, ⟨.privateRow 4 30, 3271780178620873920⟩, ⟨.privateRow 4 31, 4062346309647465840⟩, ⟨.privateRow 5 21, 9402859225992960⟩, ⟨.privateRow 5 22, 58104138922974144⟩, ⟨.privateRow 5 23, 121684060571673600⟩, ⟨.privateRow 5 24, 213327368689715280⟩, ⟨.privateRow 5 25, 477609937743818880⟩, ⟨.privateRow 5 26, 776749919982516480⟩, ⟨.privateRow 5 27, 1068994472122152576⟩, ⟨.privateRow 5 28, 1346890445452712160⟩, ⟨.privateRow 5 29, 1679240035889095680⟩, ⟨.privateRow 6 18, 3217607370885600⟩, ⟨.privateRow 6 19, 16794935443486200⟩, ⟨.privateRow 6 20, 34223642035783200⟩, ⟨.privateRow 6 21, 58180191460831440⟩, ⟨.privateRow 6 22, 136472054043925600⟩, ⟨.privateRow 6 23, 240516150973698600⟩, ⟨.privateRow 6 24, 365867030334920400⟩, ⟨.privateRow 6 25, 506700033474234600⟩, ⟨.privateRow 6 26, 640362368758432320⟩, ⟨.privateRow 6 27, 250022718205860600⟩, ⟨.privateRow 7 15, 1303757791839360⟩, ⟨.privateRow 7 16, 5703940339297200⟩, ⟨.privateRow 7 17, 12285409961563200⟩, ⟨.privateRow 7 18, 20778639807439800⟩, ⟨.privateRow 7 19, 45335214125323200⟩, ⟨.privateRow 7 20, 87188802329257200⟩, ⟨.privateRow 7 21, 142145814804708000⟩, ⟨.privateRow 7 22, 209416095314197200⟩, ⟨.privateRow 7 23, 286826714204659200⟩, ⟨.privateRow 7 24, 29062934109752400⟩, ⟨.privateRow 8 12, 671051804623200⟩, ⟨.privateRow 8 13, 2495473898442525⟩, ⟨.privateRow 8 14, 5830694569059360⟩, ⟨.privateRow 8 15, 5432324132664000⟩, ⟨.privateRow 8 16, 30859779784402800⟩, ⟨.privateRow 8 17, 34065199248580500⟩, ⟨.privateRow 8 18, 68620130748514800⟩, ⟨.privateRow 8 19, 106663684344857640⟩, ⟨.privateRow 8 20, 54504318797728800⟩, ⟨.privateRow 9 9, 320221212030720⟩, ⟨.privateRow 9 10, 1521050757145920⟩, ⟨.privateRow 9 11, 3578942957990400⟩, ⟨.privateRow 9 12, 7034859751799880⟩, ⟨.privateRow 9 13, 7503850401919872⟩, ⟨.privateRow 9 14, 24771398044947840⟩, ⟨.privateRow 9 15, 64820163035295360⟩, ⟨.privateRow 10 6, 325939447959840⟩, ⟨.privateRow 10 7, 1368945681431328⟩, ⟨.privateRow 10 8, 3242239771811040⟩, ⟨.privateRow 10 10, 26573651463078720⟩, ⟨.privateRow 10 11, 6844728407156640⟩, ⟨.privateRow 11 4, 1037080061690400⟩, ⟨.privateRow 11 5, 4345859306131200⟩, ⟨.privateRow 11 6, 6844728407156640⟩, ⟨.hall 3 32, 340162260234451200⟩, ⟨.assumptionRow 19, 2580106104576⟩]
  caps := #[0, 424066789261315200, 259850984464191120, 25638562223322048, 0, 24936013927755840, 3079584975797960, 10463479767401040, 0, 46488818110886976, 0, 0, 1129303880852539392, 446740672270244352] }

theorem case_49_36_19_checked :
    (Witness.linear .conditional case_49_36_19).check 49 36 19 = true := by
  change case_49_36_19.check 49 36 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_36_20 : Certificate := {
  objectiveScale := 184786056000000
  eta := 285288964483129470864000
  rows := #[⟨.count 2, 16514048070333253440000⟩, ⟨.count 3, 649222489418807304000⟩, ⟨.count 4, 2874785931005788800⟩, ⟨.path 3, 593954003939177831040⟩, ⟨.path 4, 2654426109290155200⟩, ⟨.privateRow 2 32, 216673680355436304000⟩, ⟨.privateRow 2 33, 1394470814449682970000⟩, ⟨.privateRow 2 34, 1941279055076409048000⟩, ⟨.privateRow 3 27, 2509733749290768000⟩, ⟨.privateRow 3 28, 77060233983905172000⟩, ⟨.privateRow 3 29, 169772080258841860800⟩, ⟨.privateRow 3 30, 267914077736789484000⟩, ⟨.privateRow 3 31, 557655233838622920000⟩, ⟨.privateRow 3 32, 593723149917445548000⟩, ⟨.privateRow 3 33, 769803788191550112000⟩, ⟨.privateRow 4 22, 631581757569453600⟩, ⟨.privateRow 4 23, 2012350151704052160⟩, ⟨.privateRow 4 24, 4764691496759594400⟩, ⟨.privateRow 4 25, 25992856126177340400⟩, ⟨.privateRow 4 26, 39630977477436945600⟩, ⟨.privateRow 4 27, 61608259604749057200⟩, ⟨.privateRow 4 28, 133917111286019661600⟩, ⟨.privateRow 4 29, 185483583923435998200⟩, ⟨.privateRow 4 30, 234933894694973073600⟩, ⟨.privateRow 4 31, 295384254410844799200⟩, ⟨.privateRow 5 18, 152105075714592000⟩, ⟨.privateRow 5 19, 343991478923769600⟩, ⟨.privateRow 5 20, 612222929751232800⟩, ⟨.privateRow 5 21, 2071394576549625600⟩, ⟨.privateRow 5 22, 7048549208614193280⟩, ⟨.privateRow 5 23, 10351595430576400000⟩, ⟨.privateRow 5 24, 15518520349781248800⟩, ⟨.privateRow 5 25, 33949852899496934400⟩, ⟨.privateRow 5 26, 54159547292775724800⟩, ⟨.privateRow 5 27, 75149033707551323520⟩, ⟨.privateRow 5 28, 96145618359193603200⟩, ⟨.privateRow 5 29, 125248389512585539200⟩, ⟨.privateRow 6 14, 39144688603020000⟩, ⟨.privateRow 6 15, 79023340117346625⟩, ⟨.privateRow 6 16, 128655543208592400⟩, ⟨.privateRow 6 17, 313716718661346000⟩, ⟨.privateRow 6 18, 813908409953562000⟩, ⟨.privateRow 6 19, 2146107552660571500⟩, ⟨.privateRow 6 20, 3411993402961416000⟩, ⟨.privateRow 6 21, 4778000690884621200⟩, ⟨.privateRow 6 22, 9774863685158572000⟩, ⟨.privateRow 6 23, 16836130568158902000⟩, ⟨.privateRow 6 24, 25335001673711730000⟩, ⟨.privateRow 6 25, 35291546421529398000⟩, ⟨.privateRow 6 26, 45344424383966307600⟩, ⟨.privateRow 6 27, 21411166048636864500⟩, ⟨.privateRow 7 10, 11407880678594400⟩, ⟨.privateRow 7 11, 27018664765092000⟩, ⟨.privateRow 7 12, 47532836160810000⟩, ⟨.privateRow 7 13, 93947252647248000⟩, ⟨.privateRow 7 14, 178248135603037500⟩, ⟨.privateRow 7 15, 395473196857939200⟩, ⟨.privateRow 7 16, 855591050894580000⟩, ⟨.privateRow 7 17, 1443535670483676000⟩, ⟨.privateRow 7 18, 2053418522146992000⟩, ⟨.privateRow 7 19, 705214441949472000⟩, ⟨.privateRow 7 20, 12143688982363738800⟩, ⟨.privateRow 7 21, 6920780945013936000⟩, ⟨.privateRow 7 22, 14438098983846037500⟩, ⟨.privateRow 7 23, 19841563894555260000⟩, ⟨.privateRow 7 24, 2680851959469684000⟩, ⟨.privateRow 8 7, 21173717926179000⟩, ⟨.privateRow 8 8, 19013134464324000⟩, ⟨.privateRow 8 9, 46582179437593800⟩, ⟨.privateRow 8 10, 77053229144892000⟩, ⟨.privateRow 8 11, 136788939618331000⟩, ⟨.privateRow 8 12, 258354944779932000⟩, ⟨.privateRow 8 13, 482458287032221500⟩, ⟨.privateRow 8 14, 811860841626634800⟩, ⟨.privateRow 8 15, 1207334038484574000⟩, ⟨.privateRow 8 16, 2078281851831108000⟩, ⟨.privateRow 8 17, 665459706251340000⟩, ⟨.privateRow 8 18, 8402941199846466000⟩, ⟨.privateRow 8 19, 7912315907328432600⟩, ⟨.privateRow 8 20, 384487830278552000⟩, ⟨.privateRow 9 5, 87956413348003200⟩, ⟨.privateRow 9 6, 24198534772776000⟩, ⟨.privateRow 9 7, 86192876238268800⟩, ⟨.privateRow 9 8, 138415618900278720⟩, ⟨.privateRow 9 9, 235362590842579200⟩, ⟨.privateRow 9 10, 402233422445254400⟩, ⟨.privateRow 9 11, 645104468177769600⟩, ⟨.privateRow 9 12, 978225768189469800⟩, ⟨.privateRow 9 13, 589153659934519680⟩, ⟨.privateRow 9 14, 4715257347152352000⟩, ⟨.privateRow 10 2, 114991437240231552⟩, ⟨.privateRow 10 3, 129764642719011300⟩, ⟨.privateRow 10 4, 83327128434950400⟩, ⟨.privateRow 10 7, 1736849833315997400⟩, ⟨.privateRow 10 8, 37826130671128800⟩, ⟨.privateRow 10 9, 585604541501179200⟩, ⟨.privateRow 11 0, 890692222213332000⟩, ⟨.privateRow 12 0, 351362724900707520⟩, ⟨.hall 3 32, 24827696676868176000⟩]
  caps := #[0, 11745846899343123840, 0, 507194287453002240, 627401274713183880, 8762571338976000, 1140458740857813125, 71132686879266600, 905325911106432900, 0, 798977951796983868, 0, 4159894475543526720, 45301595130792000000] }

theorem case_49_36_20_checked :
    (Witness.linear .negative case_49_36_20).check 49 36 20 = true := by
  change case_49_36_20.check 49 36 20 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_36_21 : Certificate := {
  objectiveScale := 993
  eta := 436368075
  rows := #[⟨.assumptionRow 21, 611⟩]
  caps := #[0, 0, 184463565, 65659825, 27875793, 10672794, 4214181, 1775208, 638588, 334305, 442805545, 431364885, 299663573, 174796941] }

theorem case_49_36_21_checked :
    (Witness.linear .conditional case_49_36_21).check 49 36 21 = true := by
  change case_49_36_21.check 49 36 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_36_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900, 534888, 326876] }

theorem case_49_36_22_checked :
    (Witness.linear .negative case_49_36_22).check 49 36 22 = true := by
  change case_49_36_22.check 49 36 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_36_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208012, 208012] }

theorem case_49_36_23_checked :
    (Witness.linear .negative case_49_36_23).check 49 36 23 = true := by
  change case_49_36_23.check 49 36 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_37_1_checked :
    (Witness.rising).check 49 37 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_37_2_checked :
    (Witness.rising).check 49 37 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_37_3_checked :
    (Witness.rising).check 49 37 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_37_4_checked :
    (Witness.rising).check 49 37 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_37_5_checked :
    (Witness.rising).check 49 37 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_37_6_checked :
    (Witness.rising).check 49 37 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_37_7_checked :
    (Witness.rising).check 49 37 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_37_8_checked :
    (Witness.rising).check 49 37 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_37_9_checked :
    (Witness.rising).check 49 37 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_37_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0, 0] }

theorem case_49_37_10_checked :
    (Witness.linear .positive case_49_37_10).check 49 37 10 = true := by
  change case_49_37_10.check 49 37 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_37_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_49_37_11_checked :
    (Witness.linear .positive case_49_37_11).check 49 37 11 = true := by
  change case_49_37_11.check 49 37 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_37_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_49_37_12_checked :
    (Witness.linear .positive case_49_37_12).check 49 37 12 = true := by
  change case_49_37_12.check 49 37 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_37_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_49_37_13_checked :
    (Witness.linear .positive case_49_37_13).check 49 37 13 = true := by
  change case_49_37_13.check 49 37 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_37_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_49_37_14_checked :
    (Witness.linear .positive case_49_37_14).check 49 37 14 = true := by
  change case_49_37_14.check 49 37 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_37_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_49_37_15_checked :
    (Witness.linear .positive case_49_37_15).check 49 37 15 = true := by
  change case_49_37_15.check 49 37 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_37_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_49_37_16_checked :
    (Witness.linear .positive case_49_37_16).check 49 37 16 = true := by
  change case_49_37_16.check 49 37 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_37_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_49_37_17_checked :
    (Witness.linear .positive case_49_37_17).check 49 37 17 = true := by
  change case_49_37_17.check 49 37 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_37_18 : Certificate := {
  objectiveScale := 7
  eta := 229064475
  rows := #[⟨.assumptionRow 18, 18⟩]
  caps := #[0, 0, 63734265, 17866745, 5051720, 1456084, 425068, 125970, 38012, 11726, 3718, 1221, 420] }

theorem case_49_37_18_checked :
    (Witness.linear .conditional case_49_37_18).check 49 37 18 = true := by
  change case_49_37_18.check 49 37 18 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_37_19 : Certificate := {
  objectiveScale := 838
  eta := 6396646725
  rows := #[⟨.assumptionRow 19, 995⟩]
  caps := #[0, 0, 1904640465, 569491845, 171119586, 51710362, 16905820, 5579502, 1851096, 813067710, 687631230, 409233825, 201451250] }

theorem case_49_37_19_checked :
    (Witness.linear .conditional case_49_37_19).check 49 37 19 = true := by
  change case_49_37_19.check 49 37 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_37_20 : Certificate := {
  objectiveScale := 597
  eta := 2882500530
  rows := #[⟨.assumptionRow 20, 551⟩]
  caps := #[0, 0, 890362200, 297059490, 101451735, 33749947, 11029158, 3558168, 1338648, 740262705, 681208710, 444935920, 242873675] }

theorem case_49_37_20_checked :
    (Witness.linear .conditional case_49_37_20).check 49 37 20 = true := by
  change case_49_37_20.check 49 37 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_37_21 : Certificate := {
  objectiveScale := 957
  eta := 365769690
  rows := #[⟨.assumptionRow 21, 581⟩]
  caps := #[0, 0, 158414685, 58563175, 23809071, 9532908, 3574641, 1589160, 585548, 1519986510, 1485553095, 1039850240, 614502845] }

theorem case_49_37_21_checked :
    (Witness.linear .conditional case_49_37_21).check 49 37 21 = true := by
  change case_49_37_21.check 49 37 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_37_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440, 2674440, 1931540, 1188640] }

theorem case_49_37_22_checked :
    (Witness.linear .negative case_49_37_22).check 49 37 22 = true := by
  change case_49_37_22.check 49 37 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_37_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 742900, 742900] }

theorem case_49_37_23_checked :
    (Witness.linear .negative case_49_37_23).check 49 37 23 = true := by
  change case_49_37_23.check 49 37 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_37_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_37_24_checked :
    (Witness.linear .negative case_49_37_24).check 49 37 24 = true := by
  change case_49_37_24.check 49 37 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_38_1_checked :
    (Witness.rising).check 49 38 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_38_2_checked :
    (Witness.rising).check 49 38 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_38_3_checked :
    (Witness.rising).check 49 38 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_38_4_checked :
    (Witness.rising).check 49 38 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_38_5_checked :
    (Witness.rising).check 49 38 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_38_6_checked :
    (Witness.rising).check 49 38 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_38_7_checked :
    (Witness.rising).check 49 38 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_38_8_checked :
    (Witness.rising).check 49 38 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_38_9_checked :
    (Witness.rising).check 49 38 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_38_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0, 0] }

theorem case_49_38_10_checked :
    (Witness.linear .positive case_49_38_10).check 49 38 10 = true := by
  change case_49_38_10.check 49 38 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_38_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_49_38_11_checked :
    (Witness.linear .positive case_49_38_11).check 49 38 11 = true := by
  change case_49_38_11.check 49 38 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_38_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_49_38_12_checked :
    (Witness.linear .positive case_49_38_12).check 49 38 12 = true := by
  change case_49_38_12.check 49 38 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_38_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_49_38_13_checked :
    (Witness.linear .positive case_49_38_13).check 49 38 13 = true := by
  change case_49_38_13.check 49 38 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_38_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_49_38_14_checked :
    (Witness.linear .positive case_49_38_14).check 49 38 14 = true := by
  change case_49_38_14.check 49 38 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_38_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_49_38_15_checked :
    (Witness.linear .positive case_49_38_15).check 49 38 15 = true := by
  change case_49_38_15.check 49 38 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_38_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_49_38_16_checked :
    (Witness.linear .positive case_49_38_16).check 49 38 16 = true := by
  change case_49_38_16.check 49 38 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_38_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_49_38_17_checked :
    (Witness.linear .positive case_49_38_17).check 49 38 17 = true := by
  change case_49_38_17.check 49 38 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_38_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_49_38_18_checked :
    (Witness.linear .positive case_49_38_18).check 49 38 18 = true := by
  change case_49_38_18.check 49 38 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_38_19 : Certificate := {
  objectiveScale := 915
  eta := 10296895875
  rows := #[⟨.assumptionRow 19, 1186⟩]
  caps := #[0, 0, 3109764105, 943841340, 288133765, 88583396, 27464690, 8600844, 2731365, 1451265270, 1182461280, 677270880] }

theorem case_49_38_19_checked :
    (Witness.linear .conditional case_49_38_19).check 49 38 19 = true := by
  change case_49_38_19.check 49 38 19 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_38_20 : Certificate := {
  objectiveScale := 365
  eta := 4211904900
  rows := #[⟨.assumptionRow 20, 381⟩]
  caps := #[0, 0, 1273726545, 384660510, 121573400, 40287467, 13217160, 4312050, 1403520, 763871745, 679764540, 428721150] }

theorem case_49_38_20_checked :
    (Witness.linear .conditional case_49_38_20).check 49 38 20 = true := by
  change case_49_38_20.check 49 38 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_38_21 : Certificate := {
  objectiveScale := 7
  eta := 12746370
  rows := #[⟨.assumptionRow 21, 5⟩]
  caps := #[0, 0, 4489485, 1480050, 600875, 216315, 74613, 31008, 13306650, 25282635, 20877675, 13463970] }

theorem case_49_38_21_checked :
    (Witness.linear .conditional case_49_38_21).check 49 38 21 = true := by
  change case_49_38_21.check 49 38 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_38_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 9694845, 9694845, 7020405, 4345965] }

theorem case_49_38_22_checked :
    (Witness.linear .negative case_49_38_22).check 49 38 22 = true := by
  change case_49_38_22.check 49 38 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_38_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2674440, 2674440] }

theorem case_49_38_23_checked :
    (Witness.linear .negative case_49_38_23).check 49 38 23 = true := by
  change case_49_38_23.check 49 38 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_38_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_38_24_checked :
    (Witness.linear .negative case_49_38_24).check 49 38 24 = true := by
  change case_49_38_24.check 49 38 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_39_1_checked :
    (Witness.rising).check 49 39 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_39_2_checked :
    (Witness.rising).check 49 39 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_39_3_checked :
    (Witness.rising).check 49 39 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_39_4_checked :
    (Witness.rising).check 49 39 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_39_5_checked :
    (Witness.rising).check 49 39 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_39_6_checked :
    (Witness.rising).check 49 39 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_39_7_checked :
    (Witness.rising).check 49 39 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_39_8_checked :
    (Witness.rising).check 49 39 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_39_9_checked :
    (Witness.rising).check 49 39 9 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_39_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_49_39_10_checked :
    (Witness.linear .positive case_49_39_10).check 49 39 10 = true := by
  change case_49_39_10.check 49 39 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_39_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_49_39_11_checked :
    (Witness.linear .positive case_49_39_11).check 49 39 11 = true := by
  change case_49_39_11.check 49 39 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_39_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_49_39_12_checked :
    (Witness.linear .positive case_49_39_12).check 49 39 12 = true := by
  change case_49_39_12.check 49 39 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_39_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_49_39_13_checked :
    (Witness.linear .positive case_49_39_13).check 49 39 13 = true := by
  change case_49_39_13.check 49 39 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_39_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_49_39_14_checked :
    (Witness.linear .positive case_49_39_14).check 49 39 14 = true := by
  change case_49_39_14.check 49 39 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_39_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_49_39_15_checked :
    (Witness.linear .positive case_49_39_15).check 49 39 15 = true := by
  change case_49_39_15.check 49 39 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_39_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_49_39_16_checked :
    (Witness.linear .positive case_49_39_16).check 49 39 16 = true := by
  change case_49_39_16.check 49 39 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_39_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_49_39_17_checked :
    (Witness.linear .positive case_49_39_17).check 49 39 17 = true := by
  change case_49_39_17.check 49 39 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_39_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_49_39_18_checked :
    (Witness.linear .positive case_49_39_18).check 49 39 18 = true := by
  change case_49_39_18.check 49 39 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_39_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_49_39_19_checked :
    (Witness.linear .positive case_49_39_19).check 49 39 19 = true := by
  change case_49_39_19.check 49 39 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_39_20 : Certificate := {
  objectiveScale := 17
  eta := 212766330
  rows := #[⟨.assumptionRow 20, 18⟩]
  caps := #[0, 0, 63731850, 19088160, 6277505, 2042975, 660858, 213180, 91185570, 99239595, 67373670] }

theorem case_49_39_20_checked :
    (Witness.linear .conditional case_49_39_20).check 49 39 20 = true := by
  change case_49_39_20.check 49 39 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_39_21 : Certificate := {
  objectiveScale := 804
  eta := 2366532675
  rows := #[⟨.assumptionRow 21, 611⟩]
  caps := #[0, 0, 848544060, 307653060, 104311900, 36461095, 14048562, 4984536, 7583289750, 7276286325, 5007502500] }

theorem case_49_39_21_checked :
    (Witness.linear .conditional case_49_39_21).check 49 39 21 = true := by
  change case_49_39_21.check 49 39 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_39_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 35357670, 35357670, 25662825, 15967980] }

theorem case_49_39_22_checked :
    (Witness.linear .negative case_49_39_22).check 49 39 22 = true := by
  change case_49_39_22.check 49 39 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_39_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 9694845, 9694845] }

theorem case_49_39_23_checked :
    (Witness.linear .negative case_49_39_23).check 49 39 23 = true := by
  change case_49_39_23.check 49 39 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_39_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_39_24_checked :
    (Witness.linear .negative case_49_39_24).check 49 39 24 = true := by
  change case_49_39_24.check 49 39 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_39_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_39_25_checked :
    (Witness.linear .negative case_49_39_25).check 49 39 25 = true := by
  change case_49_39_25.check 49 39 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_40_1_checked :
    (Witness.rising).check 49 40 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_40_2_checked :
    (Witness.rising).check 49 40 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_40_3_checked :
    (Witness.rising).check 49 40 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_40_4_checked :
    (Witness.rising).check 49 40 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_40_5_checked :
    (Witness.rising).check 49 40 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_40_6_checked :
    (Witness.rising).check 49 40 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_40_7_checked :
    (Witness.rising).check 49 40 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_40_8_checked :
    (Witness.rising).check 49 40 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_40_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1, 0] }

theorem case_49_40_9_checked :
    (Witness.linear .positive case_49_40_9).check 49 40 9 = true := by
  change case_49_40_9.check 49 40 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_40_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1, 1] }

theorem case_49_40_10_checked :
    (Witness.linear .positive case_49_40_10).check 49 40 10 = true := by
  change case_49_40_10.check 49 40 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_40_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2, 1] }

theorem case_49_40_11_checked :
    (Witness.linear .positive case_49_40_11).check 49 40 11 = true := by
  change case_49_40_11.check 49 40 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_40_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_49_40_12_checked :
    (Witness.linear .positive case_49_40_12).check 49 40 12 = true := by
  change case_49_40_12.check 49 40 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_40_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_49_40_13_checked :
    (Witness.linear .positive case_49_40_13).check 49 40 13 = true := by
  change case_49_40_13.check 49 40 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_40_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_49_40_14_checked :
    (Witness.linear .positive case_49_40_14).check 49 40 14 = true := by
  change case_49_40_14.check 49 40 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_40_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_49_40_15_checked :
    (Witness.linear .positive case_49_40_15).check 49 40 15 = true := by
  change case_49_40_15.check 49 40 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_40_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_49_40_16_checked :
    (Witness.linear .positive case_49_40_16).check 49 40 16 = true := by
  change case_49_40_16.check 49 40 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_40_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_49_40_17_checked :
    (Witness.linear .positive case_49_40_17).check 49 40 17 = true := by
  change case_49_40_17.check 49 40 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_40_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_49_40_18_checked :
    (Witness.linear .positive case_49_40_18).check 49 40 18 = true := by
  change case_49_40_18.check 49 40 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_40_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_49_40_19_checked :
    (Witness.linear .positive case_49_40_19).check 49 40 19 = true := by
  change case_49_40_19.check 49 40 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_40_20 : Certificate := {
  objectiveScale := 8
  eta := 873396480
  rows := #[⟨.assumptionRow 20, 13⟩]
  caps := #[0, 0, 245022450, 69194580, 19684665, 5794620, 1723528, 518738, 158270, 49062] }

theorem case_49_40_20_checked :
    (Witness.linear .conditional case_49_40_20).check 49 40 20 = true := by
  change case_49_40_20.check 49 40 20 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_40_21 : Certificate := {
  objectiveScale := 998
  eta := 11267310840
  rows := #[⟨.assumptionRow 21, 887⟩]
  caps := #[0, 0, 3731955045, 1203621510, 380882645, 127794095, 45272326, 27293640, 15971741880, 14932722630] }

theorem case_49_40_21_checked :
    (Witness.linear .conditional case_49_40_21).check 49 40 21 = true := by
  change case_49_40_21.check 49 40 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_40_22 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 129644790, 129644790, 94287120, 58929450] }

theorem case_49_40_22_checked :
    (Witness.linear .negative case_49_40_22).check 49 40 22 = true := by
  change case_49_40_22.check 49 40 22 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_40_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 35357670, 35357670] }

theorem case_49_40_23_checked :
    (Witness.linear .negative case_49_40_23).check 49 40 23 = true := by
  change case_49_40_23.check 49 40 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_40_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_40_24_checked :
    (Witness.linear .negative case_49_40_24).check 49 40 24 = true := by
  change case_49_40_24.check 49 40 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_40_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_40_25_checked :
    (Witness.linear .negative case_49_40_25).check 49 40 25 = true := by
  change case_49_40_25.check 49 40 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_40_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_40_26_checked :
    (Witness.linear .negative case_49_40_26).check 49 40 26 = true := by
  change case_49_40_26.check 49 40 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_41_1_checked :
    (Witness.rising).check 49 41 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_41_2_checked :
    (Witness.rising).check 49 41 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_41_3_checked :
    (Witness.rising).check 49 41 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_41_4_checked :
    (Witness.rising).check 49 41 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_41_5_checked :
    (Witness.rising).check 49 41 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_41_6_checked :
    (Witness.rising).check 49 41 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_41_7_checked :
    (Witness.rising).check 49 41 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_41_8_checked :
    (Witness.rising).check 49 41 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_41_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1, 1] }

theorem case_49_41_9_checked :
    (Witness.linear .positive case_49_41_9).check 49 41 9 = true := by
  change case_49_41_9.check 49 41 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_41_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2, 1] }

theorem case_49_41_10_checked :
    (Witness.linear .positive case_49_41_10).check 49 41 10 = true := by
  change case_49_41_10.check 49 41 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_41_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5, 2] }

theorem case_49_41_11_checked :
    (Witness.linear .positive case_49_41_11).check 49 41 11 = true := by
  change case_49_41_11.check 49 41 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_41_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14, 5] }

theorem case_49_41_12_checked :
    (Witness.linear .positive case_49_41_12).check 49 41 12 = true := by
  change case_49_41_12.check 49 41 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_41_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42, 14] }

theorem case_49_41_13_checked :
    (Witness.linear .positive case_49_41_13).check 49 41 13 = true := by
  change case_49_41_13.check 49 41 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_41_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132, 42] }

theorem case_49_41_14_checked :
    (Witness.linear .positive case_49_41_14).check 49 41 14 = true := by
  change case_49_41_14.check 49 41 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_41_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_49_41_15_checked :
    (Witness.linear .positive case_49_41_15).check 49 41 15 = true := by
  change case_49_41_15.check 49 41 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_41_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_49_41_16_checked :
    (Witness.linear .positive case_49_41_16).check 49 41 16 = true := by
  change case_49_41_16.check 49 41 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_41_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_49_41_17_checked :
    (Witness.linear .positive case_49_41_17).check 49 41 17 = true := by
  change case_49_41_17.check 49 41 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_41_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_49_41_18_checked :
    (Witness.linear .positive case_49_41_18).check 49 41 18 = true := by
  change case_49_41_18.check 49 41 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_41_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_49_41_19_checked :
    (Witness.linear .positive case_49_41_19).check 49 41 19 = true := by
  change case_49_41_19.check 49 41 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_41_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_49_41_20_checked :
    (Witness.linear .positive case_49_41_20).check 49 41 20 = true := by
  change case_49_41_20.check 49 41 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_41_21 : Certificate := {
  objectiveScale := 95
  eta := 1870854960
  rows := #[⟨.assumptionRow 21, 91⟩]
  caps := #[0, 0, 564482100, 190285095, 62547810, 20213435, 6455801, 1855967520, 3466292280] }

theorem case_49_41_21_checked :
    (Witness.linear .conditional case_49_41_21).check 49 41 21 = true := by
  change case_49_41_21.check 49 41 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_41_22 : Certificate := {
  objectiveScale := 17
  eta := 13656825
  rows := #[⟨.assumptionRow 22, 10⟩]
  caps := #[0, 0, 5278845, 2022735, 847550, 298034, 138567, 1275977670, 1255507440] }

theorem case_49_41_22_checked :
    (Witness.linear .conditional case_49_41_22).check 49 41 22 = true := by
  change case_49_41_22.check 49 41 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_41_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 129644790, 129644790] }

theorem case_49_41_23_checked :
    (Witness.linear .negative case_49_41_23).check 49 41 23 = true := by
  change case_49_41_23.check 49 41 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_41_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_41_24_checked :
    (Witness.linear .negative case_49_41_24).check 49 41 24 = true := by
  change case_49_41_24.check 49 41 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_41_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_41_25_checked :
    (Witness.linear .negative case_49_41_25).check 49 41 25 = true := by
  change case_49_41_25.check 49 41 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_41_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_41_26_checked :
    (Witness.linear .negative case_49_41_26).check 49 41 26 = true := by
  change case_49_41_26.check 49 41 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_42_1_checked :
    (Witness.rising).check 49 42 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_42_2_checked :
    (Witness.rising).check 49 42 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_42_3_checked :
    (Witness.rising).check 49 42 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_42_4_checked :
    (Witness.rising).check 49 42 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_42_5_checked :
    (Witness.rising).check 49 42 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_42_6_checked :
    (Witness.rising).check 49 42 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_42_7_checked :
    (Witness.rising).check 49 42 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_42_8_checked :
    (Witness.rising).check 49 42 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_42_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2, 1] }

theorem case_49_42_9_checked :
    (Witness.linear .positive case_49_42_9).check 49 42 9 = true := by
  change case_49_42_9.check 49 42 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_42_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5, 2] }

theorem case_49_42_10_checked :
    (Witness.linear .positive case_49_42_10).check 49 42 10 = true := by
  change case_49_42_10.check 49 42 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_42_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14, 5] }

theorem case_49_42_11_checked :
    (Witness.linear .positive case_49_42_11).check 49 42 11 = true := by
  change case_49_42_11.check 49 42 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_42_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42, 14] }

theorem case_49_42_12_checked :
    (Witness.linear .positive case_49_42_12).check 49 42 12 = true := by
  change case_49_42_12.check 49 42 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_42_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132, 42] }

theorem case_49_42_13_checked :
    (Witness.linear .positive case_49_42_13).check 49 42 13 = true := by
  change case_49_42_13.check 49 42 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_42_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429, 132] }

theorem case_49_42_14_checked :
    (Witness.linear .positive case_49_42_14).check 49 42 14 = true := by
  change case_49_42_14.check 49 42 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_42_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430, 429] }

theorem case_49_42_15_checked :
    (Witness.linear .positive case_49_42_15).check 49 42 15 = true := by
  change case_49_42_15.check 49 42 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_42_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862, 1430] }

theorem case_49_42_16_checked :
    (Witness.linear .positive case_49_42_16).check 49 42 16 = true := by
  change case_49_42_16.check 49 42 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_42_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796, 4862] }

theorem case_49_42_17_checked :
    (Witness.linear .positive case_49_42_17).check 49 42 17 = true := by
  change case_49_42_17.check 49 42 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_42_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786, 16796] }

theorem case_49_42_18_checked :
    (Witness.linear .positive case_49_42_18).check 49 42 18 = true := by
  change case_49_42_18.check 49 42 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_42_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_49_42_19_checked :
    (Witness.linear .positive case_49_42_19).check 49 42 19 = true := by
  change case_49_42_19.check 49 42 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_42_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_49_42_20_checked :
    (Witness.linear .positive case_49_42_20).check 49 42 20 = true := by
  change case_49_42_20.check 49 42 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_42_21 : Certificate := {
  objectiveScale := 19
  eta := 32711427540
  rows := #[⟨.assumptionRow 21, 51⟩]
  caps := #[0, 0, 8931843690, 2463251010, 683581620, 191045475, 53823105, 15303740] }

theorem case_49_42_21_checked :
    (Witness.linear .conditional case_49_42_21).check 49 42 21 = true := by
  change case_49_42_21.check 49 42 21 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_42_22 : Certificate := {
  objectiveScale := 12
  eta := 8714355
  rows := #[⟨.assumptionRow 22, 7⟩]
  caps := #[0, 0, 3502785, 1282710, 562925, 201894, 3295707030, 3247943160] }

theorem case_49_42_22_checked :
    (Witness.linear .conditional case_49_42_22).check 49 42 22 = true := by
  change case_49_42_22.check 49 42 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_42_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 477638700, 477638700] }

theorem case_49_42_23_checked :
    (Witness.linear .negative case_49_42_23).check 49 42 23 = true := by
  change case_49_42_23.check 49 42 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_42_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_42_24_checked :
    (Witness.linear .negative case_49_42_24).check 49 42 24 = true := by
  change case_49_42_24.check 49 42 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_42_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_42_25_checked :
    (Witness.linear .negative case_49_42_25).check 49 42 25 = true := by
  change case_49_42_25.check 49 42 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_42_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_42_26_checked :
    (Witness.linear .negative case_49_42_26).check 49 42 26 = true := by
  change case_49_42_26.check 49 42 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_42_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0, 0] }

theorem case_49_42_27_checked :
    (Witness.linear .negative case_49_42_27).check 49 42 27 = true := by
  change case_49_42_27.check 49 42 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_43_1_checked :
    (Witness.rising).check 49 43 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_43_2_checked :
    (Witness.rising).check 49 43 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_43_3_checked :
    (Witness.rising).check 49 43 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_43_4_checked :
    (Witness.rising).check 49 43 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_43_5_checked :
    (Witness.rising).check 49 43 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_43_6_checked :
    (Witness.rising).check 49 43 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_43_7_checked :
    (Witness.rising).check 49 43 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_43_8_checked :
    (Witness.rising).check 49 43 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_43_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5, 2] }

theorem case_49_43_9_checked :
    (Witness.linear .positive case_49_43_9).check 49 43 9 = true := by
  change case_49_43_9.check 49 43 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_43_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14, 5] }

theorem case_49_43_10_checked :
    (Witness.linear .positive case_49_43_10).check 49 43 10 = true := by
  change case_49_43_10.check 49 43 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_43_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42, 14] }

theorem case_49_43_11_checked :
    (Witness.linear .positive case_49_43_11).check 49 43 11 = true := by
  change case_49_43_11.check 49 43 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_43_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132, 42] }

theorem case_49_43_12_checked :
    (Witness.linear .positive case_49_43_12).check 49 43 12 = true := by
  change case_49_43_12.check 49 43 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_43_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429, 132] }

theorem case_49_43_13_checked :
    (Witness.linear .positive case_49_43_13).check 49 43 13 = true := by
  change case_49_43_13.check 49 43 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_43_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430, 429] }

theorem case_49_43_14_checked :
    (Witness.linear .positive case_49_43_14).check 49 43 14 = true := by
  change case_49_43_14.check 49 43 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_43_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862, 1430] }

theorem case_49_43_15_checked :
    (Witness.linear .positive case_49_43_15).check 49 43 15 = true := by
  change case_49_43_15.check 49 43 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_43_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796, 4862] }

theorem case_49_43_16_checked :
    (Witness.linear .positive case_49_43_16).check 49 43 16 = true := by
  change case_49_43_16.check 49 43 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_43_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786, 16796] }

theorem case_49_43_17_checked :
    (Witness.linear .positive case_49_43_17).check 49 43 17 = true := by
  change case_49_43_17.check 49 43 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_43_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012, 58786] }

theorem case_49_43_18_checked :
    (Witness.linear .positive case_49_43_18).check 49 43 18 = true := by
  change case_49_43_18.check 49 43 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_43_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900, 208012] }

theorem case_49_43_19_checked :
    (Witness.linear .positive case_49_43_19).check 49 43 19 = true := by
  change case_49_43_19.check 49 43 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_43_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440, 742900] }

theorem case_49_43_20_checked :
    (Witness.linear .positive case_49_43_20).check 49 43 20 = true := by
  change case_49_43_20.check 49 43 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_43_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845, 2674440] }

theorem case_49_43_21_checked :
    (Witness.linear .positive case_49_43_21).check 49 43 21 = true := by
  change case_49_43_21.check 49 43 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_43_22 : Certificate := {
  objectiveScale := 641
  eta := 17366198760
  rows := #[⟨.assumptionRow 22, 553⟩]
  caps := #[0, 0, 5370643980, 1864611840, 633551100, 208095030, 68854410] }

theorem case_49_43_22_checked :
    (Witness.linear .conditional case_49_43_22).check 49 43 22 = true := by
  change case_49_43_22.check 49 43 22 .conditional = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_43_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 1767263190, 1767263190] }

theorem case_49_43_23_checked :
    (Witness.linear .negative case_49_43_23).check 49 43 23 = true := by
  change case_49_43_23.check 49 43 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_43_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_49_43_24_checked :
    (Witness.linear .negative case_49_43_24).check 49 43 24 = true := by
  change case_49_43_24.check 49 43 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_43_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_49_43_25_checked :
    (Witness.linear .negative case_49_43_25).check 49 43 25 = true := by
  change case_49_43_25.check 49 43 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_43_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_49_43_26_checked :
    (Witness.linear .negative case_49_43_26).check 49 43 26 = true := by
  change case_49_43_26.check 49 43 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_43_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_49_43_27_checked :
    (Witness.linear .negative case_49_43_27).check 49 43 27 = true := by
  change case_49_43_27.check 49 43 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_43_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0, 0] }

theorem case_49_43_28_checked :
    (Witness.linear .negative case_49_43_28).check 49 43 28 = true := by
  change case_49_43_28.check 49 43 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_44_1_checked :
    (Witness.rising).check 49 44 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_44_2_checked :
    (Witness.rising).check 49 44 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_44_3_checked :
    (Witness.rising).check 49 44 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_44_4_checked :
    (Witness.rising).check 49 44 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_44_5_checked :
    (Witness.rising).check 49 44 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_44_6_checked :
    (Witness.rising).check 49 44 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_44_7_checked :
    (Witness.rising).check 49 44 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_44_8_checked :
    (Witness.rising).check 49 44 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_44_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14, 5] }

theorem case_49_44_9_checked :
    (Witness.linear .positive case_49_44_9).check 49 44 9 = true := by
  change case_49_44_9.check 49 44 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_44_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42, 14] }

theorem case_49_44_10_checked :
    (Witness.linear .positive case_49_44_10).check 49 44 10 = true := by
  change case_49_44_10.check 49 44 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_44_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132, 42] }

theorem case_49_44_11_checked :
    (Witness.linear .positive case_49_44_11).check 49 44 11 = true := by
  change case_49_44_11.check 49 44 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_44_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429, 132] }

theorem case_49_44_12_checked :
    (Witness.linear .positive case_49_44_12).check 49 44 12 = true := by
  change case_49_44_12.check 49 44 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_44_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430, 429] }

theorem case_49_44_13_checked :
    (Witness.linear .positive case_49_44_13).check 49 44 13 = true := by
  change case_49_44_13.check 49 44 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_44_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862, 1430] }

theorem case_49_44_14_checked :
    (Witness.linear .positive case_49_44_14).check 49 44 14 = true := by
  change case_49_44_14.check 49 44 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_44_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796, 4862] }

theorem case_49_44_15_checked :
    (Witness.linear .positive case_49_44_15).check 49 44 15 = true := by
  change case_49_44_15.check 49 44 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_44_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786, 16796] }

theorem case_49_44_16_checked :
    (Witness.linear .positive case_49_44_16).check 49 44 16 = true := by
  change case_49_44_16.check 49 44 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_44_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012, 58786] }

theorem case_49_44_17_checked :
    (Witness.linear .positive case_49_44_17).check 49 44 17 = true := by
  change case_49_44_17.check 49 44 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_44_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900, 208012] }

theorem case_49_44_18_checked :
    (Witness.linear .positive case_49_44_18).check 49 44 18 = true := by
  change case_49_44_18.check 49 44 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_44_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440, 742900] }

theorem case_49_44_19_checked :
    (Witness.linear .positive case_49_44_19).check 49 44 19 = true := by
  change case_49_44_19.check 49 44 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_44_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845, 2674440] }

theorem case_49_44_20_checked :
    (Witness.linear .positive case_49_44_20).check 49 44 20 = true := by
  change case_49_44_20.check 49 44 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_44_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670, 9694845] }

theorem case_49_44_21_checked :
    (Witness.linear .positive case_49_44_21).check 49 44 21 = true := by
  change case_49_44_21.check 49 44 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_44_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790, 35357670] }

theorem case_49_44_22_checked :
    (Witness.linear .positive case_49_44_22).check 49 44 22 = true := by
  change case_49_44_22.check 49 44 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_44_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 6564120420, 6564120420] }

theorem case_49_44_23_checked :
    (Witness.linear .negative case_49_44_23).check 49 44 23 = true := by
  change case_49_44_23.check 49 44 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_44_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_49_44_24_checked :
    (Witness.linear .negative case_49_44_24).check 49 44 24 = true := by
  change case_49_44_24.check 49 44 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_44_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_49_44_25_checked :
    (Witness.linear .negative case_49_44_25).check 49 44 25 = true := by
  change case_49_44_25.check 49 44 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_44_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_49_44_26_checked :
    (Witness.linear .negative case_49_44_26).check 49 44 26 = true := by
  change case_49_44_26.check 49 44 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_44_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_49_44_27_checked :
    (Witness.linear .negative case_49_44_27).check 49 44 27 = true := by
  change case_49_44_27.check 49 44 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_44_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0, 0] }

theorem case_49_44_28_checked :
    (Witness.linear .negative case_49_44_28).check 49 44 28 = true := by
  change case_49_44_28.check 49 44 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_45_1_checked :
    (Witness.rising).check 49 45 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_45_2_checked :
    (Witness.rising).check 49 45 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_45_3_checked :
    (Witness.rising).check 49 45 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_45_4_checked :
    (Witness.rising).check 49 45 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_45_5_checked :
    (Witness.rising).check 49 45 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_45_6_checked :
    (Witness.rising).check 49 45 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_45_7_checked :
    (Witness.rising).check 49 45 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_45_8_checked :
    (Witness.rising).check 49 45 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_45_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42, 14] }

theorem case_49_45_9_checked :
    (Witness.linear .positive case_49_45_9).check 49 45 9 = true := by
  change case_49_45_9.check 49 45 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_45_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132, 42] }

theorem case_49_45_10_checked :
    (Witness.linear .positive case_49_45_10).check 49 45 10 = true := by
  change case_49_45_10.check 49 45 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_45_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429, 132] }

theorem case_49_45_11_checked :
    (Witness.linear .positive case_49_45_11).check 49 45 11 = true := by
  change case_49_45_11.check 49 45 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_45_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430, 429] }

theorem case_49_45_12_checked :
    (Witness.linear .positive case_49_45_12).check 49 45 12 = true := by
  change case_49_45_12.check 49 45 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_45_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862, 1430] }

theorem case_49_45_13_checked :
    (Witness.linear .positive case_49_45_13).check 49 45 13 = true := by
  change case_49_45_13.check 49 45 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_45_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796, 4862] }

theorem case_49_45_14_checked :
    (Witness.linear .positive case_49_45_14).check 49 45 14 = true := by
  change case_49_45_14.check 49 45 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_45_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786, 16796] }

theorem case_49_45_15_checked :
    (Witness.linear .positive case_49_45_15).check 49 45 15 = true := by
  change case_49_45_15.check 49 45 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_45_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012, 58786] }

theorem case_49_45_16_checked :
    (Witness.linear .positive case_49_45_16).check 49 45 16 = true := by
  change case_49_45_16.check 49 45 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_45_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900, 208012] }

theorem case_49_45_17_checked :
    (Witness.linear .positive case_49_45_17).check 49 45 17 = true := by
  change case_49_45_17.check 49 45 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_45_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440, 742900] }

theorem case_49_45_18_checked :
    (Witness.linear .positive case_49_45_18).check 49 45 18 = true := by
  change case_49_45_18.check 49 45 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_45_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845, 2674440] }

theorem case_49_45_19_checked :
    (Witness.linear .positive case_49_45_19).check 49 45 19 = true := by
  change case_49_45_19.check 49 45 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_45_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670, 9694845] }

theorem case_49_45_20_checked :
    (Witness.linear .positive case_49_45_20).check 49 45 20 = true := by
  change case_49_45_20.check 49 45 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_45_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790, 35357670] }

theorem case_49_45_21_checked :
    (Witness.linear .positive case_49_45_21).check 49 45 21 = true := by
  change case_49_45_21.check 49 45 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_45_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700, 129644790] }

theorem case_49_45_22_checked :
    (Witness.linear .positive case_49_45_22).check 49 45 22 = true := by
  change case_49_45_22.check 49 45 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_45_23 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 24466267020, 24466267020] }

theorem case_49_45_23_checked :
    (Witness.linear .negative case_49_45_23).check 49 45 23 = true := by
  change case_49_45_23.check 49 45 23 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_45_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_49_45_24_checked :
    (Witness.linear .negative case_49_45_24).check 49 45 24 = true := by
  change case_49_45_24.check 49 45 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_45_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_49_45_25_checked :
    (Witness.linear .negative case_49_45_25).check 49 45 25 = true := by
  change case_49_45_25.check 49 45 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_45_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_49_45_26_checked :
    (Witness.linear .negative case_49_45_26).check 49 45 26 = true := by
  change case_49_45_26.check 49 45 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_45_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_49_45_27_checked :
    (Witness.linear .negative case_49_45_27).check 49 45 27 = true := by
  change case_49_45_27.check 49 45 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_45_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_49_45_28_checked :
    (Witness.linear .negative case_49_45_28).check 49 45 28 = true := by
  change case_49_45_28.check 49 45 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_45_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0, 0] }

theorem case_49_45_29_checked :
    (Witness.linear .negative case_49_45_29).check 49 45 29 = true := by
  change case_49_45_29.check 49 45 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_46_1_checked :
    (Witness.rising).check 49 46 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_46_2_checked :
    (Witness.rising).check 49 46 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_46_3_checked :
    (Witness.rising).check 49 46 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_46_4_checked :
    (Witness.rising).check 49 46 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_46_5_checked :
    (Witness.rising).check 49 46 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_46_6_checked :
    (Witness.rising).check 49 46 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_46_7_checked :
    (Witness.rising).check 49 46 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_46_8_checked :
    (Witness.rising).check 49 46 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_46_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132, 42] }

theorem case_49_46_9_checked :
    (Witness.linear .positive case_49_46_9).check 49 46 9 = true := by
  change case_49_46_9.check 49 46 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_46_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429, 132] }

theorem case_49_46_10_checked :
    (Witness.linear .positive case_49_46_10).check 49 46 10 = true := by
  change case_49_46_10.check 49 46 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_46_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430, 429] }

theorem case_49_46_11_checked :
    (Witness.linear .positive case_49_46_11).check 49 46 11 = true := by
  change case_49_46_11.check 49 46 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_46_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862, 1430] }

theorem case_49_46_12_checked :
    (Witness.linear .positive case_49_46_12).check 49 46 12 = true := by
  change case_49_46_12.check 49 46 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_46_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796, 4862] }

theorem case_49_46_13_checked :
    (Witness.linear .positive case_49_46_13).check 49 46 13 = true := by
  change case_49_46_13.check 49 46 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_46_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786, 16796] }

theorem case_49_46_14_checked :
    (Witness.linear .positive case_49_46_14).check 49 46 14 = true := by
  change case_49_46_14.check 49 46 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_46_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012, 58786] }

theorem case_49_46_15_checked :
    (Witness.linear .positive case_49_46_15).check 49 46 15 = true := by
  change case_49_46_15.check 49 46 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_46_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900, 208012] }

theorem case_49_46_16_checked :
    (Witness.linear .positive case_49_46_16).check 49 46 16 = true := by
  change case_49_46_16.check 49 46 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_46_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440, 742900] }

theorem case_49_46_17_checked :
    (Witness.linear .positive case_49_46_17).check 49 46 17 = true := by
  change case_49_46_17.check 49 46 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_46_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845, 2674440] }

theorem case_49_46_18_checked :
    (Witness.linear .positive case_49_46_18).check 49 46 18 = true := by
  change case_49_46_18.check 49 46 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_46_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670, 9694845] }

theorem case_49_46_19_checked :
    (Witness.linear .positive case_49_46_19).check 49 46 19 = true := by
  change case_49_46_19.check 49 46 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_46_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790, 35357670] }

theorem case_49_46_20_checked :
    (Witness.linear .positive case_49_46_20).check 49 46 20 = true := by
  change case_49_46_20.check 49 46 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_46_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700, 129644790] }

theorem case_49_46_21_checked :
    (Witness.linear .positive case_49_46_21).check 49 46 21 = true := by
  change case_49_46_21.check 49 46 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_46_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190, 477638700] }

theorem case_49_46_22_checked :
    (Witness.linear .positive case_49_46_22).check 49 46 22 = true := by
  change case_49_46_22.check 49 46 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_46_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420, 1767263190] }

theorem case_49_46_23_checked :
    (Witness.linear .positive case_49_46_23).check 49 46 23 = true := by
  change case_49_46_23.check 49 46 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_46_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_49_46_24_checked :
    (Witness.linear .negative case_49_46_24).check 49 46 24 = true := by
  change case_49_46_24.check 49 46 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_46_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_49_46_25_checked :
    (Witness.linear .negative case_49_46_25).check 49 46 25 = true := by
  change case_49_46_25.check 49 46 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_46_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_49_46_26_checked :
    (Witness.linear .negative case_49_46_26).check 49 46 26 = true := by
  change case_49_46_26.check 49 46 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_46_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_49_46_27_checked :
    (Witness.linear .negative case_49_46_27).check 49 46 27 = true := by
  change case_49_46_27.check 49 46 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_46_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_49_46_28_checked :
    (Witness.linear .negative case_49_46_28).check 49 46 28 = true := by
  change case_49_46_28.check 49 46 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_46_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_49_46_29_checked :
    (Witness.linear .negative case_49_46_29).check 49 46 29 = true := by
  change case_49_46_29.check 49 46 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_46_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0, 0] }

theorem case_49_46_30_checked :
    (Witness.linear .negative case_49_46_30).check 49 46 30 = true := by
  change case_49_46_30.check 49 46 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_47_1_checked :
    (Witness.rising).check 49 47 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_47_2_checked :
    (Witness.rising).check 49 47 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_47_3_checked :
    (Witness.rising).check 49 47 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_47_4_checked :
    (Witness.rising).check 49 47 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_47_5_checked :
    (Witness.rising).check 49 47 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_47_6_checked :
    (Witness.rising).check 49 47 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_47_7_checked :
    (Witness.rising).check 49 47 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_47_8_checked :
    (Witness.rising).check 49 47 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_47_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0, 132] }

theorem case_49_47_9_checked :
    (Witness.linear .positive case_49_47_9).check 49 47 9 = true := by
  change case_49_47_9.check 49 47 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_47_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0, 429] }

theorem case_49_47_10_checked :
    (Witness.linear .positive case_49_47_10).check 49 47 10 = true := by
  change case_49_47_10.check 49 47 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_47_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0, 1430] }

theorem case_49_47_11_checked :
    (Witness.linear .positive case_49_47_11).check 49 47 11 = true := by
  change case_49_47_11.check 49 47 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_47_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0, 4862] }

theorem case_49_47_12_checked :
    (Witness.linear .positive case_49_47_12).check 49 47 12 = true := by
  change case_49_47_12.check 49 47 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_47_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0, 16796] }

theorem case_49_47_13_checked :
    (Witness.linear .positive case_49_47_13).check 49 47 13 = true := by
  change case_49_47_13.check 49 47 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_47_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0, 58786] }

theorem case_49_47_14_checked :
    (Witness.linear .positive case_49_47_14).check 49 47 14 = true := by
  change case_49_47_14.check 49 47 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_47_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0, 208012] }

theorem case_49_47_15_checked :
    (Witness.linear .positive case_49_47_15).check 49 47 15 = true := by
  change case_49_47_15.check 49 47 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_47_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0, 742900] }

theorem case_49_47_16_checked :
    (Witness.linear .positive case_49_47_16).check 49 47 16 = true := by
  change case_49_47_16.check 49 47 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_47_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0, 2674440] }

theorem case_49_47_17_checked :
    (Witness.linear .positive case_49_47_17).check 49 47 17 = true := by
  change case_49_47_17.check 49 47 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_47_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0, 9694845] }

theorem case_49_47_18_checked :
    (Witness.linear .positive case_49_47_18).check 49 47 18 = true := by
  change case_49_47_18.check 49 47 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_47_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0, 35357670] }

theorem case_49_47_19_checked :
    (Witness.linear .positive case_49_47_19).check 49 47 19 = true := by
  change case_49_47_19.check 49 47 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_47_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0, 129644790] }

theorem case_49_47_20_checked :
    (Witness.linear .positive case_49_47_20).check 49 47 20 = true := by
  change case_49_47_20.check 49 47 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_47_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0, 477638700] }

theorem case_49_47_21_checked :
    (Witness.linear .positive case_49_47_21).check 49 47 21 = true := by
  change case_49_47_21.check 49 47 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_47_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0, 1767263190] }

theorem case_49_47_22_checked :
    (Witness.linear .positive case_49_47_22).check 49 47 22 = true := by
  change case_49_47_22.check 49 47 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_47_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0, 6564120420] }

theorem case_49_47_23_checked :
    (Witness.linear .positive case_49_47_23).check 49 47 23 = true := by
  change case_49_47_23.check 49 47 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_47_24 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_49_47_24_checked :
    (Witness.linear .negative case_49_47_24).check 49 47 24 = true := by
  change case_49_47_24.check 49 47 24 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_47_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_49_47_25_checked :
    (Witness.linear .negative case_49_47_25).check 49 47 25 = true := by
  change case_49_47_25.check 49 47 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_47_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_49_47_26_checked :
    (Witness.linear .negative case_49_47_26).check 49 47 26 = true := by
  change case_49_47_26.check 49 47 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_47_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_49_47_27_checked :
    (Witness.linear .negative case_49_47_27).check 49 47 27 = true := by
  change case_49_47_27.check 49 47 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_47_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_49_47_28_checked :
    (Witness.linear .negative case_49_47_28).check 49 47 28 = true := by
  change case_49_47_28.check 49 47 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_47_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_49_47_29_checked :
    (Witness.linear .negative case_49_47_29).check 49 47 29 = true := by
  change case_49_47_29.check 49 47 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_47_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_49_47_30_checked :
    (Witness.linear .negative case_49_47_30).check 49 47 30 = true := by
  change case_49_47_30.check 49 47 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_48_1_checked :
    (Witness.rising).check 49 48 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_48_2_checked :
    (Witness.rising).check 49 48 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_48_3_checked :
    (Witness.rising).check 49 48 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_48_4_checked :
    (Witness.rising).check 49 48 4 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_48_5_checked :
    (Witness.rising).check 49 48 5 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_48_6_checked :
    (Witness.rising).check 49 48 6 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_48_7_checked :
    (Witness.rising).check 49 48 7 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_49_48_8_checked :
    (Witness.rising).check 49 48 8 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_48_9 : Certificate := {
  objectiveScale := 1
  eta := 429
  rows := #[]
  caps := #[0, 0] }

theorem case_49_48_9_checked :
    (Witness.linear .positive case_49_48_9).check 49 48 9 = true := by
  change case_49_48_9.check 49 48 9 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_48_10 : Certificate := {
  objectiveScale := 1
  eta := 1430
  rows := #[]
  caps := #[0, 0] }

theorem case_49_48_10_checked :
    (Witness.linear .positive case_49_48_10).check 49 48 10 = true := by
  change case_49_48_10.check 49 48 10 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_48_11 : Certificate := {
  objectiveScale := 1
  eta := 4862
  rows := #[]
  caps := #[0, 0] }

theorem case_49_48_11_checked :
    (Witness.linear .positive case_49_48_11).check 49 48 11 = true := by
  change case_49_48_11.check 49 48 11 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_48_12 : Certificate := {
  objectiveScale := 1
  eta := 16796
  rows := #[]
  caps := #[0, 0] }

theorem case_49_48_12_checked :
    (Witness.linear .positive case_49_48_12).check 49 48 12 = true := by
  change case_49_48_12.check 49 48 12 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_48_13 : Certificate := {
  objectiveScale := 1
  eta := 58786
  rows := #[]
  caps := #[0, 0] }

theorem case_49_48_13_checked :
    (Witness.linear .positive case_49_48_13).check 49 48 13 = true := by
  change case_49_48_13.check 49 48 13 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_48_14 : Certificate := {
  objectiveScale := 1
  eta := 208012
  rows := #[]
  caps := #[0, 0] }

theorem case_49_48_14_checked :
    (Witness.linear .positive case_49_48_14).check 49 48 14 = true := by
  change case_49_48_14.check 49 48 14 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_48_15 : Certificate := {
  objectiveScale := 1
  eta := 742900
  rows := #[]
  caps := #[0, 0] }

theorem case_49_48_15_checked :
    (Witness.linear .positive case_49_48_15).check 49 48 15 = true := by
  change case_49_48_15.check 49 48 15 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_48_16 : Certificate := {
  objectiveScale := 1
  eta := 2674440
  rows := #[]
  caps := #[0, 0] }

theorem case_49_48_16_checked :
    (Witness.linear .positive case_49_48_16).check 49 48 16 = true := by
  change case_49_48_16.check 49 48 16 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_48_17 : Certificate := {
  objectiveScale := 1
  eta := 9694845
  rows := #[]
  caps := #[0, 0] }

theorem case_49_48_17_checked :
    (Witness.linear .positive case_49_48_17).check 49 48 17 = true := by
  change case_49_48_17.check 49 48 17 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_48_18 : Certificate := {
  objectiveScale := 1
  eta := 35357670
  rows := #[]
  caps := #[0, 0] }

theorem case_49_48_18_checked :
    (Witness.linear .positive case_49_48_18).check 49 48 18 = true := by
  change case_49_48_18.check 49 48 18 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_48_19 : Certificate := {
  objectiveScale := 1
  eta := 129644790
  rows := #[]
  caps := #[0, 0] }

theorem case_49_48_19_checked :
    (Witness.linear .positive case_49_48_19).check 49 48 19 = true := by
  change case_49_48_19.check 49 48 19 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_48_20 : Certificate := {
  objectiveScale := 1
  eta := 477638700
  rows := #[]
  caps := #[0, 0] }

theorem case_49_48_20_checked :
    (Witness.linear .positive case_49_48_20).check 49 48 20 = true := by
  change case_49_48_20.check 49 48 20 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_48_21 : Certificate := {
  objectiveScale := 1
  eta := 1767263190
  rows := #[]
  caps := #[0, 0] }

theorem case_49_48_21_checked :
    (Witness.linear .positive case_49_48_21).check 49 48 21 = true := by
  change case_49_48_21.check 49 48 21 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_48_22 : Certificate := {
  objectiveScale := 1
  eta := 6564120420
  rows := #[]
  caps := #[0, 0] }

theorem case_49_48_22_checked :
    (Witness.linear .positive case_49_48_22).check 49 48 22 = true := by
  change case_49_48_22.check 49 48 22 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_48_23 : Certificate := {
  objectiveScale := 1
  eta := 24466267020
  rows := #[]
  caps := #[0, 0] }

theorem case_49_48_23_checked :
    (Witness.linear .positive case_49_48_23).check 49 48 23 = true := by
  change case_49_48_23.check 49 48 23 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_48_24 : Certificate := {
  objectiveScale := 1
  eta := 91482563640
  rows := #[]
  caps := #[0, 0] }

theorem case_49_48_24_checked :
    (Witness.linear .positive case_49_48_24).check 49 48 24 = true := by
  change case_49_48_24.check 49 48 24 .positive = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_48_25 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_49_48_25_checked :
    (Witness.linear .negative case_49_48_25).check 49 48 25 = true := by
  change case_49_48_25.check 49 48 25 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_48_26 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_49_48_26_checked :
    (Witness.linear .negative case_49_48_26).check 49 48 26 = true := by
  change case_49_48_26.check 49 48 26 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_48_27 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_49_48_27_checked :
    (Witness.linear .negative case_49_48_27).check 49 48 27 = true := by
  change case_49_48_27.check 49 48 27 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_48_28 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_49_48_28_checked :
    (Witness.linear .negative case_49_48_28).check 49 48 28 = true := by
  change case_49_48_28.check 49 48 28 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_48_29 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_49_48_29_checked :
    (Witness.linear .negative case_49_48_29).check 49 48 29 = true := by
  change case_49_48_29.check 49 48 29 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_48_30 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_49_48_30_checked :
    (Witness.linear .negative case_49_48_30).check 49 48 30 = true := by
  change case_49_48_30.check 49 48 30 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_49_48_31 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_49_48_31_checked :
    (Witness.linear .negative case_49_48_31).check 49 48 31 = true := by
  change case_49_48_31.check 49 48 31 .negative = true
  rw [← Certificate.kernelCheck_eq_check]
  simp only [Certificate.kernelCheck, Certificate.KernelAccepts,
    Certificate.kernelResidualCheck, Certificate.bound_eq_kernel, Certificate.cap,
    targetCoeff, targetConstant, kernelCoeff, rhs, meanBase, meanBeta, edgeGap,
    differenceCoeff, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_49 (a k : ℕ) (h : Domain 49 a k) :
    ∃ w : Witness, w.check 49 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 25 ≤ a := by omega
  have haHi : a ≤ 48 := by omega
  interval_cases a

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_49_25_1_checked⟩

    · exact ⟨Witness.rising, case_49_25_2_checked⟩

    · exact ⟨Witness.rising, case_49_25_3_checked⟩

    · exact ⟨Witness.rising, case_49_25_4_checked⟩

    · exact ⟨Witness.rising, case_49_25_5_checked⟩

    · exact ⟨Witness.rising, case_49_25_6_checked⟩

    · exact ⟨Witness.rising, case_49_25_7_checked⟩

    · exact ⟨Witness.rising, case_49_25_8_checked⟩

    · exact ⟨Witness.rising, case_49_25_9_checked⟩

    · exact ⟨Witness.linear .positive case_49_25_10, case_49_25_10_checked⟩

    · exact ⟨Witness.linear .positive case_49_25_11, case_49_25_11_checked⟩

    · exact ⟨Witness.linear .positive case_49_25_12, case_49_25_12_checked⟩

    · exact ⟨Witness.linear .positive case_49_25_13, case_49_25_13_checked⟩

    · exact ⟨Witness.linear .conditional case_49_25_14, case_49_25_14_checked⟩

    · exact ⟨Witness.linear .conditional case_49_25_15, case_49_25_15_checked⟩

    · exact ⟨Witness.linear .conditional case_49_25_16, case_49_25_16_checked⟩

  · have hkHi : k ≤ 16 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_49_26_1_checked⟩

    · exact ⟨Witness.rising, case_49_26_2_checked⟩

    · exact ⟨Witness.rising, case_49_26_3_checked⟩

    · exact ⟨Witness.rising, case_49_26_4_checked⟩

    · exact ⟨Witness.rising, case_49_26_5_checked⟩

    · exact ⟨Witness.rising, case_49_26_6_checked⟩

    · exact ⟨Witness.rising, case_49_26_7_checked⟩

    · exact ⟨Witness.rising, case_49_26_8_checked⟩

    · exact ⟨Witness.rising, case_49_26_9_checked⟩

    · exact ⟨Witness.linear .positive case_49_26_10, case_49_26_10_checked⟩

    · exact ⟨Witness.linear .positive case_49_26_11, case_49_26_11_checked⟩

    · exact ⟨Witness.linear .positive case_49_26_12, case_49_26_12_checked⟩

    · exact ⟨Witness.linear .positive case_49_26_13, case_49_26_13_checked⟩

    · exact ⟨Witness.linear .conditional case_49_26_14, case_49_26_14_checked⟩

    · exact ⟨Witness.linear .conditional case_49_26_15, case_49_26_15_checked⟩

    · exact ⟨Witness.linear .conditional case_49_26_16, case_49_26_16_checked⟩

  · have hkHi : k ≤ 17 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_49_27_1_checked⟩

    · exact ⟨Witness.rising, case_49_27_2_checked⟩

    · exact ⟨Witness.rising, case_49_27_3_checked⟩

    · exact ⟨Witness.rising, case_49_27_4_checked⟩

    · exact ⟨Witness.rising, case_49_27_5_checked⟩

    · exact ⟨Witness.rising, case_49_27_6_checked⟩

    · exact ⟨Witness.rising, case_49_27_7_checked⟩

    · exact ⟨Witness.rising, case_49_27_8_checked⟩

    · exact ⟨Witness.rising, case_49_27_9_checked⟩

    · exact ⟨Witness.linear .positive case_49_27_10, case_49_27_10_checked⟩

    · exact ⟨Witness.linear .positive case_49_27_11, case_49_27_11_checked⟩

    · exact ⟨Witness.linear .positive case_49_27_12, case_49_27_12_checked⟩

    · exact ⟨Witness.linear .positive case_49_27_13, case_49_27_13_checked⟩

    · exact ⟨Witness.linear .positive case_49_27_14, case_49_27_14_checked⟩

    · exact ⟨Witness.linear .conditional case_49_27_15, case_49_27_15_checked⟩

    · exact ⟨Witness.linear .conditional case_49_27_16, case_49_27_16_checked⟩

    · exact ⟨Witness.linear .conditional case_49_27_17, case_49_27_17_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_49_28_1_checked⟩

    · exact ⟨Witness.rising, case_49_28_2_checked⟩

    · exact ⟨Witness.rising, case_49_28_3_checked⟩

    · exact ⟨Witness.rising, case_49_28_4_checked⟩

    · exact ⟨Witness.rising, case_49_28_5_checked⟩

    · exact ⟨Witness.rising, case_49_28_6_checked⟩

    · exact ⟨Witness.rising, case_49_28_7_checked⟩

    · exact ⟨Witness.rising, case_49_28_8_checked⟩

    · exact ⟨Witness.rising, case_49_28_9_checked⟩

    · exact ⟨Witness.linear .positive case_49_28_10, case_49_28_10_checked⟩

    · exact ⟨Witness.linear .positive case_49_28_11, case_49_28_11_checked⟩

    · exact ⟨Witness.linear .positive case_49_28_12, case_49_28_12_checked⟩

    · exact ⟨Witness.linear .positive case_49_28_13, case_49_28_13_checked⟩

    · exact ⟨Witness.linear .positive case_49_28_14, case_49_28_14_checked⟩

    · exact ⟨Witness.linear .conditional case_49_28_15, case_49_28_15_checked⟩

    · exact ⟨Witness.linear .conditional case_49_28_16, case_49_28_16_checked⟩

    · exact ⟨Witness.linear .conditional case_49_28_17, case_49_28_17_checked⟩

    · exact ⟨Witness.linear .negative case_49_28_18, case_49_28_18_checked⟩

  · have hkHi : k ≤ 18 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_49_29_1_checked⟩

    · exact ⟨Witness.rising, case_49_29_2_checked⟩

    · exact ⟨Witness.rising, case_49_29_3_checked⟩

    · exact ⟨Witness.rising, case_49_29_4_checked⟩

    · exact ⟨Witness.rising, case_49_29_5_checked⟩

    · exact ⟨Witness.rising, case_49_29_6_checked⟩

    · exact ⟨Witness.rising, case_49_29_7_checked⟩

    · exact ⟨Witness.rising, case_49_29_8_checked⟩

    · exact ⟨Witness.rising, case_49_29_9_checked⟩

    · exact ⟨Witness.linear .positive case_49_29_10, case_49_29_10_checked⟩

    · exact ⟨Witness.linear .positive case_49_29_11, case_49_29_11_checked⟩

    · exact ⟨Witness.linear .positive case_49_29_12, case_49_29_12_checked⟩

    · exact ⟨Witness.linear .positive case_49_29_13, case_49_29_13_checked⟩

    · exact ⟨Witness.linear .positive case_49_29_14, case_49_29_14_checked⟩

    · exact ⟨Witness.linear .conditional case_49_29_15, case_49_29_15_checked⟩

    · exact ⟨Witness.linear .conditional case_49_29_16, case_49_29_16_checked⟩

    · exact ⟨Witness.linear .conditional case_49_29_17, case_49_29_17_checked⟩

    · exact ⟨Witness.linear .negative case_49_29_18, case_49_29_18_checked⟩

  · have hkHi : k ≤ 19 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_49_30_1_checked⟩

    · exact ⟨Witness.rising, case_49_30_2_checked⟩

    · exact ⟨Witness.rising, case_49_30_3_checked⟩

    · exact ⟨Witness.rising, case_49_30_4_checked⟩

    · exact ⟨Witness.rising, case_49_30_5_checked⟩

    · exact ⟨Witness.rising, case_49_30_6_checked⟩

    · exact ⟨Witness.rising, case_49_30_7_checked⟩

    · exact ⟨Witness.rising, case_49_30_8_checked⟩

    · exact ⟨Witness.rising, case_49_30_9_checked⟩

    · exact ⟨Witness.linear .positive case_49_30_10, case_49_30_10_checked⟩

    · exact ⟨Witness.linear .positive case_49_30_11, case_49_30_11_checked⟩

    · exact ⟨Witness.linear .positive case_49_30_12, case_49_30_12_checked⟩

    · exact ⟨Witness.linear .positive case_49_30_13, case_49_30_13_checked⟩

    · exact ⟨Witness.linear .positive case_49_30_14, case_49_30_14_checked⟩

    · exact ⟨Witness.linear .conditional case_49_30_15, case_49_30_15_checked⟩

    · exact ⟨Witness.linear .conditional case_49_30_16, case_49_30_16_checked⟩

    · exact ⟨Witness.linear .conditional case_49_30_17, case_49_30_17_checked⟩

    · exact ⟨Witness.linear .conditional case_49_30_18, case_49_30_18_checked⟩

    · exact ⟨Witness.linear .negative case_49_30_19, case_49_30_19_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_49_31_1_checked⟩

    · exact ⟨Witness.rising, case_49_31_2_checked⟩

    · exact ⟨Witness.rising, case_49_31_3_checked⟩

    · exact ⟨Witness.rising, case_49_31_4_checked⟩

    · exact ⟨Witness.rising, case_49_31_5_checked⟩

    · exact ⟨Witness.rising, case_49_31_6_checked⟩

    · exact ⟨Witness.rising, case_49_31_7_checked⟩

    · exact ⟨Witness.rising, case_49_31_8_checked⟩

    · exact ⟨Witness.rising, case_49_31_9_checked⟩

    · exact ⟨Witness.linear .positive case_49_31_10, case_49_31_10_checked⟩

    · exact ⟨Witness.linear .positive case_49_31_11, case_49_31_11_checked⟩

    · exact ⟨Witness.linear .positive case_49_31_12, case_49_31_12_checked⟩

    · exact ⟨Witness.linear .positive case_49_31_13, case_49_31_13_checked⟩

    · exact ⟨Witness.linear .conditional case_49_31_14, case_49_31_14_checked⟩

    · exact ⟨Witness.linear .positive case_49_31_15, case_49_31_15_checked⟩

    · exact ⟨Witness.linear .conditional case_49_31_16, case_49_31_16_checked⟩

    · exact ⟨Witness.linear .conditional case_49_31_17, case_49_31_17_checked⟩

    · exact ⟨Witness.linear .conditional case_49_31_18, case_49_31_18_checked⟩

    · exact ⟨Witness.linear .negative case_49_31_19, case_49_31_19_checked⟩

    · exact ⟨Witness.linear .negative case_49_31_20, case_49_31_20_checked⟩

  · have hkHi : k ≤ 20 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_49_32_1_checked⟩

    · exact ⟨Witness.rising, case_49_32_2_checked⟩

    · exact ⟨Witness.rising, case_49_32_3_checked⟩

    · exact ⟨Witness.rising, case_49_32_4_checked⟩

    · exact ⟨Witness.rising, case_49_32_5_checked⟩

    · exact ⟨Witness.rising, case_49_32_6_checked⟩

    · exact ⟨Witness.rising, case_49_32_7_checked⟩

    · exact ⟨Witness.rising, case_49_32_8_checked⟩

    · exact ⟨Witness.rising, case_49_32_9_checked⟩

    · exact ⟨Witness.linear .positive case_49_32_10, case_49_32_10_checked⟩

    · exact ⟨Witness.linear .positive case_49_32_11, case_49_32_11_checked⟩

    · exact ⟨Witness.linear .positive case_49_32_12, case_49_32_12_checked⟩

    · exact ⟨Witness.linear .positive case_49_32_13, case_49_32_13_checked⟩

    · exact ⟨Witness.linear .positive case_49_32_14, case_49_32_14_checked⟩

    · exact ⟨Witness.linear .positive case_49_32_15, case_49_32_15_checked⟩

    · exact ⟨Witness.linear .conditional case_49_32_16, case_49_32_16_checked⟩

    · exact ⟨Witness.linear .conditional case_49_32_17, case_49_32_17_checked⟩

    · exact ⟨Witness.linear .conditional case_49_32_18, case_49_32_18_checked⟩

    · exact ⟨Witness.linear .negative case_49_32_19, case_49_32_19_checked⟩

    · exact ⟨Witness.linear .negative case_49_32_20, case_49_32_20_checked⟩

  · have hkHi : k ≤ 21 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_49_33_1_checked⟩

    · exact ⟨Witness.rising, case_49_33_2_checked⟩

    · exact ⟨Witness.rising, case_49_33_3_checked⟩

    · exact ⟨Witness.rising, case_49_33_4_checked⟩

    · exact ⟨Witness.rising, case_49_33_5_checked⟩

    · exact ⟨Witness.rising, case_49_33_6_checked⟩

    · exact ⟨Witness.rising, case_49_33_7_checked⟩

    · exact ⟨Witness.rising, case_49_33_8_checked⟩

    · exact ⟨Witness.rising, case_49_33_9_checked⟩

    · exact ⟨Witness.linear .positive case_49_33_10, case_49_33_10_checked⟩

    · exact ⟨Witness.linear .positive case_49_33_11, case_49_33_11_checked⟩

    · exact ⟨Witness.linear .positive case_49_33_12, case_49_33_12_checked⟩

    · exact ⟨Witness.linear .positive case_49_33_13, case_49_33_13_checked⟩

    · exact ⟨Witness.linear .positive case_49_33_14, case_49_33_14_checked⟩

    · exact ⟨Witness.linear .positive case_49_33_15, case_49_33_15_checked⟩

    · exact ⟨Witness.linear .conditional case_49_33_16, case_49_33_16_checked⟩

    · exact ⟨Witness.linear .conditional case_49_33_17, case_49_33_17_checked⟩

    · exact ⟨Witness.linear .conditional case_49_33_18, case_49_33_18_checked⟩

    · exact ⟨Witness.linear .conditional case_49_33_19, case_49_33_19_checked⟩

    · exact ⟨Witness.linear .negative case_49_33_20, case_49_33_20_checked⟩

    · exact ⟨Witness.linear .conditional case_49_33_21, case_49_33_21_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_49_34_1_checked⟩

    · exact ⟨Witness.rising, case_49_34_2_checked⟩

    · exact ⟨Witness.rising, case_49_34_3_checked⟩

    · exact ⟨Witness.rising, case_49_34_4_checked⟩

    · exact ⟨Witness.rising, case_49_34_5_checked⟩

    · exact ⟨Witness.rising, case_49_34_6_checked⟩

    · exact ⟨Witness.rising, case_49_34_7_checked⟩

    · exact ⟨Witness.rising, case_49_34_8_checked⟩

    · exact ⟨Witness.rising, case_49_34_9_checked⟩

    · exact ⟨Witness.linear .positive case_49_34_10, case_49_34_10_checked⟩

    · exact ⟨Witness.linear .positive case_49_34_11, case_49_34_11_checked⟩

    · exact ⟨Witness.linear .positive case_49_34_12, case_49_34_12_checked⟩

    · exact ⟨Witness.linear .positive case_49_34_13, case_49_34_13_checked⟩

    · exact ⟨Witness.linear .positive case_49_34_14, case_49_34_14_checked⟩

    · exact ⟨Witness.linear .positive case_49_34_15, case_49_34_15_checked⟩

    · exact ⟨Witness.linear .conditional case_49_34_16, case_49_34_16_checked⟩

    · exact ⟨Witness.linear .conditional case_49_34_17, case_49_34_17_checked⟩

    · exact ⟨Witness.linear .conditional case_49_34_18, case_49_34_18_checked⟩

    · exact ⟨Witness.linear .conditional case_49_34_19, case_49_34_19_checked⟩

    · exact ⟨Witness.linear .negative case_49_34_20, case_49_34_20_checked⟩

    · exact ⟨Witness.linear .conditional case_49_34_21, case_49_34_21_checked⟩

    · exact ⟨Witness.linear .negative case_49_34_22, case_49_34_22_checked⟩

  · have hkHi : k ≤ 22 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_49_35_1_checked⟩

    · exact ⟨Witness.rising, case_49_35_2_checked⟩

    · exact ⟨Witness.rising, case_49_35_3_checked⟩

    · exact ⟨Witness.rising, case_49_35_4_checked⟩

    · exact ⟨Witness.rising, case_49_35_5_checked⟩

    · exact ⟨Witness.rising, case_49_35_6_checked⟩

    · exact ⟨Witness.rising, case_49_35_7_checked⟩

    · exact ⟨Witness.rising, case_49_35_8_checked⟩

    · exact ⟨Witness.rising, case_49_35_9_checked⟩

    · exact ⟨Witness.linear .positive case_49_35_10, case_49_35_10_checked⟩

    · exact ⟨Witness.linear .positive case_49_35_11, case_49_35_11_checked⟩

    · exact ⟨Witness.linear .positive case_49_35_12, case_49_35_12_checked⟩

    · exact ⟨Witness.linear .positive case_49_35_13, case_49_35_13_checked⟩

    · exact ⟨Witness.linear .positive case_49_35_14, case_49_35_14_checked⟩

    · exact ⟨Witness.linear .positive case_49_35_15, case_49_35_15_checked⟩

    · exact ⟨Witness.linear .positive case_49_35_16, case_49_35_16_checked⟩

    · exact ⟨Witness.linear .conditional case_49_35_17, case_49_35_17_checked⟩

    · exact ⟨Witness.linear .conditional case_49_35_18, case_49_35_18_checked⟩

    · exact ⟨Witness.linear .conditional case_49_35_19, case_49_35_19_checked⟩

    · exact ⟨Witness.linear .negative case_49_35_20, case_49_35_20_checked⟩

    · exact ⟨Witness.linear .conditional case_49_35_21, case_49_35_21_checked⟩

    · exact ⟨Witness.linear .negative case_49_35_22, case_49_35_22_checked⟩

  · have hkHi : k ≤ 23 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_49_36_1_checked⟩

    · exact ⟨Witness.rising, case_49_36_2_checked⟩

    · exact ⟨Witness.rising, case_49_36_3_checked⟩

    · exact ⟨Witness.rising, case_49_36_4_checked⟩

    · exact ⟨Witness.rising, case_49_36_5_checked⟩

    · exact ⟨Witness.rising, case_49_36_6_checked⟩

    · exact ⟨Witness.rising, case_49_36_7_checked⟩

    · exact ⟨Witness.rising, case_49_36_8_checked⟩

    · exact ⟨Witness.rising, case_49_36_9_checked⟩

    · exact ⟨Witness.linear .positive case_49_36_10, case_49_36_10_checked⟩

    · exact ⟨Witness.linear .positive case_49_36_11, case_49_36_11_checked⟩

    · exact ⟨Witness.linear .positive case_49_36_12, case_49_36_12_checked⟩

    · exact ⟨Witness.linear .positive case_49_36_13, case_49_36_13_checked⟩

    · exact ⟨Witness.linear .positive case_49_36_14, case_49_36_14_checked⟩

    · exact ⟨Witness.linear .positive case_49_36_15, case_49_36_15_checked⟩

    · exact ⟨Witness.linear .positive case_49_36_16, case_49_36_16_checked⟩

    · exact ⟨Witness.linear .positive case_49_36_17, case_49_36_17_checked⟩

    · exact ⟨Witness.linear .conditional case_49_36_18, case_49_36_18_checked⟩

    · exact ⟨Witness.linear .conditional case_49_36_19, case_49_36_19_checked⟩

    · exact ⟨Witness.linear .negative case_49_36_20, case_49_36_20_checked⟩

    · exact ⟨Witness.linear .conditional case_49_36_21, case_49_36_21_checked⟩

    · exact ⟨Witness.linear .negative case_49_36_22, case_49_36_22_checked⟩

    · exact ⟨Witness.linear .negative case_49_36_23, case_49_36_23_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_49_37_1_checked⟩

    · exact ⟨Witness.rising, case_49_37_2_checked⟩

    · exact ⟨Witness.rising, case_49_37_3_checked⟩

    · exact ⟨Witness.rising, case_49_37_4_checked⟩

    · exact ⟨Witness.rising, case_49_37_5_checked⟩

    · exact ⟨Witness.rising, case_49_37_6_checked⟩

    · exact ⟨Witness.rising, case_49_37_7_checked⟩

    · exact ⟨Witness.rising, case_49_37_8_checked⟩

    · exact ⟨Witness.rising, case_49_37_9_checked⟩

    · exact ⟨Witness.linear .positive case_49_37_10, case_49_37_10_checked⟩

    · exact ⟨Witness.linear .positive case_49_37_11, case_49_37_11_checked⟩

    · exact ⟨Witness.linear .positive case_49_37_12, case_49_37_12_checked⟩

    · exact ⟨Witness.linear .positive case_49_37_13, case_49_37_13_checked⟩

    · exact ⟨Witness.linear .positive case_49_37_14, case_49_37_14_checked⟩

    · exact ⟨Witness.linear .positive case_49_37_15, case_49_37_15_checked⟩

    · exact ⟨Witness.linear .positive case_49_37_16, case_49_37_16_checked⟩

    · exact ⟨Witness.linear .positive case_49_37_17, case_49_37_17_checked⟩

    · exact ⟨Witness.linear .conditional case_49_37_18, case_49_37_18_checked⟩

    · exact ⟨Witness.linear .conditional case_49_37_19, case_49_37_19_checked⟩

    · exact ⟨Witness.linear .conditional case_49_37_20, case_49_37_20_checked⟩

    · exact ⟨Witness.linear .conditional case_49_37_21, case_49_37_21_checked⟩

    · exact ⟨Witness.linear .negative case_49_37_22, case_49_37_22_checked⟩

    · exact ⟨Witness.linear .negative case_49_37_23, case_49_37_23_checked⟩

    · exact ⟨Witness.linear .negative case_49_37_24, case_49_37_24_checked⟩

  · have hkHi : k ≤ 24 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_49_38_1_checked⟩

    · exact ⟨Witness.rising, case_49_38_2_checked⟩

    · exact ⟨Witness.rising, case_49_38_3_checked⟩

    · exact ⟨Witness.rising, case_49_38_4_checked⟩

    · exact ⟨Witness.rising, case_49_38_5_checked⟩

    · exact ⟨Witness.rising, case_49_38_6_checked⟩

    · exact ⟨Witness.rising, case_49_38_7_checked⟩

    · exact ⟨Witness.rising, case_49_38_8_checked⟩

    · exact ⟨Witness.rising, case_49_38_9_checked⟩

    · exact ⟨Witness.linear .positive case_49_38_10, case_49_38_10_checked⟩

    · exact ⟨Witness.linear .positive case_49_38_11, case_49_38_11_checked⟩

    · exact ⟨Witness.linear .positive case_49_38_12, case_49_38_12_checked⟩

    · exact ⟨Witness.linear .positive case_49_38_13, case_49_38_13_checked⟩

    · exact ⟨Witness.linear .positive case_49_38_14, case_49_38_14_checked⟩

    · exact ⟨Witness.linear .positive case_49_38_15, case_49_38_15_checked⟩

    · exact ⟨Witness.linear .positive case_49_38_16, case_49_38_16_checked⟩

    · exact ⟨Witness.linear .positive case_49_38_17, case_49_38_17_checked⟩

    · exact ⟨Witness.linear .positive case_49_38_18, case_49_38_18_checked⟩

    · exact ⟨Witness.linear .conditional case_49_38_19, case_49_38_19_checked⟩

    · exact ⟨Witness.linear .conditional case_49_38_20, case_49_38_20_checked⟩

    · exact ⟨Witness.linear .conditional case_49_38_21, case_49_38_21_checked⟩

    · exact ⟨Witness.linear .negative case_49_38_22, case_49_38_22_checked⟩

    · exact ⟨Witness.linear .negative case_49_38_23, case_49_38_23_checked⟩

    · exact ⟨Witness.linear .negative case_49_38_24, case_49_38_24_checked⟩

  · have hkHi : k ≤ 25 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_49_39_1_checked⟩

    · exact ⟨Witness.rising, case_49_39_2_checked⟩

    · exact ⟨Witness.rising, case_49_39_3_checked⟩

    · exact ⟨Witness.rising, case_49_39_4_checked⟩

    · exact ⟨Witness.rising, case_49_39_5_checked⟩

    · exact ⟨Witness.rising, case_49_39_6_checked⟩

    · exact ⟨Witness.rising, case_49_39_7_checked⟩

    · exact ⟨Witness.rising, case_49_39_8_checked⟩

    · exact ⟨Witness.rising, case_49_39_9_checked⟩

    · exact ⟨Witness.linear .positive case_49_39_10, case_49_39_10_checked⟩

    · exact ⟨Witness.linear .positive case_49_39_11, case_49_39_11_checked⟩

    · exact ⟨Witness.linear .positive case_49_39_12, case_49_39_12_checked⟩

    · exact ⟨Witness.linear .positive case_49_39_13, case_49_39_13_checked⟩

    · exact ⟨Witness.linear .positive case_49_39_14, case_49_39_14_checked⟩

    · exact ⟨Witness.linear .positive case_49_39_15, case_49_39_15_checked⟩

    · exact ⟨Witness.linear .positive case_49_39_16, case_49_39_16_checked⟩

    · exact ⟨Witness.linear .positive case_49_39_17, case_49_39_17_checked⟩

    · exact ⟨Witness.linear .positive case_49_39_18, case_49_39_18_checked⟩

    · exact ⟨Witness.linear .positive case_49_39_19, case_49_39_19_checked⟩

    · exact ⟨Witness.linear .conditional case_49_39_20, case_49_39_20_checked⟩

    · exact ⟨Witness.linear .conditional case_49_39_21, case_49_39_21_checked⟩

    · exact ⟨Witness.linear .negative case_49_39_22, case_49_39_22_checked⟩

    · exact ⟨Witness.linear .negative case_49_39_23, case_49_39_23_checked⟩

    · exact ⟨Witness.linear .negative case_49_39_24, case_49_39_24_checked⟩

    · exact ⟨Witness.linear .negative case_49_39_25, case_49_39_25_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_49_40_1_checked⟩

    · exact ⟨Witness.rising, case_49_40_2_checked⟩

    · exact ⟨Witness.rising, case_49_40_3_checked⟩

    · exact ⟨Witness.rising, case_49_40_4_checked⟩

    · exact ⟨Witness.rising, case_49_40_5_checked⟩

    · exact ⟨Witness.rising, case_49_40_6_checked⟩

    · exact ⟨Witness.rising, case_49_40_7_checked⟩

    · exact ⟨Witness.rising, case_49_40_8_checked⟩

    · exact ⟨Witness.linear .positive case_49_40_9, case_49_40_9_checked⟩

    · exact ⟨Witness.linear .positive case_49_40_10, case_49_40_10_checked⟩

    · exact ⟨Witness.linear .positive case_49_40_11, case_49_40_11_checked⟩

    · exact ⟨Witness.linear .positive case_49_40_12, case_49_40_12_checked⟩

    · exact ⟨Witness.linear .positive case_49_40_13, case_49_40_13_checked⟩

    · exact ⟨Witness.linear .positive case_49_40_14, case_49_40_14_checked⟩

    · exact ⟨Witness.linear .positive case_49_40_15, case_49_40_15_checked⟩

    · exact ⟨Witness.linear .positive case_49_40_16, case_49_40_16_checked⟩

    · exact ⟨Witness.linear .positive case_49_40_17, case_49_40_17_checked⟩

    · exact ⟨Witness.linear .positive case_49_40_18, case_49_40_18_checked⟩

    · exact ⟨Witness.linear .positive case_49_40_19, case_49_40_19_checked⟩

    · exact ⟨Witness.linear .conditional case_49_40_20, case_49_40_20_checked⟩

    · exact ⟨Witness.linear .conditional case_49_40_21, case_49_40_21_checked⟩

    · exact ⟨Witness.linear .negative case_49_40_22, case_49_40_22_checked⟩

    · exact ⟨Witness.linear .negative case_49_40_23, case_49_40_23_checked⟩

    · exact ⟨Witness.linear .negative case_49_40_24, case_49_40_24_checked⟩

    · exact ⟨Witness.linear .negative case_49_40_25, case_49_40_25_checked⟩

    · exact ⟨Witness.linear .negative case_49_40_26, case_49_40_26_checked⟩

  · have hkHi : k ≤ 26 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_49_41_1_checked⟩

    · exact ⟨Witness.rising, case_49_41_2_checked⟩

    · exact ⟨Witness.rising, case_49_41_3_checked⟩

    · exact ⟨Witness.rising, case_49_41_4_checked⟩

    · exact ⟨Witness.rising, case_49_41_5_checked⟩

    · exact ⟨Witness.rising, case_49_41_6_checked⟩

    · exact ⟨Witness.rising, case_49_41_7_checked⟩

    · exact ⟨Witness.rising, case_49_41_8_checked⟩

    · exact ⟨Witness.linear .positive case_49_41_9, case_49_41_9_checked⟩

    · exact ⟨Witness.linear .positive case_49_41_10, case_49_41_10_checked⟩

    · exact ⟨Witness.linear .positive case_49_41_11, case_49_41_11_checked⟩

    · exact ⟨Witness.linear .positive case_49_41_12, case_49_41_12_checked⟩

    · exact ⟨Witness.linear .positive case_49_41_13, case_49_41_13_checked⟩

    · exact ⟨Witness.linear .positive case_49_41_14, case_49_41_14_checked⟩

    · exact ⟨Witness.linear .positive case_49_41_15, case_49_41_15_checked⟩

    · exact ⟨Witness.linear .positive case_49_41_16, case_49_41_16_checked⟩

    · exact ⟨Witness.linear .positive case_49_41_17, case_49_41_17_checked⟩

    · exact ⟨Witness.linear .positive case_49_41_18, case_49_41_18_checked⟩

    · exact ⟨Witness.linear .positive case_49_41_19, case_49_41_19_checked⟩

    · exact ⟨Witness.linear .positive case_49_41_20, case_49_41_20_checked⟩

    · exact ⟨Witness.linear .conditional case_49_41_21, case_49_41_21_checked⟩

    · exact ⟨Witness.linear .conditional case_49_41_22, case_49_41_22_checked⟩

    · exact ⟨Witness.linear .negative case_49_41_23, case_49_41_23_checked⟩

    · exact ⟨Witness.linear .negative case_49_41_24, case_49_41_24_checked⟩

    · exact ⟨Witness.linear .negative case_49_41_25, case_49_41_25_checked⟩

    · exact ⟨Witness.linear .negative case_49_41_26, case_49_41_26_checked⟩

  · have hkHi : k ≤ 27 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_49_42_1_checked⟩

    · exact ⟨Witness.rising, case_49_42_2_checked⟩

    · exact ⟨Witness.rising, case_49_42_3_checked⟩

    · exact ⟨Witness.rising, case_49_42_4_checked⟩

    · exact ⟨Witness.rising, case_49_42_5_checked⟩

    · exact ⟨Witness.rising, case_49_42_6_checked⟩

    · exact ⟨Witness.rising, case_49_42_7_checked⟩

    · exact ⟨Witness.rising, case_49_42_8_checked⟩

    · exact ⟨Witness.linear .positive case_49_42_9, case_49_42_9_checked⟩

    · exact ⟨Witness.linear .positive case_49_42_10, case_49_42_10_checked⟩

    · exact ⟨Witness.linear .positive case_49_42_11, case_49_42_11_checked⟩

    · exact ⟨Witness.linear .positive case_49_42_12, case_49_42_12_checked⟩

    · exact ⟨Witness.linear .positive case_49_42_13, case_49_42_13_checked⟩

    · exact ⟨Witness.linear .positive case_49_42_14, case_49_42_14_checked⟩

    · exact ⟨Witness.linear .positive case_49_42_15, case_49_42_15_checked⟩

    · exact ⟨Witness.linear .positive case_49_42_16, case_49_42_16_checked⟩

    · exact ⟨Witness.linear .positive case_49_42_17, case_49_42_17_checked⟩

    · exact ⟨Witness.linear .positive case_49_42_18, case_49_42_18_checked⟩

    · exact ⟨Witness.linear .positive case_49_42_19, case_49_42_19_checked⟩

    · exact ⟨Witness.linear .positive case_49_42_20, case_49_42_20_checked⟩

    · exact ⟨Witness.linear .conditional case_49_42_21, case_49_42_21_checked⟩

    · exact ⟨Witness.linear .conditional case_49_42_22, case_49_42_22_checked⟩

    · exact ⟨Witness.linear .negative case_49_42_23, case_49_42_23_checked⟩

    · exact ⟨Witness.linear .negative case_49_42_24, case_49_42_24_checked⟩

    · exact ⟨Witness.linear .negative case_49_42_25, case_49_42_25_checked⟩

    · exact ⟨Witness.linear .negative case_49_42_26, case_49_42_26_checked⟩

    · exact ⟨Witness.linear .negative case_49_42_27, case_49_42_27_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_49_43_1_checked⟩

    · exact ⟨Witness.rising, case_49_43_2_checked⟩

    · exact ⟨Witness.rising, case_49_43_3_checked⟩

    · exact ⟨Witness.rising, case_49_43_4_checked⟩

    · exact ⟨Witness.rising, case_49_43_5_checked⟩

    · exact ⟨Witness.rising, case_49_43_6_checked⟩

    · exact ⟨Witness.rising, case_49_43_7_checked⟩

    · exact ⟨Witness.rising, case_49_43_8_checked⟩

    · exact ⟨Witness.linear .positive case_49_43_9, case_49_43_9_checked⟩

    · exact ⟨Witness.linear .positive case_49_43_10, case_49_43_10_checked⟩

    · exact ⟨Witness.linear .positive case_49_43_11, case_49_43_11_checked⟩

    · exact ⟨Witness.linear .positive case_49_43_12, case_49_43_12_checked⟩

    · exact ⟨Witness.linear .positive case_49_43_13, case_49_43_13_checked⟩

    · exact ⟨Witness.linear .positive case_49_43_14, case_49_43_14_checked⟩

    · exact ⟨Witness.linear .positive case_49_43_15, case_49_43_15_checked⟩

    · exact ⟨Witness.linear .positive case_49_43_16, case_49_43_16_checked⟩

    · exact ⟨Witness.linear .positive case_49_43_17, case_49_43_17_checked⟩

    · exact ⟨Witness.linear .positive case_49_43_18, case_49_43_18_checked⟩

    · exact ⟨Witness.linear .positive case_49_43_19, case_49_43_19_checked⟩

    · exact ⟨Witness.linear .positive case_49_43_20, case_49_43_20_checked⟩

    · exact ⟨Witness.linear .positive case_49_43_21, case_49_43_21_checked⟩

    · exact ⟨Witness.linear .conditional case_49_43_22, case_49_43_22_checked⟩

    · exact ⟨Witness.linear .negative case_49_43_23, case_49_43_23_checked⟩

    · exact ⟨Witness.linear .negative case_49_43_24, case_49_43_24_checked⟩

    · exact ⟨Witness.linear .negative case_49_43_25, case_49_43_25_checked⟩

    · exact ⟨Witness.linear .negative case_49_43_26, case_49_43_26_checked⟩

    · exact ⟨Witness.linear .negative case_49_43_27, case_49_43_27_checked⟩

    · exact ⟨Witness.linear .negative case_49_43_28, case_49_43_28_checked⟩

  · have hkHi : k ≤ 28 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_49_44_1_checked⟩

    · exact ⟨Witness.rising, case_49_44_2_checked⟩

    · exact ⟨Witness.rising, case_49_44_3_checked⟩

    · exact ⟨Witness.rising, case_49_44_4_checked⟩

    · exact ⟨Witness.rising, case_49_44_5_checked⟩

    · exact ⟨Witness.rising, case_49_44_6_checked⟩

    · exact ⟨Witness.rising, case_49_44_7_checked⟩

    · exact ⟨Witness.rising, case_49_44_8_checked⟩

    · exact ⟨Witness.linear .positive case_49_44_9, case_49_44_9_checked⟩

    · exact ⟨Witness.linear .positive case_49_44_10, case_49_44_10_checked⟩

    · exact ⟨Witness.linear .positive case_49_44_11, case_49_44_11_checked⟩

    · exact ⟨Witness.linear .positive case_49_44_12, case_49_44_12_checked⟩

    · exact ⟨Witness.linear .positive case_49_44_13, case_49_44_13_checked⟩

    · exact ⟨Witness.linear .positive case_49_44_14, case_49_44_14_checked⟩

    · exact ⟨Witness.linear .positive case_49_44_15, case_49_44_15_checked⟩

    · exact ⟨Witness.linear .positive case_49_44_16, case_49_44_16_checked⟩

    · exact ⟨Witness.linear .positive case_49_44_17, case_49_44_17_checked⟩

    · exact ⟨Witness.linear .positive case_49_44_18, case_49_44_18_checked⟩

    · exact ⟨Witness.linear .positive case_49_44_19, case_49_44_19_checked⟩

    · exact ⟨Witness.linear .positive case_49_44_20, case_49_44_20_checked⟩

    · exact ⟨Witness.linear .positive case_49_44_21, case_49_44_21_checked⟩

    · exact ⟨Witness.linear .positive case_49_44_22, case_49_44_22_checked⟩

    · exact ⟨Witness.linear .negative case_49_44_23, case_49_44_23_checked⟩

    · exact ⟨Witness.linear .negative case_49_44_24, case_49_44_24_checked⟩

    · exact ⟨Witness.linear .negative case_49_44_25, case_49_44_25_checked⟩

    · exact ⟨Witness.linear .negative case_49_44_26, case_49_44_26_checked⟩

    · exact ⟨Witness.linear .negative case_49_44_27, case_49_44_27_checked⟩

    · exact ⟨Witness.linear .negative case_49_44_28, case_49_44_28_checked⟩

  · have hkHi : k ≤ 29 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_49_45_1_checked⟩

    · exact ⟨Witness.rising, case_49_45_2_checked⟩

    · exact ⟨Witness.rising, case_49_45_3_checked⟩

    · exact ⟨Witness.rising, case_49_45_4_checked⟩

    · exact ⟨Witness.rising, case_49_45_5_checked⟩

    · exact ⟨Witness.rising, case_49_45_6_checked⟩

    · exact ⟨Witness.rising, case_49_45_7_checked⟩

    · exact ⟨Witness.rising, case_49_45_8_checked⟩

    · exact ⟨Witness.linear .positive case_49_45_9, case_49_45_9_checked⟩

    · exact ⟨Witness.linear .positive case_49_45_10, case_49_45_10_checked⟩

    · exact ⟨Witness.linear .positive case_49_45_11, case_49_45_11_checked⟩

    · exact ⟨Witness.linear .positive case_49_45_12, case_49_45_12_checked⟩

    · exact ⟨Witness.linear .positive case_49_45_13, case_49_45_13_checked⟩

    · exact ⟨Witness.linear .positive case_49_45_14, case_49_45_14_checked⟩

    · exact ⟨Witness.linear .positive case_49_45_15, case_49_45_15_checked⟩

    · exact ⟨Witness.linear .positive case_49_45_16, case_49_45_16_checked⟩

    · exact ⟨Witness.linear .positive case_49_45_17, case_49_45_17_checked⟩

    · exact ⟨Witness.linear .positive case_49_45_18, case_49_45_18_checked⟩

    · exact ⟨Witness.linear .positive case_49_45_19, case_49_45_19_checked⟩

    · exact ⟨Witness.linear .positive case_49_45_20, case_49_45_20_checked⟩

    · exact ⟨Witness.linear .positive case_49_45_21, case_49_45_21_checked⟩

    · exact ⟨Witness.linear .positive case_49_45_22, case_49_45_22_checked⟩

    · exact ⟨Witness.linear .negative case_49_45_23, case_49_45_23_checked⟩

    · exact ⟨Witness.linear .negative case_49_45_24, case_49_45_24_checked⟩

    · exact ⟨Witness.linear .negative case_49_45_25, case_49_45_25_checked⟩

    · exact ⟨Witness.linear .negative case_49_45_26, case_49_45_26_checked⟩

    · exact ⟨Witness.linear .negative case_49_45_27, case_49_45_27_checked⟩

    · exact ⟨Witness.linear .negative case_49_45_28, case_49_45_28_checked⟩

    · exact ⟨Witness.linear .negative case_49_45_29, case_49_45_29_checked⟩

  · have hkHi : k ≤ 30 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_49_46_1_checked⟩

    · exact ⟨Witness.rising, case_49_46_2_checked⟩

    · exact ⟨Witness.rising, case_49_46_3_checked⟩

    · exact ⟨Witness.rising, case_49_46_4_checked⟩

    · exact ⟨Witness.rising, case_49_46_5_checked⟩

    · exact ⟨Witness.rising, case_49_46_6_checked⟩

    · exact ⟨Witness.rising, case_49_46_7_checked⟩

    · exact ⟨Witness.rising, case_49_46_8_checked⟩

    · exact ⟨Witness.linear .positive case_49_46_9, case_49_46_9_checked⟩

    · exact ⟨Witness.linear .positive case_49_46_10, case_49_46_10_checked⟩

    · exact ⟨Witness.linear .positive case_49_46_11, case_49_46_11_checked⟩

    · exact ⟨Witness.linear .positive case_49_46_12, case_49_46_12_checked⟩

    · exact ⟨Witness.linear .positive case_49_46_13, case_49_46_13_checked⟩

    · exact ⟨Witness.linear .positive case_49_46_14, case_49_46_14_checked⟩

    · exact ⟨Witness.linear .positive case_49_46_15, case_49_46_15_checked⟩

    · exact ⟨Witness.linear .positive case_49_46_16, case_49_46_16_checked⟩

    · exact ⟨Witness.linear .positive case_49_46_17, case_49_46_17_checked⟩

    · exact ⟨Witness.linear .positive case_49_46_18, case_49_46_18_checked⟩

    · exact ⟨Witness.linear .positive case_49_46_19, case_49_46_19_checked⟩

    · exact ⟨Witness.linear .positive case_49_46_20, case_49_46_20_checked⟩

    · exact ⟨Witness.linear .positive case_49_46_21, case_49_46_21_checked⟩

    · exact ⟨Witness.linear .positive case_49_46_22, case_49_46_22_checked⟩

    · exact ⟨Witness.linear .positive case_49_46_23, case_49_46_23_checked⟩

    · exact ⟨Witness.linear .negative case_49_46_24, case_49_46_24_checked⟩

    · exact ⟨Witness.linear .negative case_49_46_25, case_49_46_25_checked⟩

    · exact ⟨Witness.linear .negative case_49_46_26, case_49_46_26_checked⟩

    · exact ⟨Witness.linear .negative case_49_46_27, case_49_46_27_checked⟩

    · exact ⟨Witness.linear .negative case_49_46_28, case_49_46_28_checked⟩

    · exact ⟨Witness.linear .negative case_49_46_29, case_49_46_29_checked⟩

    · exact ⟨Witness.linear .negative case_49_46_30, case_49_46_30_checked⟩

  · have hkHi : k ≤ 30 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_49_47_1_checked⟩

    · exact ⟨Witness.rising, case_49_47_2_checked⟩

    · exact ⟨Witness.rising, case_49_47_3_checked⟩

    · exact ⟨Witness.rising, case_49_47_4_checked⟩

    · exact ⟨Witness.rising, case_49_47_5_checked⟩

    · exact ⟨Witness.rising, case_49_47_6_checked⟩

    · exact ⟨Witness.rising, case_49_47_7_checked⟩

    · exact ⟨Witness.rising, case_49_47_8_checked⟩

    · exact ⟨Witness.linear .positive case_49_47_9, case_49_47_9_checked⟩

    · exact ⟨Witness.linear .positive case_49_47_10, case_49_47_10_checked⟩

    · exact ⟨Witness.linear .positive case_49_47_11, case_49_47_11_checked⟩

    · exact ⟨Witness.linear .positive case_49_47_12, case_49_47_12_checked⟩

    · exact ⟨Witness.linear .positive case_49_47_13, case_49_47_13_checked⟩

    · exact ⟨Witness.linear .positive case_49_47_14, case_49_47_14_checked⟩

    · exact ⟨Witness.linear .positive case_49_47_15, case_49_47_15_checked⟩

    · exact ⟨Witness.linear .positive case_49_47_16, case_49_47_16_checked⟩

    · exact ⟨Witness.linear .positive case_49_47_17, case_49_47_17_checked⟩

    · exact ⟨Witness.linear .positive case_49_47_18, case_49_47_18_checked⟩

    · exact ⟨Witness.linear .positive case_49_47_19, case_49_47_19_checked⟩

    · exact ⟨Witness.linear .positive case_49_47_20, case_49_47_20_checked⟩

    · exact ⟨Witness.linear .positive case_49_47_21, case_49_47_21_checked⟩

    · exact ⟨Witness.linear .positive case_49_47_22, case_49_47_22_checked⟩

    · exact ⟨Witness.linear .positive case_49_47_23, case_49_47_23_checked⟩

    · exact ⟨Witness.linear .negative case_49_47_24, case_49_47_24_checked⟩

    · exact ⟨Witness.linear .negative case_49_47_25, case_49_47_25_checked⟩

    · exact ⟨Witness.linear .negative case_49_47_26, case_49_47_26_checked⟩

    · exact ⟨Witness.linear .negative case_49_47_27, case_49_47_27_checked⟩

    · exact ⟨Witness.linear .negative case_49_47_28, case_49_47_28_checked⟩

    · exact ⟨Witness.linear .negative case_49_47_29, case_49_47_29_checked⟩

    · exact ⟨Witness.linear .negative case_49_47_30, case_49_47_30_checked⟩

  · have hkHi : k ≤ 31 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_49_48_1_checked⟩

    · exact ⟨Witness.rising, case_49_48_2_checked⟩

    · exact ⟨Witness.rising, case_49_48_3_checked⟩

    · exact ⟨Witness.rising, case_49_48_4_checked⟩

    · exact ⟨Witness.rising, case_49_48_5_checked⟩

    · exact ⟨Witness.rising, case_49_48_6_checked⟩

    · exact ⟨Witness.rising, case_49_48_7_checked⟩

    · exact ⟨Witness.rising, case_49_48_8_checked⟩

    · exact ⟨Witness.linear .positive case_49_48_9, case_49_48_9_checked⟩

    · exact ⟨Witness.linear .positive case_49_48_10, case_49_48_10_checked⟩

    · exact ⟨Witness.linear .positive case_49_48_11, case_49_48_11_checked⟩

    · exact ⟨Witness.linear .positive case_49_48_12, case_49_48_12_checked⟩

    · exact ⟨Witness.linear .positive case_49_48_13, case_49_48_13_checked⟩

    · exact ⟨Witness.linear .positive case_49_48_14, case_49_48_14_checked⟩

    · exact ⟨Witness.linear .positive case_49_48_15, case_49_48_15_checked⟩

    · exact ⟨Witness.linear .positive case_49_48_16, case_49_48_16_checked⟩

    · exact ⟨Witness.linear .positive case_49_48_17, case_49_48_17_checked⟩

    · exact ⟨Witness.linear .positive case_49_48_18, case_49_48_18_checked⟩

    · exact ⟨Witness.linear .positive case_49_48_19, case_49_48_19_checked⟩

    · exact ⟨Witness.linear .positive case_49_48_20, case_49_48_20_checked⟩

    · exact ⟨Witness.linear .positive case_49_48_21, case_49_48_21_checked⟩

    · exact ⟨Witness.linear .positive case_49_48_22, case_49_48_22_checked⟩

    · exact ⟨Witness.linear .positive case_49_48_23, case_49_48_23_checked⟩

    · exact ⟨Witness.linear .positive case_49_48_24, case_49_48_24_checked⟩

    · exact ⟨Witness.linear .negative case_49_48_25, case_49_48_25_checked⟩

    · exact ⟨Witness.linear .negative case_49_48_26, case_49_48_26_checked⟩

    · exact ⟨Witness.linear .negative case_49_48_27, case_49_48_27_checked⟩

    · exact ⟨Witness.linear .negative case_49_48_28, case_49_48_28_checked⟩

    · exact ⟨Witness.linear .negative case_49_48_29, case_49_48_29_checked⟩

    · exact ⟨Witness.linear .negative case_49_48_30, case_49_48_30_checked⟩

    · exact ⟨Witness.linear .negative case_49_48_31, case_49_48_31_checked⟩


#print axioms coverage_49
end ForestUnimodality.FiniteRows.FiniteData
