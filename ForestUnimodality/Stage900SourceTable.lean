import ForestUnimodality.SelectionCertifiedLibrary
import ForestUnimodality.MeanMatchedSourceBudget
import ForestUnimodality.StageDensityBounds
import ForestUnimodality.NonnegativeSourceData.Case01.Complete
import ForestUnimodality.NonnegativeSourceData.Case02.Complete
import ForestUnimodality.NonnegativeSourceData.Case03.Complete
import ForestUnimodality.NonnegativeSourceData.Case04.Complete
import ForestUnimodality.NonnegativeSourceData.Case05.Complete
import ForestUnimodality.NonnegativeSourceData.Case06.Complete
import ForestUnimodality.NonnegativeSourceData.Case07.Complete
import ForestUnimodality.NonnegativeSourceData.Case08.Complete
import ForestUnimodality.NonnegativeSourceData.Case09.Complete
import ForestUnimodality.NonnegativeSourceData.Case10.Complete
import ForestUnimodality.NonnegativeSourceData.Case11.Complete
import ForestUnimodality.NonnegativeSourceData.Case12.Complete
import ForestUnimodality.NonnegativeSourceData.Case13.Complete
import ForestUnimodality.NonnegativeSourceData.Case14.Complete
import ForestUnimodality.NonnegativeSourceData.Case15.Complete
import ForestUnimodality.NonnegativeSourceData.Case16.Complete

/-! Exact frozen stage900 source parameters. All numerical conditions are
kernel-decided rational propositions, while source validity reuses the
complete continuous-domain certificates. Input pass flags are never imported. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.Stage900SourceTable
open SelectionSourceTable

structure Row where
  rho : ℚ
  qa : ℚ
  qb : ℚ
  Cs : ℚ
  D : ℚ
  R : ℚ
  start : ℚ
  CW : ℚ

def row (i : Fin 28) : Row :=
  ![⟨(1/4), (1/4), (1/3), (224166666666666666666666666667/500000000000000000000000000000), (130416666666666666666666666667/31250000000000000000000000000), (3803687/2500000), (675/2), (2101229/1250000)⟩,
    ⟨(1/4), (1/3), (7/17), (761647058823529411764705882353/1000000000000000000000000000000), (4854823529411764705882352941177/1000000000000000000000000000000), (74081147/50000000), (54642857142857142857142857142857/200000000000000000000000000000), (7298891/5000000)⟩,
    ⟨(1/4), (7/17), (4/9), (242138888888888888888888888889/250000000000000000000000000000), (1070982426303854875283446712019/250000000000000000000000000000), (53922541/50000000), (2025/8), (11546949/10000000)⟩,
    ⟨(1/4), (4/9), (17/37), (507040540540540540540540540541/500000000000000000000000000000), (1941892736486486486486486486489/500000000000000000000000000000), (45415711/50000000), (122426470588235294117647058823529/500000000000000000000000000000), (2578803/2500000)⟩,
    ⟨(1/4), (17/37), (22/47), (1084148936170212765957446808511/1000000000000000000000000000000), (1979584591032908783037620555107/500000000000000000000000000000), (211213679/250000000), (240340909090909090909090909090909/1000000000000000000000000000000), (9813057/10000000)⟩,
    ⟨(1/4), (22/47), (9/19), (68865131578947368421052631579/62500000000000000000000000000), (778499673771204871683340582863/200000000000000000000000000000), (5091347/6250000), (475/2), (596913/625000)⟩,
    ⟨(1/4), (9/19), (23/48), (1173/1000), (514587962962962962962962962963/125000000000000000000000000000), (2556421/3125000), (234782608695652173913043478260869/1000000000000000000000000000000), (1893807/2000000)⟩,
    ⟨(1/4), (23/48), (47/97), (1190783505154639175257731958763/1000000000000000000000000000000), (4099367099955177050649932765577/1000000000000000000000000000000), (20561191/25000000), (232180851063829787234042553191489/1000000000000000000000000000000), (469703/500000)⟩,
    ⟨(1/4), (47/97), (24/49), (1208204081632653061224489795919/1000000000000000000000000000000), (2041193346329025045962250903079/500000000000000000000000000000), (25847103/31250000), (3675/16), (1165247/1250000)⟩,
    ⟨(258476333333333333333333333333/1000000000000000000000000000000), (24/49), (49/99), (241660402966772215278525978797/200000000000000000000000000000), (199751140418064274689123643703/50000000000000000000000000000), (415764751/500000000), (58750615561224489795918367346863/250000000000000000000000000000), (9250149/10000000)⟩,
    ⟨(26761748979591836734693877551/100000000000000000000000000000), (49/99), (1/2), (584280444629431116922363376239/500000000000000000000000000000), (1874857408501896866703908142657/500000000000000000000000000000), (4181239/5000000), (240855740816326530612244897959/1000000000000000000000000000), (9181239/10000000)⟩,
    ⟨(276393/1000000), (1/2), (51/101), (46707914548279349540059779279/40000000000000000000000000000), (36707914548279349540059779279/10000000000000000000000000000), (105132843/125000000), (246314938235294117647058823529411/1000000000000000000000000000000), (2278543/2500000)⟩,
    ⟨(138878956002311880886818616659/500000000000000000000000000000), (51/101), (26/51), (1185857738653382095420331007563/1000000000000000000000000000000), (3670486271435275184691578857421/1000000000000000000000000000000), (211530161/250000000), (122587386163579141013557202012463/500000000000000000000000000000), (9049611/10000000)⟩,
    ⟨(279089580929303266684937255733/1000000000000000000000000000000), (26/51), (53/103), (1238910053561610761786078201529/1000000000000000000000000000000), (951333228296505026407392530391/250000000000000000000000000000), (425698183/500000000), (122035868642200060479687186822873/500000000000000000000000000000), (8987361/10000000)⟩,
    ⟨(140194625359166630852074778121/500000000000000000000000000000), (53/103), (107/207), (123874195073347194650531956349/100000000000000000000000000000), (373507061421552291935739951907/100000000000000000000000000000), (817992197/1000000000), (122047937871087585643652014784777/500000000000000000000000000000), (8782571/10000000)⟩,
    ⟨(140513728574749096896883602033/500000000000000000000000000000), (107/207), (27/52), (1242501764868828435496415580047/1000000000000000000000000000000), (92890117309075966531107326381/25000000000000000000000000000), (5131669/6250000), (608892823823912753219828942143/2500000000000000000000000000), (875513/1000000)⟩,
    ⟨(140829050834247263984353734313/500000000000000000000000000000), (27/52), (109/209), (623108811166206589559243723607/500000000000000000000000000000), (924133213575735677755963668473/250000000000000000000000000000), (824198607/1000000000), (121513506706063808969985951487501/500000000000000000000000000000), (8728223/10000000)⟩,
    ⟨(141140661275938093534042176647/500000000000000000000000000000), (109/209), (11/21), (1249890315329405070113876685059/1000000000000000000000000000000), (3677843520234302067809464479427/1000000000000000000000000000000), (16592647/20000000), (121252659005237725808790779028559/500000000000000000000000000000), (1742507/2000000)⟩,
    ⟨(282897254601131014328941419761/1000000000000000000000000000000), (11/21), (111/211), (1291588487682543290909882571039/1000000000000000000000000000000), (3798268785685963564390563750647/1000000000000000000000000000000), (830404533/1000000000), (120995920380078332479878323451833/500000000000000000000000000000), (8674903/10000000)⟩,
    ⟨(283506029255228275314312630391/1000000000000000000000000000000), (111/211), (28/53), (2590572267695958676944983861/2000000000000000000000000000), (1889758703232119476021987388921/500000000000000000000000000000), (52095593/62500000), (48297277126694245473188258820181/200000000000000000000000000000), (2162181/2500000)⟩,
    ⟨(142053887349331640082303101279/500000000000000000000000000000), (28/53), (113/213), (259788326974291535023413590837/200000000000000000000000000000), (752226288865797094235674460027/200000000000000000000000000000), (836654057/1000000000), (48197752574985620183676999141919/200000000000000000000000000000), (8622789/10000000)⟩,
    ⟨(11388104638608594711128320207/40000000000000000000000000000), (113/213), (57/107), (651277865000321419623984422723/500000000000000000000000000000), (1871550274665172095459358546051/500000000000000000000000000000), (419913989/500000000), (15031174296847692854737626589009/62500000000000000000000000000), (8597327/10000000)⟩,
    ⟨(14264533751880970675456561201/50000000000000000000000000000), (57/107), (29/54), (266530687191537196734976170629/200000000000000000000000000000), (3818882483311648761801696179643/1000000000000000000000000000000), (6822499/7812500), (119526955231278478418480840408379/500000000000000000000000000000), (542037/625000)⟩,
    ⟨(286446919846708539653993128729/1000000000000000000000000000000), (29/54), (6/11), (695083010299045722488745746381/500000000000000000000000000000), (158322193391868473415189783253/40000000000000000000000000000), (23473887/25000000), (9452748354941381808581773248057/40000000000000000000000000000), (4406717/5000000)⟩,
    ⟨(288683073375379155524016373733/1000000000000000000000000000000), (6/11), (13/23), (77415373263275590619439781543/50000000000000000000000000000), (1092675022896714786798918550931/250000000000000000000000000000), (14108033/12500000), (4596722783746421937959337643287/20000000000000000000000000000), (1156871/1250000)⟩,
    ⟨(293866307348293569444703934861/1000000000000000000000000000000), (13/23), (3/5), (372485539632115153119862923981/200000000000000000000000000000), (5060498534478962011846375348697/1000000000000000000000000000000), (5693969/4000000), (881598922044880708334111804583/4000000000000000000000000000), (9693969/10000000)⟩,
    ⟨(60554672334610151038684899671/200000000000000000000000000000), (3/5), (9/14), (596698932959198870966271985999/200000000000000000000000000000), (1905204628330551635299555506941/250000000000000000000000000000), (43935559/25000000), (423882706342271057270794297697/2000000000000000000000000000), (9847937/10000000)⟩,
    ⟨(313400203765318023034505606997/1000000000000000000000000000000), (9/14), (9/13), (314118095449098608364675529343/100000000000000000000000000000), (7045326754076953980182272068053/1000000000000000000000000000000), (22914583/10000000), (4074202648949134299448572890961/20000000000000000000000000000), (2531891/2500000)⟩] i

def nonnegative (i : Fin 28) : NonnegativeSource.Parameters :=
  ![NonnegativeSourceData.Case01.parameters,
    NonnegativeSourceData.Case02.parameters,
    NonnegativeSourceData.Case03.parameters,
    NonnegativeSourceData.Case03.parameters,
    NonnegativeSourceData.Case04.parameters,
    NonnegativeSourceData.Case04.parameters,
    NonnegativeSourceData.Case05.parameters,
    NonnegativeSourceData.Case05.parameters,
    NonnegativeSourceData.Case05.parameters,
    NonnegativeSourceData.Case06.parameters,
    NonnegativeSourceData.Case06.parameters,
    NonnegativeSourceData.Case08.parameters,
    NonnegativeSourceData.Case09.parameters,
    NonnegativeSourceData.Case10.parameters,
    NonnegativeSourceData.Case10.parameters,
    NonnegativeSourceData.Case10.parameters,
    NonnegativeSourceData.Case10.parameters,
    NonnegativeSourceData.Case10.parameters,
    NonnegativeSourceData.Case11.parameters,
    NonnegativeSourceData.Case11.parameters,
    NonnegativeSourceData.Case11.parameters,
    NonnegativeSourceData.Case11.parameters,
    NonnegativeSourceData.Case12.parameters,
    NonnegativeSourceData.Case13.parameters,
    NonnegativeSourceData.Case14.parameters,
    NonnegativeSourceData.Case15.parameters,
    NonnegativeSourceData.Case16.parameters,
    NonnegativeSourceData.Case16.parameters] i

def selection (i : Fin 28) : SelectionSource.Parameters :=
  ![SelectionSourceData.Case01.parameters,
    SelectionSourceData.Case02.parameters,
    SelectionSourceData.Case03.parameters,
    SelectionSourceData.Case04.parameters,
    SelectionSourceData.Case05.parameters,
    SelectionSourceData.Case06.parameters,
    SelectionSourceData.Case07.parameters,
    SelectionSourceData.Case08.parameters,
    SelectionSourceData.Case09.parameters,
    SelectionSourceData.Case10.parameters,
    SelectionSourceData.Case11.parameters,
    SelectionSourceData.Case12.parameters,
    SelectionSourceData.Case13.parameters,
    SelectionSourceData.Case14.parameters,
    SelectionSourceData.Case15.parameters,
    SelectionSourceData.Case16.parameters,
    SelectionSourceData.Case17.parameters,
    SelectionSourceData.Case18.parameters,
    SelectionSourceData.Case19.parameters,
    SelectionSourceData.Case20.parameters,
    SelectionSourceData.Case21.parameters,
    SelectionSourceData.Case22.parameters,
    SelectionSourceData.Case23.parameters,
    SelectionSourceData.Case24.parameters,
    SelectionSourceData.Case25.parameters,
    SelectionSourceData.Case26.parameters,
    SelectionSourceData.Case27.parameters,
    SelectionSourceData.Case28.parameters] i

def base (i : Fin 28) : SelectionSourceTable.Row := SelectionSourceTable.row i

structure Valid (i : Fin 28) : Prop where
  rho_pos : 0<(row i).rho
  qa_pos : 0<(row i).qa
  qb_pos : 0<(row i).qb
  qb_lt_one : (row i).qb<1
  lower_pos : 0<(base i).lower
  qa_eq : (row i).qa=(base i).lower/(1+(base i).lower)
  qb_eq : (row i).qb=(base i).upper/(1+(base i).upper)
  source_upper : (base i).upper≤(nonnegative i).b
  CW_bound : (selection i).CJ+2*(selection i).Cmu≤(row i).CW
  Cs_bound : (nonnegative i).A*(2*(row i).qb/(row i).rho-1)≤(row i).Cs
  Cs_cap : (row i).qb≤2*(row i).Cs
  D_bound : (row i).Cs/(row i).qa^2-(1-(row i).qa)/(row i).qa≤(row i).D
  R_bound : (row i).CW/(1-(row i).qb)-1≤(row i).R
  start_pos : 0<(row i).start
  start_bound : (row i).start≤(row i).rho*900/(2*(row i).qb)
  density : if 1≤(base i).lower then
      (1+(base i).lower)*(row i).rho^2≤2*(base i).lower*(276393/1000000)^2
    else (row i).rho≤max (1/4)
      (276393/1000000-max (nonnegative i).A (43/100)*(1-(base i).lower)/(base i).lower)

instance (i : Fin 28) : Decidable (Valid i) :=
  decidable_of_iff ((0<(row i).rho) ∧
    (0<(row i).qa) ∧
    (0<(row i).qb) ∧
    ((row i).qb<1) ∧
    (0<(base i).lower) ∧
    ((row i).qa=(base i).lower/(1+(base i).lower)) ∧
    ((row i).qb=(base i).upper/(1+(base i).upper)) ∧
    ((base i).upper≤(nonnegative i).b) ∧
    ((selection i).CJ+2*(selection i).Cmu≤(row i).CW) ∧
    ((nonnegative i).A*(2*(row i).qb/(row i).rho-1)≤(row i).Cs) ∧
    ((row i).qb≤2*(row i).Cs) ∧
    ((row i).Cs/(row i).qa^2-(1-(row i).qa)/(row i).qa≤(row i).D) ∧
    ((row i).CW/(1-(row i).qb)-1≤(row i).R) ∧
    (0<(row i).start) ∧
    ((row i).start≤(row i).rho*900/(2*(row i).qb)) ∧
    (if 1≤(base i).lower then
      (1+(base i).lower)*(row i).rho^2≤2*(base i).lower*(276393/1000000)^2
    else (row i).rho≤max (1/4)
      (276393/1000000-max (nonnegative i).A (43/100)*(1-(base i).lower)/(base i).lower)))
    ⟨(fun ⟨rho_pos,qa_pos,qb_pos,qb_lt_one,lower_pos,qa_eq,qb_eq,source_upper,CW_bound,Cs_bound,Cs_cap,D_bound,R_bound,start_pos,start_bound,density⟩=>⟨rho_pos,qa_pos,qb_pos,qb_lt_one,lower_pos,qa_eq,qb_eq,source_upper,CW_bound,Cs_bound,Cs_cap,D_bound,R_bound,start_pos,start_bound,density⟩),
      (fun h=>⟨h.rho_pos,h.qa_pos,h.qb_pos,h.qb_lt_one,h.lower_pos,h.qa_eq,h.qb_eq,h.source_upper,h.CW_bound,h.Cs_bound,h.Cs_cap,h.D_bound,h.R_bound,h.start_pos,h.start_bound,h.density⟩)⟩

theorem valid (i : Fin 28) : Valid i := by
  fin_cases i <;> decide +kernel

theorem nonnegative_checked (i : Fin 28) : (nonnegative i).check=true := by
  fin_cases i
  · exact NonnegativeSourceData.Case01.parameters_checked
  · exact NonnegativeSourceData.Case02.parameters_checked
  · exact NonnegativeSourceData.Case03.parameters_checked
  · exact NonnegativeSourceData.Case03.parameters_checked
  · exact NonnegativeSourceData.Case04.parameters_checked
  · exact NonnegativeSourceData.Case04.parameters_checked
  · exact NonnegativeSourceData.Case05.parameters_checked
  · exact NonnegativeSourceData.Case05.parameters_checked
  · exact NonnegativeSourceData.Case05.parameters_checked
  · exact NonnegativeSourceData.Case06.parameters_checked
  · exact NonnegativeSourceData.Case06.parameters_checked
  · exact NonnegativeSourceData.Case08.parameters_checked
  · exact NonnegativeSourceData.Case09.parameters_checked
  · exact NonnegativeSourceData.Case10.parameters_checked
  · exact NonnegativeSourceData.Case10.parameters_checked
  · exact NonnegativeSourceData.Case10.parameters_checked
  · exact NonnegativeSourceData.Case10.parameters_checked
  · exact NonnegativeSourceData.Case10.parameters_checked
  · exact NonnegativeSourceData.Case11.parameters_checked
  · exact NonnegativeSourceData.Case11.parameters_checked
  · exact NonnegativeSourceData.Case11.parameters_checked
  · exact NonnegativeSourceData.Case11.parameters_checked
  · exact NonnegativeSourceData.Case12.parameters_checked
  · exact NonnegativeSourceData.Case13.parameters_checked
  · exact NonnegativeSourceData.Case14.parameters_checked
  · exact NonnegativeSourceData.Case15.parameters_checked
  · exact NonnegativeSourceData.Case16.parameters_checked
  · exact NonnegativeSourceData.Case16.parameters_checked

theorem nonnegative_valid (i : Fin 28) :
    NonnegativeSourceRowValid (nonnegative i).b (nonnegative i).A (nonnegative i).u (nonnegative i).v := by
  fin_cases i
  · exact NonnegativeSourceData.Case01.source_valid
  · exact NonnegativeSourceData.Case02.source_valid
  · exact NonnegativeSourceData.Case03.source_valid
  · exact NonnegativeSourceData.Case03.source_valid
  · exact NonnegativeSourceData.Case04.source_valid
  · exact NonnegativeSourceData.Case04.source_valid
  · exact NonnegativeSourceData.Case05.source_valid
  · exact NonnegativeSourceData.Case05.source_valid
  · exact NonnegativeSourceData.Case05.source_valid
  · exact NonnegativeSourceData.Case06.source_valid
  · exact NonnegativeSourceData.Case06.source_valid
  · exact NonnegativeSourceData.Case08.source_valid
  · exact NonnegativeSourceData.Case09.source_valid
  · exact NonnegativeSourceData.Case10.source_valid
  · exact NonnegativeSourceData.Case10.source_valid
  · exact NonnegativeSourceData.Case10.source_valid
  · exact NonnegativeSourceData.Case10.source_valid
  · exact NonnegativeSourceData.Case10.source_valid
  · exact NonnegativeSourceData.Case11.source_valid
  · exact NonnegativeSourceData.Case11.source_valid
  · exact NonnegativeSourceData.Case11.source_valid
  · exact NonnegativeSourceData.Case11.source_valid
  · exact NonnegativeSourceData.Case12.source_valid
  · exact NonnegativeSourceData.Case13.source_valid
  · exact NonnegativeSourceData.Case14.source_valid
  · exact NonnegativeSourceData.Case15.source_valid
  · exact NonnegativeSourceData.Case16.source_valid
  · exact NonnegativeSourceData.Case16.source_valid

theorem selection_checked (i : Fin 28) : (selection i).check=true := by
  fin_cases i
  · exact SelectionSourceData.Case01.parameters_checked
  · exact SelectionSourceData.Case02.parameters_checked
  · exact SelectionSourceData.Case03.parameters_checked
  · exact SelectionSourceData.Case04.parameters_checked
  · exact SelectionSourceData.Case05.parameters_checked
  · exact SelectionSourceData.Case06.parameters_checked
  · exact SelectionSourceData.Case07.parameters_checked
  · exact SelectionSourceData.Case08.parameters_checked
  · exact SelectionSourceData.Case09.parameters_checked
  · exact SelectionSourceData.Case10.parameters_checked
  · exact SelectionSourceData.Case11.parameters_checked
  · exact SelectionSourceData.Case12.parameters_checked
  · exact SelectionSourceData.Case13.parameters_checked
  · exact SelectionSourceData.Case14.parameters_checked
  · exact SelectionSourceData.Case15.parameters_checked
  · exact SelectionSourceData.Case16.parameters_checked
  · exact SelectionSourceData.Case17.parameters_checked
  · exact SelectionSourceData.Case18.parameters_checked
  · exact SelectionSourceData.Case19.parameters_checked
  · exact SelectionSourceData.Case20.parameters_checked
  · exact SelectionSourceData.Case21.parameters_checked
  · exact SelectionSourceData.Case22.parameters_checked
  · exact SelectionSourceData.Case23.parameters_checked
  · exact SelectionSourceData.Case24.parameters_checked
  · exact SelectionSourceData.Case25.parameters_checked
  · exact SelectionSourceData.Case26.parameters_checked
  · exact SelectionSourceData.Case27.parameters_checked
  · exact SelectionSourceData.Case28.parameters_checked

theorem selection_valid (i : Fin 28) :
    SelectionSourceRowValid (selection i).toReal (base i).lower (base i).upper := by
  fin_cases i
  · exact SelectionSourceData.Case01.source_valid
  · exact SelectionSourceData.Case02.source_valid
  · exact SelectionSourceData.Case03.source_valid
  · exact SelectionSourceData.Case04.source_valid
  · exact SelectionSourceData.Case05.source_valid
  · exact SelectionSourceData.Case06.source_valid
  · exact SelectionSourceData.Case07.source_valid
  · exact SelectionSourceData.Case08.source_valid
  · exact SelectionSourceData.Case09.source_valid
  · exact SelectionSourceData.Case10.source_valid
  · exact SelectionSourceData.Case11.source_valid
  · exact SelectionSourceData.Case12.source_valid
  · exact SelectionSourceData.Case13.source_valid
  · exact SelectionSourceData.Case14.source_valid
  · exact SelectionSourceData.Case15.source_valid
  · exact SelectionSourceData.Case16.source_valid
  · exact SelectionSourceData.Case17.source_valid
  · exact SelectionSourceData.Case18.source_valid
  · exact SelectionSourceData.Case19.source_valid
  · exact SelectionSourceData.Case20.source_valid
  · exact SelectionSourceData.Case21.source_valid
  · exact SelectionSourceData.Case22.source_valid
  · exact SelectionSourceData.Case23.source_valid
  · exact SelectionSourceData.Case24.source_valid
  · exact SelectionSourceData.Case25.source_valid
  · exact SelectionSourceData.Case26.source_valid
  · exact SelectionSourceData.Case27.source_valid
  · exact SelectionSourceData.Case28.source_valid

variable {V : Type*} [DecidableEq V]

theorem activity_fraction_mono {a z : ℝ} (ha : 0<a) (haz : a≤z) :
    a/(1+a)≤z/(1+z) := by
  apply (div_le_div_iff₀ (by positivity) (by have hz := ha.trans_le haz; positivity)).mpr
  nlinarith

/-- Density at the actual activity. The rank input is used only in the
lower-activity branch; the upper branch uses the proved square comparison. -/
theorem density (i : Fin 28) (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    {z : ℝ} (hlo : ((base i).lower:ℝ)≤z)
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    (row i).rho*(S.card:ℝ)≤hardCoreMean G S z := by
  have hv := valid i
  have ha : (0:ℝ)<(base i).lower := by exact_mod_cast hv.lower_pos
  have hrho : (0:ℝ)≤(row i).rho := by exact_mod_cast hv.rho_pos.le
  by_cases hhigh : (1:ℚ)≤(base i).lower
  · apply forest_density_of_upper_activity_certificate G hG S
      (by exact_mod_cast hhigh) hlo hrho
    have hcert := hv.density
    rw [if_pos hhigh] at hcert
    have hreal := (Rat.cast_le (K := ℝ)).mpr hcert
    norm_num at hreal ⊢
    exact hreal
  · have hA : (43/100:ℝ)≤(max (nonnegative i).A (43/100:ℚ):ℝ) := by
      have hreal := (Rat.cast_le (K := ℝ)).mpr (le_max_right (nonnegative i).A (43/100:ℚ))
      norm_num at hreal ⊢
    apply forest_central_density_of_lower_activity_certificate G hG S
      (A := (max (nonnegative i).A (43/100:ℚ):ℝ)) ha
      (by exact_mod_cast (le_of_not_ge hhigh)) hlo hA hrank
    have hcert := hv.density
    rw [if_neg hhigh] at hcert
    have hreal := (Rat.cast_le (K := ℝ)).mpr hcert
    norm_num at hreal ⊢
    exact hreal

/-- All frozen scalar source and density obligations are discharged. The
only graph inputs are the actual forest, one maximum-marginal independent
set, activity membership, n>=900, and the central-rank condition. -/
theorem actual_bounds (i : Fin 28) {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 900≤S.card) (hlo : ((base i).lower:ℝ)≤z) (hhi : z≤((base i).upper:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    MeanMatchedSourceBudget.Bounds G S B z 900 (row i).rho (row i).qb
      (row i).Cs (row i).D (row i).R := by
  have hv := valid i
  have ha : (0:ℝ)<(base i).lower := by exact_mod_cast hv.lower_pos
  have hz : 0<z := ha.trans_le hlo
  have hqa : (row i).qa=(base i).lower/(1+(base i).lower) := hv.qa_eq
  have hqb : (row i).qb=(base i).upper/(1+(base i).upper) := hv.qb_eq
  have hqaR : ((row i).qa:ℝ)=((base i).lower:ℝ)/(1+((base i).lower:ℝ)) := by exact_mod_cast hqa
  have hqbR : ((row i).qb:ℝ)=((base i).upper:ℝ)/(1+((base i).upper:ℝ)) := by exact_mod_cast hqb
  have hqlo : ((row i).qa:ℝ)≤z/(1+z) := by rw [hqaR]; exact activity_fraction_mono ha hlo
  have hqhi : z/(1+z)≤((row i).qb:ℝ) := by rw [hqbR]; exact activity_fraction_mono hz hhi
  have hsourceHi : z≤((nonnegative i).b:ℝ) :=
    hhi.trans (by exact_mod_cast hv.source_upper)
  have hnonneg := NonnegativeSource.Parameters.check_sound (nonnegative_checked i)
  have hselect := SelectionSource.Parameters.check_sound (selection_checked i)
  refine MeanMatchedSourceBudget.of_certificates hB hG 900 (by decide) hn ha hlo hhi hsourceHi
    (by exact_mod_cast hv.rho_pos) (by exact_mod_cast hv.qa_pos) hqlo hqhi
    (by exact_mod_cast hv.qb_lt_one) (density i G hG S hlo hrank)
    hnonneg.A_nonneg hnonneg.u_nonneg hnonneg.v_nonneg (nonnegative_valid i)
    (selection i).toReal hselect.1 hselect.2.1 hselect.2.2 (selection_valid i)
    (CW := ((row i).CW:ℝ)) ?_ ?_ ?_ ?_ ?_
  · change ((selection i).CJ:ℝ)+2*((selection i).Cmu:ℝ)≤((row i).CW:ℝ)
    exact_mod_cast hv.CW_bound
  · exact_mod_cast hv.Cs_bound
  · exact_mod_cast hv.Cs_cap
  · exact_mod_cast hv.D_bound
  · exact_mod_cast hv.R_bound

theorem start_le_available (i : Fin 28) {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hn : 900≤S.card) (hlo : ((base i).lower:ℝ)≤z) (hhi : z≤((base i).upper:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    ((row i).start:ℝ)≤hardCoreAvailableMean G S B z := by
  have hstart : ((row i).start:ℝ)≤((row i).rho:ℝ)*900/(2*((row i).qb:ℝ)) := by
    exact_mod_cast (valid i).start_bound
  exact hstart.trans (actual_bounds i hB hG hn hlo hhi hrank).mean_lower

#print axioms density
#print axioms actual_bounds
#print axioms start_le_available


#print axioms valid
#print axioms nonnegative_valid
#print axioms selection_valid
end ForestUnimodality.Stage900SourceTable
