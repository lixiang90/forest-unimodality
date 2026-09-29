import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell140.Parameters
import ForestUnimodality.BinomialMassData.Q4657_8862.Batch000_049
import ForestUnimodality.BinomialMassData.Q4657_8862.Batch050_099
import ForestUnimodality.BinomialMassData.Q111_211.Batch000_049
import ForestUnimodality.BinomialMassData.Q111_211.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree000.table
  base := (338908866876486291508285825879/10000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (34)
      previous := (17)
      next := (17)
      square := (584262023027174726141907950000000000000)
      linear := (-38645461270330615406731755500000000000)
      constant := (169454433438243145754142912939500000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree000.table
  base := (338908866876486291508285825879/10000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (34)
      previous := (17)
      next := (17)
      square := (584262023027174726141907950000000000000)
      linear := (-38645461270330615406731755500000000000)
      constant := (169454433438243145754142912939500000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 0 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 0 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree001.table
  base := (184043144531147408123491415257216378117773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-25630200334480047411992450650950171000000000000)
      constant := (3620592203799832212721338027315840336749984934253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree001.table
  base := (22984713257475163592243047084094328916719/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-29088536263855307850462356680515500000000000)
      constant := (4101313483478337266305246309221369970804986396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 1 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 1 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (3120750519209934493/6250000000000000000)
  directionHi := (49932008307358951889/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree002.table
  base := (52724314906973606813303892535198761499707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-24871444584163619718113761572352735500000000000)
      constant := (1048645322998805616796747752914631789281248808027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree002.table
  base := (21056307122422492939906234119458858828041/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-112913075892988452744803217748831000000000000)
      constant := (4748449247466251252667947086760001269416066805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 2 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 2 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3120750519209934493/6250000000000000000)
  centralHi := (49932008307358951889/100000000000000000000)
  directionLo := (35307261672396539619/50000000000000000000)
  directionHi := (70614523344793079239/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree003.table
  base := (12859417715952217848600587641157698232469/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (148343972)
      previous := (74171986)
      next := (74171986)
      square := (2549169093664898906291260616511100000000000000)
      linear := (-8206175333574936828940288404273419000000000000)
      constant := (146867416707741038847694262919072225836899325505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree003.table
  base := (64166922856935570100158932653440468024759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-167649079258266289788681722136631000000000000)
      constant := (2991782727547023752904122288672316076930295439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 3 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 3 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35307261672396539619/50000000000000000000)
  centralHi := (70614523344793079239/100000000000000000000)
  directionLo := (43242387656148481201/50000000000000000000)
  directionHi := (86484775312296962403/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree004.table
  base := (521546942073691306258421398773901042049/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-48984133418010811742348834066108035500000000000)
      constant := (461877110250211720271434659870028180889640651560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree004.table
  base := (41629777439983612989371842016401603989017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-222385082623544126832560226524431000000000000)
      constant := (2090998400535779974272774625239139811195025857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 4 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 4 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43242387656148481201/50000000000000000000)
  centralHi := (86484775312296962403/100000000000000000000)
  directionLo := (3120750519209934493/3125000000000000000)
  directionHi := (99864016614717903777/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree005.table
  base := (14266227762278197362599316185831351776151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-61040477834934407754466370312985685500000000000)
      constant := (361288780620418721777412168315343205829874233911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree005.table
  base := (28465083768521197254232028076948222064461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-277121085988821963876438730912231000000000000)
      constant := (1636279767228347346429797159066966794531868181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 5 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 5 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3120750519209934493/3125000000000000000)
  centralHi := (99864016614717903777/100000000000000000000)
  directionLo := (55825682414169414517/50000000000000000000)
  directionHi := (22330272965667765807/20000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree006.table
  base := (10106390584613837522814107596830280988107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (74171986)
      previous := (37085993)
      next := (37085993)
      square := (1274584546832449453145630308255550000000000000)
      linear := (-8121869139095333751842656284429259500000000000)
      constant := (34984472340807091410920855374497005553704075603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree006.table
  base := (2520377943056700033346468688744510356163/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-165928544677049900460158617650015500000000000)
      constant := (713422603587625361627719039309970382266931692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 6 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 6 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55825682414169414517/50000000000000000000)
  centralHi := (22330272965667765807/20000000000000000000)
  directionLo := (122307942185440191067/100000000000000000000)
  directionHi := (30576985546360047767/25000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree007.table
  base := (7266364435035790081043526497292463009303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (13623426)
      previous := (6811713)
      next := (6811713)
      square := (234107365744735613843074954577550000000000000)
      linear := (-1737819727934318362830641689933489500000000000)
      constant := (6136330829478398164780361448218554960734609767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree007.table
  base := (905886993688990965081740364638227198289/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-193296546359688818982097869843915500000000000)
      constant := (681719693107280597694248698056976604760196552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 7 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 7 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122307942185440191067/100000000000000000000)
  centralHi := (30576985546360047767/25000000000000000000)
  directionLo := (132107676443282975807/100000000000000000000)
  directionHi := (2064182444426296497/1562500000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree008.table
  base := (5185179460913299391630806995698953210757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-97209511085705195790818979053618635500000000000)
      constant := (307734711337194306309036576545016749290185567077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree008.table
  base := (1033899617052594644115101505454098000203/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-220664548042327737504037122037815500000000000)
      constant := (698108459727232604751615348710933485335188815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 8 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 8 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132107676443282975807/100000000000000000000)
  centralHi := (2064182444426296497/1562500000000000000)
  directionLo := (141229046689586158477/100000000000000000000)
  directionHi := (70614523344793079239/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree009.table
  base := (357381905732592764461983557499814693819/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (74171986)
      previous := (37085993)
      next := (37085993)
      square := (1274584546832449453145630308255550000000000000)
      linear := (-12140650611403199089215168366721809500000000000)
      constant := (36705474466609212380738060203859454241922692510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree009.table
  base := (1424208950007405661441119631433647664491/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-496065099449933312051952748463431000000000000)
      constant := (1499516276074108785175740147591366138354019055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 9 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 9 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141229046689586158477/100000000000000000000)
  centralHi := (70614523344793079239/50000000000000000000)
  directionLo := (9362251557629803479/6250000000000000000)
  directionHi := (29959204984415371133/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree010.table
  base := (4555410584813613819999030179552214995093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-242644399839104775630108103094747871000000000000)
      constant := (730977882122317913341305996262049461234272134773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree010.table
  base := (2266102792574771184453006806787290454241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-275400551407605574547915626425615500000000000)
      constant := (829809554484127501416887745695631958313263561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 10 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 10 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9362251557629803479/6250000000000000000)
  centralHi := (29959204984415371133/20000000000000000000)
  directionLo := (157898874397703145361/100000000000000000000)
  directionHi := (78949437198851572681/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree011.table
  base := (2419367937076668524078807935148445172471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-266757088672951967654343175588503171000000000000)
      constant := (822885118472103313608751410351538200537899393431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree011.table
  base := (1199382947709071844807529125527918492129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-302768553090244493069854878619515500000000000)
      constant := (934395775719348330276655903184798959188075209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 11 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 11 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157898874397703145361/100000000000000000000)
  centralHi := (78949437198851572681/50000000000000000000)
  directionLo := (165605736584418467479/100000000000000000000)
  directionHi := (4140143414610461687/2500000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree012.table
  base := (634409354645134331613649840486424400401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (148343972)
      previous := (74171986)
      next := (74171986)
      square := (2549169093664898906291260616511100000000000000)
      linear := (-32318864167422128853175360898028719000000000000)
      constant := (103817413903382981156712961334070466935782393129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree012.table
  base := (307977079690322274270712688695152400789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-330136554772883411591794130813415500000000000)
      constant := (1061184535289207849408499663640982880035527069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 12 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 12 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165605736584418467479/100000000000000000000)
  centralHi := (4140143414610461687/2500000000000000000)
  directionLo := (34593910124918784961/20000000000000000000)
  directionHi := (86484775312296962403/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree013.table
  base := (-216942278325429472323970072158725786401/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-157491233170323175851406660288006885500000000000)
      constant := (532025819325789257062425357575990980440531431678) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree013.table
  base := (-110544893268064144139028314065157474457/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-357504556455522330113733383007315500000000000)
      constant := (1208659235942922984754140806489921996318799612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 13 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 13 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34593910124918784961/20000000000000000000)
  centralHi := (86484775312296962403/50000000000000000000)
  directionLo := (180032416239076578101/100000000000000000000)
  directionHi := (90016208119538289051/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree014.table
  base := (-2134894518330795458165122413700130449231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (27246852)
      previous := (13623426)
      next := (13623426)
      square := (468214731489471227686149909155100000000000000)
      linear := (-6920309289275378443409150878974879000000000000)
      constant := (24714955051261204712888546513266199430428079841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree014.table
  base := (-537453047300933392599194891137288295671/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-384872558138161248635672635201215500000000000)
      constant := (1375759428240696756620069169723470575576862818) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 14 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 14 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180032416239076578101/100000000000000000000)
  centralHi := (90016208119538289051/50000000000000000000)
  directionLo := (186828467719687428179/100000000000000000000)
  directionHi := (9341423385984371409/5000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree015.table
  base := (-1601205820104460448142407250719826798187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (74171986)
      previous := (37085993)
      next := (37085993)
      square := (1274584546832449453145630308255550000000000000)
      linear := (-20178213556018929763960192531306909500000000000)
      constant := (76366904854248275095446726847133838214777912077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree015.table
  base := (-3215805914106694216598916011093251004309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-824481119641600334315223774790231000000000000)
      constant := (3123394138923447177443533127014582372037159011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 15 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 15 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186828467719687428179/100000000000000000000)
  centralHi := (9341423385984371409/5000000000000000000)
  directionLo := (9669291830854580577/5000000000000000000)
  directionHi := (193385836617091611541/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree016.table
  base := (-2048934241110524451644303146482212175123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-193660266421093963887759269028639835500000000000)
      constant := (777112618666532130507961880436196803402344872397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree016.table
  base := (-4109866968601789813618354114876654916949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-879217123006878171359102279178031000000000000)
      constant := (3531718805327600680704768618908072446442513571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 16 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 16 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9669291830854580577/5000000000000000000)
  centralHi := (193385836617091611541/100000000000000000000)
  directionLo := (3120750519209934493/1562500000000000000)
  directionHi := (199728033229435807553/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree017.table
  base := (-4843349283430309555937676106839530969397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-411433221676035119799753610551034971000000000000)
      constant := (1749462050709952598986146182836908523094760987883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree017.table
  base := (-2427034331657073061502337573739391096203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-466976563186078004201490391782915500000000000)
      constant := (1987755064915756399496947953667712069005946237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 17 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 17 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3120750519209934493/1562500000000000000)
  centralHi := (199728033229435807553/100000000000000000000)
  directionLo := (25734368043807431891/12500000000000000000)
  directionHi := (205874944350459455129/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree018.table
  base := (-5456912416317959463787646493549094777079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (148343972)
      previous := (74171986)
      next := (74171986)
      square := (2549169093664898906291260616511100000000000000)
      linear := (-48393990056653590202665409227198919000000000000)
      constant := (217773352637531999597446993308837573820053626209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree018.table
  base := (-21353370027363685177374112885257321579/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-494344564868716922723429643976815500000000000)
      constant := (2226982215709499951283260535442117724605611648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 18 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 18 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25734368043807431891/12500000000000000000)
  centralHi := (205874944350459455129/100000000000000000000)
  directionLo := (42368714006875847543/20000000000000000000)
  directionHi := (52960892508594809429/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree019.table
  base := (-5953504937656932962832519730105890164561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-459658599343729503848223755538545571000000000000)
      constant := (2185426139476237229166954093559957924316758656079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree019.table
  base := (-5961990918166342632168036727372833491327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-1043425133102711682490737792341431000000000000)
      constant := (4966416488060253862897598634900023080132630633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 19 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 19 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42368714006875847543/20000000000000000000)
  centralHi := (52960892508594809429/25000000000000000000)
  directionLo := (27206072282476383851/12500000000000000000)
  directionHi := (217648578259811070809/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree020.table
  base := (-6345588998978329069927196192168016629731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-483771288177576695872458828032300871000000000000)
      constant := (2425615269020592915191675558523686459647836051709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree020.table
  base := (-3176555084234011401362165198707255935131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-549080568233994759767308148364615500000000000)
      constant := (2756155852350193765586555472879664258512032749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 20 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 20 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27206072282476383851/12500000000000000000)
  centralHi := (217648578259811070809/100000000000000000000)
  directionLo := (55825682414169414517/25000000000000000000)
  directionHi := (223302729656677658069/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree021.table
  base := (-1660899904473883025669816022417117241167/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-575832173482340008953167687671265500000000000)
      constant := (3038914607402497819000149496565171796612007986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree021.table
  base := (-1662562480188573541427146616662202704949/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-576448569916633678289247400558515500000000000)
      constant := (3045592876057268247086857867025989646745931142) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 21 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 21 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55825682414169414517/25000000000000000000)
  centralHi := (223302729656677658069/100000000000000000000)
  directionLo := (45763441533927245081/20000000000000000000)
  directionHi := (114408603834818112703/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree022.table
  base := (-6856296343620116983045146718031797279691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-531996665845271079920928973019811471000000000000)
      constant := (2949376400705779912215036918503145108810096752149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree022.table
  base := (-214442617161145573342142375704150021993/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-603816571599272596811186652752415500000000000)
      constant := (3351324456214396084007967846806649589933594352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 22 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 22 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45763441533927245081/20000000000000000000)
  centralHi := (114408603834818112703/50000000000000000000)
  directionLo := (46840375736894166993/20000000000000000000)
  directionHi := (117100939342235417483/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree023.table
  base := (-6991042995009212701387335861310961216363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-556109354679118271945164045513566771000000000000)
      constant := (3232631840491435259019442279069117791297659568757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree023.table
  base := (-6996209210558098436105710027696755019417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-1262369146563823030666251809892631000000000000)
      constant := (7346373619853167262564952475716025769780535743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 23 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 23 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46840375736894166993/20000000000000000000)
  centralHi := (117100939342235417483/50000000000000000000)
  directionLo := (23946549946274464909/10000000000000000000)
  directionHi := (239465499462744649091/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree024.table
  base := (-7054035285154460348816618731878159614689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (148343972)
      previous := (74171986)
      next := (74171986)
      square := (2549169093664898906291260616511100000000000000)
      linear := (-64469115945885051552155457556369119000000000000)
      constant := (392218595326211473832299946335425286333927120519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree024.table
  base := (-3529287814425308363317657175396647942239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-658552574964550433855065157140215500000000000)
      constant := (4011042159749332971856922094310937836963577481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 24 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 24 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23946549946274464909/10000000000000000000)
  centralHi := (239465499462744649091/100000000000000000000)
  directionLo := (122307942185440191067/50000000000000000000)
  directionHi := (48923176874176076427/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree025.table
  base := (-3525244332650073945243469144282058941501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-302167366173406327996817095250538685500000000000)
      constant := (1920640277057973213052899894045479581904656384739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree025.table
  base := (-7054472093304226216351147190920438054573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-1371841153294378704754008818668231000000000000)
      constant := (8729549097501897962786943613128806177372355467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 25 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 25 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122307942185440191067/50000000000000000000)
  centralHi := (48923176874176076427/20000000000000000000)
  directionLo := (3120750519209934493/1250000000000000000)
  directionHi := (249660041536794759441/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree026.table
  base := (-3492397330210449059685159412540160679567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-314223710590329924008934631497416335500000000000)
      constant := (2083242603439893734441188943808293722815783938513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree026.table
  base := (-1747070980742010012866729661936208672003/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-713288578329828270898943661528015500000000000)
      constant := (4734286357536738876700835080944779107427508874) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 26 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 26 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3120750519209934493/1250000000000000000)
  centralHi := (249660041536794759441/100000000000000000000)
  directionLo := (25460428471210033423/10000000000000000000)
  directionHi := (254604284712100334231/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree027.table
  base := (-6860651636564781238141283642271814166279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (148343972)
      previous := (74171986)
      next := (74171986)
      square := (2549169093664898906291260616511100000000000000)
      linear := (-72506678890500782226900481720954219000000000000)
      constant := (500612078154705340883322296035332192013651539409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree027.table
  base := (-3431851765958564728258597926752920499109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-740656580012467189420882913721915500000000000)
      constant := (5119495391123184534785260185804851726459168211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 27 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 27 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25460428471210033423/10000000000000000000)
  centralHi := (254604284712100334231/100000000000000000000)
  directionLo := (32431790742111360901/12500000000000000000)
  directionHi := (259454325936890887209/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree028.table
  base := (-6681174503950836067509059826704570131721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (27246852)
      previous := (13623426)
      next := (13623426)
      square := (468214731489471227686149909155100000000000000)
      linear := (-13809648956088861878904885877190679000000000000)
      constant := (99148773188792880764343700062914354498490844231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree028.table
  base := (-3341920100443062874070487771229689637847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-768024581695106107942822165915815500000000000)
      constant := (5520332435366492695222704734341716987633413713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 28 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 28 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32431790742111360901/12500000000000000000)
  centralHi := (259454325936890887209/100000000000000000000)
  directionLo := (132107676443282975807/50000000000000000000)
  directionHi := (52843070577313190323/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree029.table
  base := (-3224493453412267122675673806995043741733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-350392743841100712045287240238049285500000000000)
      constant := (2612388621725616060960415245127694263740268552187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree029.table
  base := (-3225656155257932956881233568190631242789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-795392583377745026464761418109715500000000000)
      constant := (5936739203804408006254612112721934406439790931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 29 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 29 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132107676443282975807/50000000000000000000)
  centralHi := (52843070577313190323/20000000000000000000)
  directionLo := (26889209388633712323/10000000000000000000)
  directionHi := (268892093886337123231/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree030.table
  base := (-308314938655033315510317918899663322483/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (74171986)
      previous := (37085993)
      next := (37085993)
      square := (1274584546832449453145630308255550000000000000)
      linear := (-40272120917558256450822752942769659500000000000)
      constant := (311384854766499151975285983019655561217669834930) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree030.table
  base := (-6168324914116629136946950258472374725201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-1645521170120767889973401340607231000000000000)
      constant := (12737333221695433996230454827786481404859326279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 30 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 30 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26889209388633712323/10000000000000000000)
  centralHi := (268892093886337123231/100000000000000000000)
  directionLo := (273488872914758456187/100000000000000000000)
  directionHi := (68372218228689614047/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree031.table
  base := (-2917485793198362106514831824822807610843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-374505432674947904069522312731804585500000000000)
      constant := (2999351882681828872985653751160662377269727529477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree031.table
  base := (-1167347003433245040607251897876749900989/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-1700257173486045727017279844995031000000000000)
      constant := (13632146637251961772155897458346107088290343655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 31 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 31 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273488872914758456187/100000000000000000000)
  centralHi := (68372218228689614047/25000000000000000000)
  directionLo := (11120386256729831047/4000000000000000000)
  directionHi := (17375603526140361011/6250000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree032.table
  base := (-272828667130461679694262079760266749907/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-386561777091871500081639848978682235500000000000)
      constant := (3203037798247284894010960871066215349360791897730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree032.table
  base := (-218324261187920914492882312884136943927/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-1754993176851323564061158349382831000000000000)
      constant := (14557849027439803730153816989011925477985650825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 32 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 32 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11120386256729831047/4000000000000000000)
  centralHi := (17375603526140361011/6250000000000000000)
  directionLo := (141229046689586158477/50000000000000000000)
  directionHi := (56491618675834463391/20000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree033.table
  base := (-5032424830223637123185177823386778379263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (148343972)
      previous := (74171986)
      next := (74171986)
      square := (2549169093664898906291260616511100000000000000)
      linear := (-88581804779732243576390530050124419000000000000)
      constant := (758557438571585125370768639270453424249064766873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree033.table
  base := (-5033756534074328686438674543553413477951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-1809729180216601401105036853770631000000000000)
      constant := (15514381754435107619348481445600881478548143529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 33 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 33 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141229046689586158477/50000000000000000000)
  centralHi := (56491618675834463391/20000000000000000000)
  directionLo := (286837549789080773443/100000000000000000000)
  directionHi := (71709387447270193361/25000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree034.table
  base := (-4563638608490486549369806641601804497377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-821348931851437384211749842944875071000000000000)
      constant := (7261505973590323094769285889674450142329774855103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree034.table
  base := (-2282397122460230645793141901431806207293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-932232591790939619074457679079215500000000000)
      constant := (8250847717446769814814021437409781555845108347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 34 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 34 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286837549789080773443/100000000000000000000)
  centralHi := (71709387447270193361/25000000000000000000)
  directionLo := (18196946153326622799/6250000000000000000)
  directionHi := (58230227690645192957/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree035.table
  base := (-506393979716593678445412993998225524263/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (13623426)
      previous := (6811713)
      next := (6811713)
      square := (234107365744735613843074954577550000000000000)
      linear := (-8627159394747801798326376688149289500000000000)
      constant := (78668615059703478158479221998663806301634331172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree035.table
  base := (-1013038454386862280849185407501076189067/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-959600593473578537596396931273115500000000000)
      constant := (8759874239643248731782262707178831673973096186) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 35 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 35 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18196946153326622799/6250000000000000000)
  centralHi := (58230227690645192957/20000000000000000000)
  directionLo := (147700872438364187227/50000000000000000000)
  directionHi := (59080348975345674891/20000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree036.table
  base := (-1747876966250690486261354796525947721451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (74171986)
      previous := (37085993)
      next := (37085993)
      square := (1274584546832449453145630308255550000000000000)
      linear := (-48309683862173987125567777107354759500000000000)
      constant := (453947575263860891422983775486724682793170721421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree036.table
  base := (-139864879086342819404239153488924454869/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-1973937190312434912236672366934031000000000000)
      constant := (18568505861821205967819562188523105858619431275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 36 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 36 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147700872438364187227/50000000000000000000)
  centralHi := (59080348975345674891/20000000000000000000)
  directionLo := (9362251557629803479/3125000000000000000)
  directionHi := (299592049844153711329/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree037.table
  base := (-1449054927246533318044032903592438617793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-446843499176489480142227530213070485500000000000)
      constant := (4323044577293480888181957049366768373521081890527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree037.table
  base := (-1449430643468352115929503463760355083363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-1014336596838856374640275435660915500000000000)
      constant := (9823969042261100096441621070095398731333595877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 37 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 37 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9362251557629803479/3125000000000000000)
  centralHi := (299592049844153711329/100000000000000000000)
  directionLo := (303724549194542463793/100000000000000000000)
  directionHi := (151862274597271231897/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree038.table
  base := (-90351189319275951348507110496359689141/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-917799687186826152308690132919896271000000000000)
      constant := (9134611677919041418786347325457477565334282767475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree038.table
  base := (-2259429743631692315798217242204300531573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-2083409197042990586324429375709631000000000000)
      constant := (20758020304816180425204233864454400336033838467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 38 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 38 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303724549194542463793/100000000000000000000)
  centralHi := (151862274597271231897/50000000000000000000)
  directionLo := (153900785603123391411/50000000000000000000)
  directionHi := (307801571206246782823/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree039.table
  base := (-789117695954607997463749744811123858863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (74171986)
      previous := (37085993)
      next := (37085993)
      square := (1274584546832449453145630308255550000000000000)
      linear := (-52328465334481852462940289189647309500000000000)
      constant := (535367481170402036288356521966012703029298458473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree039.table
  base := (-394699320102709089021304685172319195801/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-1069072600204134211684153940048715500000000000)
      constant := (10949365800404302614697921684415890854167487358) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 39 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 39 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153900785603123391411/50000000000000000000)
  centralHi := (307801571206246782823/100000000000000000000)
  directionLo := (77956322983867211433/25000000000000000000)
  directionHi := (311825291935468845733/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree040.table
  base := (-856874271384066518667795180555324085067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-966025064854520536357160277907406871000000000000)
      constant := (10152090300787434612319060826913491659636250853013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree040.table
  base := (-857359665150605390322355435986492717539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-2192881203773546260412186384485231000000000000)
      constant := (23070054352517846327434976695519685357722446181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 40 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 40 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77956322983867211433/25000000000000000000)
  centralHi := (311825291935468845733/100000000000000000000)
  directionLo := (157898874397703145361/50000000000000000000)
  directionHi := (315797748795406290723/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree041.table
  base := (-11878894301086591563945503538293512141/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-495068876844183864190697675200581085500000000000)
      constant := (5340516012015091203433419712508892555089092030796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree041.table
  base := (-23862551315267259430227969876619532411/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-1123808603569412048728032444436515500000000000)
      constant := (12135986860382350004902364122502381543595059738) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 41 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 41 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157898874397703145361/50000000000000000000)
  centralHi := (315797748795406290723/100000000000000000000)
  directionLo := (319720852616548454503/100000000000000000000)
  directionHi := (39965106577068556813/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree042.table
  base := (707011955142977488049152745059279487247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-2299887624766927257155624541711831000000000000)
      constant := (25449964385484848668469625158605281182051723687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree042.table
  base := (353325197382243255279987512872393481071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-1151176605252050967249971696630415500000000000)
      constant := (12752238604152210340994251041614142830170761991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 42 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 42 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319720852616548454503/100000000000000000000)
  centralHi := (39965106577068556813/12500000000000000000)
  directionLo := (323596398390740532837/100000000000000000000)
  directionHi := (161798199195370266419/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree043.table
  base := (1549017511827746009926306765590568623251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-1038363131356062112429865495388672771000000000000)
      constant := (11779292446782883788883159702964330968703009177011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree043.table
  base := (309741146305682358393937227146799700873/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-2357089213869379771543821897648631000000000000)
      constant := (26767554290221341592264082095278746347412834165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 43 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 43 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323596398390740532837/100000000000000000000)
  centralHi := (161798199195370266419/50000000000000000000)
  directionLo := (327426074870443122889/100000000000000000000)
  directionHi := (32742607487044312289/10000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree044.table
  base := (243078541970524596020059271105632682367/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-531237910094954652227050283941214035500000000000)
      constant := (6174301276873254375847894718046637896196912961435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree044.table
  base := (1215258355553187954711859331196407838273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-1205912608617328804293850201018215500000000000)
      constant := (14030598051327428802381184566264277273367752233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 44 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 44 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327426074870443122889/100000000000000000000)
  centralHi := (32742607487044312289/10000000000000000000)
  directionLo := (165605736584418467479/50000000000000000000)
  directionHi := (331211473168836934959/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree045.table
  base := (1676073564187984562170765698113131597629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (74171986)
      previous := (37085993)
      next := (37085993)
      square := (1274584546832449453145630308255550000000000000)
      linear := (-60366028279097583137685313354232409500000000000)
      constant := (718408961422857375135075874377415400611043994741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree045.table
  base := (1675957830423039018523352460957791297793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-1233280610299967722815789453212115500000000000)
      constant := (14692697590325407817207282975163499326369042153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 45 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 45 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165605736584418467479/50000000000000000000)
  centralHi := (331211473168836934959/100000000000000000000)
  directionLo := (334954094485016487103/100000000000000000000)
  directionHi := (5233657726328382611/1562500000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree046.table
  base := (4312960659785399846608954682104219441203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-1110701197857603688502570712869938671000000000000)
      constant := (13527565914814466185734327871724069872600133254483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree046.table
  base := (4312761370443996690738790811891201740973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-2521297223965213282675457410812031000000000000)
      constant := (30740145237385292601227062944180634192709858933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 46 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 46 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334954094485016487103/100000000000000000000)
  centralHi := (5233657726328382611/1562500000000000000)
  directionLo := (169327678530330294347/50000000000000000000)
  directionHi := (67731071412132117739/20000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree047.table
  base := (1328276604764432590151290241722831192733/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-567406943345725440263402892681846985500000000000)
      constant := (7068607016629200308618639765343008789012929317626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree047.table
  base := (5312934915640975494101957779694497970349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-2576033227330491119719335915199831000000000000)
      constant := (32125440978231346604166243930108035744137907829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 47 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 47 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169327678530330294347/50000000000000000000)
  centralHi := (67731071412132117739/20000000000000000000)
  directionLo := (342316602459608550941/100000000000000000000)
  directionHi := (171158301229804275471/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree048.table
  base := (6352483665756022549509252219891604227321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (148343972)
      previous := (74171986)
      next := (74171986)
      square := (2549169093664898906291260616511100000000000000)
      linear := (-128769619502810896950115650873049919000000000000)
      constant := (1640033742558841574264752124882140543478423353809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree048.table
  base := (6352336141023457580080401583462590868831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-2630769230695768956763214419587631000000000000)
      constant := (33541277944169810677953917447457226008071224951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 48 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 48 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342316602459608550941/100000000000000000000)
  centralHi := (171158301229804275471/50000000000000000000)
  directionLo := (345939101249187849611/100000000000000000000)
  directionHi := (86484775312296962403/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree049.table
  base := (1486201508290386628113820919779130612121/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (27246852)
      previous := (13623426)
      next := (13623426)
      square := (468214731489471227686149909155100000000000000)
      linear := (-24143658456309087032148488374514379000000000000)
      constant := (314221085674242569627094359994356543829200756845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree049.table
  base := (7430880697910153456062067701242285789539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-2685505234061046793807092923975431000000000000)
      constant := (34987652379913045133089502216856326805636065819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 49 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 49 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345939101249187849611/100000000000000000000)
  centralHi := (86484775312296962403/25000000000000000000)
  directionLo := (349524058151512663217/100000000000000000000)
  directionHi := (174762029075756331609/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree050.table
  base := (8548606565902281752475186555287337010669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-1207151953192992456599511002844959871000000000000)
      constant := (16046801174857325021785322868591145786193929596109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree050.table
  base := (26714054842876418493596489707240672141/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-1370120618713162315425485714181615500000000000)
      constant := (18232280561420722333598718343074244914302313760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 50 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 50 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349524058151512663217/100000000000000000000)
  centralHi := (174762029075756331609/50000000000000000000)
  directionLo := (11033519272623918631/3125000000000000000)
  directionHi := (353072616723965396193/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree051.table
  base := (4852610263978083578768162120904656287073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (74171986)
      previous := (37085993)
      next := (37085993)
      square := (1274584546832449453145630308255550000000000000)
      linear := (-68403591223713313812430337518817509500000000000)
      constant := (928344801739808064939820651189766062175282074617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree051.table
  base := (9705126871046539759077922444932828222707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-2794977240791602467894849932751031000000000000)
      constant := (37972001509468027761377614484462435445303138347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 51 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 51 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11033519272623918631/3125000000000000000)
  centralHi := (353072616723965396193/100000000000000000000)
  directionLo := (44573232952551371403/12500000000000000000)
  directionHi := (14263434544816438849/4000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree052.table
  base := (5450399354481501175578071991833133236851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-627688665430343420323990573916235235500000000000)
      constant := (8693523985808841242682009547999888870853488926611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree052.table
  base := (5450359139147401923442009250724526922789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-1424856622078440152469364218569415500000000000)
      constant := (19754985648332411716240684036693712663129489069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 52 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 52 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44573232952551371403/12500000000000000000)
  centralHi := (14263434544816438849/4000000000000000000)
  directionLo := (360064832478153156203/100000000000000000000)
  directionHi := (90016208119538289051/25000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree053.table
  base := (485411935450495701711205307456354946799/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-1279490019694534032672216220326225771000000000000)
      constant := (18077324956954233495643672624775323179415482025975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree053.table
  base := (12135229339568255929154651689360035928251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-2904449247522158141982606941526631000000000000)
      constant := (41078468595321345777489855111347041159561662771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 53 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 53 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360064832478153156203/100000000000000000000)
  centralHi := (90016208119538289051/25000000000000000000)
  directionLo := (90877626867510224439/25000000000000000000)
  directionHi := (363510507470040897757/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree054.table
  base := (13408683572600690110745834924918207832909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (148343972)
      previous := (74171986)
      next := (74171986)
      square := (2549169093664898906291260616511100000000000000)
      linear := (-144844745392042358299605699202220119000000000000)
      constant := (2086781853417895670663754803916943004015518137861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree054.table
  base := (1676078039965005165613097872758057052931/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-1479592625443717989513242722957215500000000000)
      constant := (21338745907236560839575470337918982832214164204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 54 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 54 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90877626867510224439/25000000000000000000)
  centralHi := (363510507470040897757/100000000000000000000)
  directionLo := (366923826556320573201/100000000000000000000)
  directionHi := (183461913278160286601/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree055.table
  base := (7360461977140079034432081025322263196843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-663857698681114208360343182656868185500000000000)
      constant := (9749091273933134356063342030048915334835911416523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree055.table
  base := (7360436561731657160439637052934295872851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-1506960627126356908035181975151115500000000000)
      constant := (22153519807123942739732396377888540286555199371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 55 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 55 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366923826556320573201/100000000000000000000)
  centralHi := (183461913278160286601/50000000000000000000)
  directionLo := (92576421116670883277/25000000000000000000)
  directionHi := (370305684466683533109/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree056.table
  base := (16071993996710348704887178303093170558987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (27246852)
      previous := (13623426)
      next := (13623426)
      square := (468214731489471227686149909155100000000000000)
      linear := (-27588328289715828749896355873622279000000000000)
      constant := (412831878712853274302797395017274463418109942043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree056.table
  base := (4017987601320040289103714792486908674541/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-1534328628808995826557121227345015500000000000)
      constant := (22983555433118917069946461045219487322198479722) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 56 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 56 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92576421116670883277/25000000000000000000)
  centralHi := (370305684466683533109/100000000000000000000)
  directionLo := (373656935439374856359/100000000000000000000)
  directionHi := (9341423385984371409/2500000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree057.table
  base := (17461872190970566464994898121048178815913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (148343972)
      previous := (74171986)
      next := (74171986)
      square := (2549169093664898906291260616511100000000000000)
      linear := (-152882308336658088974350723366805219000000000000)
      constant := (2330308309516741990849721543218441787984099870977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree057.table
  base := (349236696396105963370319461441834794507/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-1561696630491634745079060479538915500000000000)
      constant := (23828852310062979933237551562954081672156153675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 57 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 57 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373656935439374856359/100000000000000000000)
  centralHi := (9341423385984371409/2500000000000000000)
  directionLo := (188489197870561877501/50000000000000000000)
  directionHi := (376978395741123755003/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree058.table
  base := (118065877619705426686373198513781310803/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-700026731931884996396695791397501135500000000000)
      constant := (10865110189153098384068020489317366933505825606640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree058.table
  base := (18890508390514770523643104409690930978119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-3178129264348547327201999463465631000000000000)
      constant := (49378820075579439666067323275029047938076835999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 58 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 58 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188489197870561877501/50000000000000000000)
  centralHi := (376978395741123755003/100000000000000000000)
  directionLo := (380270845988957555067/100000000000000000000)
  directionHi := (95067711497239388767/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree059.table
  base := (1017899170987985972084585564914154237693/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-712083076348808592408813327644378785500000000000)
      constant := (11250549267627885947176065307848428006450015533730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree059.table
  base := (20357955978048713690621116142084644204837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-3232865267713825164245877967853431000000000000)
      constant := (51130456558578833009877134261614379444643548077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 59 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 59 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380270845988957555067/100000000000000000000)
  centralHi := (95067711497239388767/25000000000000000000)
  directionLo := (191767516646305116373/50000000000000000000)
  directionHi := (383535033292610232747/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree060.table
  base := (218641883373825753865056695435882876883/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (74171986)
      previous := (37085993)
      next := (37085993)
      square := (1274584546832449453145630308255550000000000000)
      linear := (-80459935640636909824547873765695159500000000000)
      constant := (1293633833561076909687625486707651201826184705350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree060.table
  base := (5466041208110972529129063684163111781321/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-1643800635539551500644878236120615500000000000)
      constant := (26456306750741513299405186222319181799232384482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 60 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 60 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191767516646305116373/50000000000000000000)
  centralHi := (383535033292610232747/100000000000000000000)
  directionLo := (386771673234183223081/100000000000000000000)
  directionHi := (193385836617091611541/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree061.table
  base := (1463071521460900134229922628662373604569/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-736195765182655784433048400138134085500000000000)
      constant := (12041575786114983195074496931003392121108530032072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree061.table
  base := (11704562108016661733997342449151171831947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-1671168637222190419166817488314515500000000000)
      constant := (27362645213120174489765341071464104821130112387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 61 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 61 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386771673234183223081/100000000000000000000)
  centralHi := (193385836617091611541/50000000000000000000)
  directionLo := (12186920365622457151/3125000000000000000)
  directionHi := (389981451699918628833/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree062.table
  base := (24992842316323854966688825758082653538257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-1496504219199158760890331872770023471000000000000)
      constant := (24894326060559907615989909056285625184815942294577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree062.table
  base := (6248206271465078733279035234172066086761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-1698536638904829337688756740508415500000000000)
      constant := (28284243465124662482115835393842010108497372962) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 62 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 62 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12186920365622457151/3125000000000000000)
  centralHi := (389981451699918628833/100000000000000000000)
  directionLo := (98291256644341886811/25000000000000000000)
  directionHi := (78633005315473509449/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree063.table
  base := (13307637286451653966102384783029250921111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-1724055451284587248202456854040565500000000000)
      constant := (29159787208885022403695603752289280530258782831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree063.table
  base := (51982929348074707549615824246351384987/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-1725904640587468256210695992702315500000000000)
      constant := (29221101337225451148022960788945759862817594112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 63 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 63 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98291256644341886811/25000000000000000000)
  centralHi := (78633005315473509449/20000000000000000000)
  directionLo := (396323029329848927421/100000000000000000000)
  directionHi := (198161514664924463711/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree064.table
  base := (3534554330143653873578676089758934042379/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-772364798433426572469401008878767035500000000000)
      constant := (13278485109095513836264961191884606426411332629676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree064.table
  base := (1131056880935117899972873387301636992277/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-3506545284540214349465270489792431000000000000)
      constant := (60346437373299978316685880454108188513329107925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 64 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 64 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396323029329848927421/100000000000000000000)
  centralHi := (198161514664924463711/50000000000000000000)
  directionLo := (79891213291774323021/20000000000000000000)
  directionHi := (199728033229435807553/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree065.table
  base := (29976317069485396819513792170923413225023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-1568842285700700336963037090251289371000000000000)
      constant := (27408439653388276632988278605552974272064340801503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree065.table
  base := (29976306275924693266806653403668542484457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-3561281287905492186509148994180231000000000000)
      constant := (62281190786319634320291921743085742179950510097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 65 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 65 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79891213291774323021/20000000000000000000)
  centralHi := (199728033229435807553/50000000000000000000)
  directionLo := (402564720864112258999/100000000000000000000)
  directionHi := (402564720864112259/100000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree066.table
  base := (31714917265854009656226537981443147230007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (148343972)
      previous := (74171986)
      next := (74171986)
      square := (2549169093664898906291260616511100000000000000)
      linear := (-176994997170505280998585795860560519000000000000)
      constant := (3141482281518774597902941258299832356533529940703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree066.table
  base := (7928727008738622829203391424665638345789/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-1808008645635385011776513749284015500000000000)
      constant := (32123231355494146786885653475736600769585744138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 66 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 66 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402564720864112258999/100000000000000000000)
  centralHi := (402564720864112259/100000000000000000)
  directionLo := (202824776554792969477/50000000000000000000)
  directionHi := (81129910621917187791/20000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree067.table
  base := (6698446272441639494263161162265840090241/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-1617067663368394721011507235238799971000000000000)
      constant := (29151672783088804094759925668993393378480051132005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree067.table
  base := (6698444693908898849586094883397483963313/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-3670753294636047860596906002955831000000000000)
      constant := (66242252976749439987965768102031573917653290365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 67 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 67 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202824776554792969477/50000000000000000000)
  centralHi := (81129910621917187791/20000000000000000000)
  directionLo := (102177775650949698919/25000000000000000000)
  directionHi := (408711102603798795677/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree068.table
  base := (35308256100367609333959176530094701133761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-1641180352202241913035742307732555271000000000000)
      constant := (30043436337677440468816746727787873727426692505121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree068.table
  base := (8827062338358573852471307972137398672491/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-1862744649000662848820392253671815500000000000)
      constant := (34134280719983366999199269454170312252595943622) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 68 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 68 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102177775650949698919/25000000000000000000)
  centralHi := (408711102603798795677/100000000000000000000)
  directionLo := (411749888700918910257/100000000000000000000)
  directionHi := (205874944350459455129/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree069.table
  base := (37162988735869189779873834053149567138301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (148343972)
      previous := (74171986)
      next := (74171986)
      square := (2549169093664898906291260616511100000000000000)
      linear := (-185032560115121011673330820025145619000000000000)
      constant := (3438736793727860977664606850407792755549650642229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree069.table
  base := (18581491484797388208291681230807809782171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-1890112650683301767342331505865715500000000000)
      constant := (35162693989837661112701153609954763999312035091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 69 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 69 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411749888700918910257/100000000000000000000)
  centralHi := (205874944350459455129/50000000000000000000)
  directionLo := (414766411729331421119/100000000000000000000)
  directionHi := (1296145036654160691/312500000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree070.table
  base := (19528213478488079991499568958300750645811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (13623426)
      previous := (6811713)
      next := (6811713)
      square := (234107365744735613843074954577550000000000000)
      linear := (-17238833978264656092696045435919039500000000000)
      constant := (325176093421639200764013625104746796975519363779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree070.table
  base := (7811284405971622036613168899059807327323/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-3834961304731881371728541516119231000000000000)
      constant := (72412732494003684839327612434264378410098736415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 70 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 70 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414766411729331421119/100000000000000000000)
  centralHi := (1296145036654160691/312500000000000000)
  directionLo := (104440288488336553441/25000000000000000000)
  directionHi := (83552230790669242753/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree071.table
  base := (20494284408227743705190026968974874394351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-856759209351891744554223762606910585500000000000)
      constant := (16399657167377805562217551891343488718113707284111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree071.table
  base := (20494282303615976016882488739125479038033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-1944848654048579604386210010253515500000000000)
      constant := (37265297448580097831436752478469705952252267193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 71 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 71 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104440288488336553441/25000000000000000000)
  centralHi := (83552230790669242753/20000000000000000000)
  directionLo := (420734580473292687291/100000000000000000000)
  directionHi := (105183645118323171823/25000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree072.table
  base := (42959412674110867822561083820492265623459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (148343972)
      previous := (74171986)
      next := (74171986)
      square := (2549169093664898906291260616511100000000000000)
      linear := (-193070123059736742348075844189730719000000000000)
      constant := (3749422516628048324127334577471350419733278888811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree072.table
  base := (4295940907889598576318509691967164287053/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-1972216655731218522908149262447415500000000000)
      constant := (38339487558447635699127556154569866606119433065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 72 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 72 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420734580473292687291/100000000000000000000)
  centralHi := (105183645118323171823/25000000000000000000)
  directionLo := (423687140068758475431/100000000000000000000)
  directionHi := (52960892508594809429/12500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree073.table
  base := (22484478574187795933199555956371101111551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-880871898185738936578458835100665885500000000000)
      constant := (17351861036442881238004990486217031514281026673311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree073.table
  base := (44968954078194922049250973311740766006187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-3999169314827714882860177029282631000000000000)
      constant := (78857873092364051909564323197947673643361451427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 73 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423687140068758475431/100000000000000000000)
  centralHi := (52960892508594809429/12500000000000000000)
  directionLo := (426619265989300964903/100000000000000000000)
  directionHi := (53327408248662620613/12500000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree074.table
  base := (2350860053776849328993694511820857610219/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-892928242602662532590576371347543535500000000000)
      constant := (17838036290803768653709772741148187615840710036590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree074.table
  base := (23508599227104058439341942281926416363131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-2026952659096496359952027766835215500000000000)
      constant := (40533644386163199602342977818583692982902955251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 74 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426619265989300964903/100000000000000000000)
  centralHi := (53327408248662620613/12500000000000000000)
  directionLo := (214765688348288127093/50000000000000000000)
  directionHi := (429531376696576254187/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree075.table
  base := (49104143475389297213099918352063053393479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (148343972)
      previous := (74171986)
      next := (74171986)
      square := (2549169093664898906291260616511100000000000000)
      linear := (-201107686004352473022820868354315819000000000000)
      constant := (4073539350730292654643426448203939373306422849391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree075.table
  base := (49104141237700056597465172871905516483873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-4108641321558270556947934038058231000000000000)
      constant := (83307222113630978980229444962702430499378509833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 75 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214765688348288127093/50000000000000000000)
  centralHi := (429531376696576254187/100000000000000000000)
  directionLo := (216211938280742406007/50000000000000000000)
  directionHi := (86484775312296962403/20000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree076.table
  base := (51229783522301550747413223950023831942333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-1834081862873019449229622887682597671000000000000)
      constant := (37661066781570811030677961655412895066659931904413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree076.table
  base := (51229781612444670923529981997595074397499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-4163377324923548393991812542446031000000000000)
      constant := (85577673079938590361166981709967286307251052979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 76 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216211938280742406007/50000000000000000000)
  centralHi := (86484775312296962403/20000000000000000000)
  directionLo := (435297156519622141617/100000000000000000000)
  directionHi := (217648578259811070809/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree077.table
  base := (26697060260423357916511203234257369930399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (13623426)
      previous := (6811713)
      next := (6811713)
      square := (234107365744735613843074954577550000000000000)
      linear := (-18961168894968026951569979185472989500000000000)
      constant := (394629698397430822424689842740238264050041644911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree077.table
  base := (53394118891075366943559656863706006921123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-4218113328288826231035691046833831000000000000)
      constant := (87878641640646985264404706036269242134135317083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 77 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435297156519622141617/100000000000000000000)
  centralHi := (217648578259811070809/50000000000000000000)
  directionLo := (438151594688042394821/100000000000000000000)
  directionHi := (219075797344021197411/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree078.table
  base := (55597153885273058745411138684974834176647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (148343972)
      previous := (74171986)
      next := (74171986)
      square := (2549169093664898906291260616511100000000000000)
      linear := (-209145248948968203697565892518900919000000000000)
      constant := (4411087236578261449703663713771251492026546553263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree078.table
  base := (55597152494746526127446836178575973780943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-4272849331654104068079569551221631000000000000)
      constant := (90210127769985377907363708109542198928701363303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 78 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438151594688042394821/100000000000000000000)
  centralHi := (219075797344021197411/50000000000000000000)
  directionLo := (3445215288641326117/781250000000000000)
  directionHi := (440987556946089742977/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree079.table
  base := (5783888312221196236712990789071082143989/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-953209964687280512651164052581931785500000000000)
      constant := (20369645415326263433216777749758844487382238063145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree079.table
  base := (28919440968002465643360831642435350714639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-2163792667509690952561724027804715500000000000)
      constant := (46286065723125931803798060720772488749166442919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 79 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3445215288641326117/781250000000000000)
  centralHi := (440987556946089742977/100000000000000000000)
  directionLo := (443805397482823441271/100000000000000000000)
  directionHi := (55475674685352930159/12500000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree080.table
  base := (30059653908055985045589465370347128447733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-965266309104204108663281588828809435500000000000)
      constant := (20896113769566952036348823071012278746979090713813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree080.table
  base := (1202386136087290499829805186075323585829/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-2191160669192329871083663279998615500000000000)
      constant := (47482326325585596301132820325356727034117322725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 80 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443805397482823441271/100000000000000000000)
  centralHi := (55475674685352930159/12500000000000000000)
  directionLo := (446605459313355316137/100000000000000000000)
  directionHi := (223302729656677658069/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree081.table
  base := (31219213808484628267952925914047696662131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (74171986)
      previous := (37085993)
      next := (37085993)
      square := (1274584546832449453145630308255550000000000000)
      linear := (-108591405946791967186155458341743009500000000000)
      constant := (2381033069320921844972008290017617553401641978299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree081.table
  base := (12487685350831570583138926287733833137269/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-4437057341749937579211205064385031000000000000)
      constant := (97387691369353904157321837839750500925521765745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 81 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446605459313355316137/100000000000000000000)
  centralHi := (223302729656677658069/50000000000000000000)
  directionLo := (449388074766230566993/100000000000000000000)
  directionHi := (224694037383115283497/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree082.table
  base := (16199060557498121369942067128196231556183/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-989378997938051300687516661322564735500000000000)
      constant := (21969196975396365818292329074796648301449510188526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree082.table
  base := (16199060373576219866758138617976562139113/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-2245896672557607708127541784386415500000000000)
      constant := (49920623793920412004079912819870040045990899746) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 82 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449388074766230566993/100000000000000000000)
  centralHi := (224694037383115283497/50000000000000000000)
  directionLo := (226076782971906138549/50000000000000000000)
  directionHi := (452153565943812277099/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree083.table
  base := (67192751406897091716052117590953559855693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-2002870684709949793399268395138884771000000000000)
      constant := (45031623643307559540705633417570613416805870851373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree083.table
  base := (33596375389848285131989498317242167292243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-2273264674240246626649481036580315500000000000)
      constant := (51162660647859726417539864055647425030017950603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 83 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226076782971906138549/50000000000000000000)
  centralHi := (452153565943812277099/100000000000000000000)
  directionLo := (22745112257873754053/5000000000000000000)
  directionHi := (454902245157475081061/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree084.table
  base := (17406988734643025414468314095185222201569/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-2298167090185710867827101437225215500000000000)
      constant := (52310979956026578281152924072725079555272106898) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree084.table
  base := (69627954403938393655014796499111099111557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-4601265351845771090342840577548431000000000000)
      constant := (104839912483800899694424260668510329243545629197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 84 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22745112257873754053/5000000000000000000)
  centralHi := (454902245157475081061/100000000000000000000)
  directionLo := (45763441533927245081/10000000000000000000)
  directionHi := (457634415339272450811/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree085.table
  base := (72101852648903106063200719630592806648979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-2051096062377644177447738540126395371000000000000)
      constant := (47258375981058590926684167866963698651565264580019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree085.table
  base := (72101852193239113959971156992698476464819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-4656001355211048927386719081936231000000000000)
      constant := (107385021144347804982476628296895563870690206699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 85 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45763441533927245081/10000000000000000000)
  centralHi := (457634415339272450811/100000000000000000000)
  directionLo := (92070074086322725757/20000000000000000000)
  directionHi := (230175185215806814393/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree086.table
  base := (37307222194784556064918400057758484727297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-1037604375605745684735986806310075335500000000000)
      constant := (24195949309962453632433214931813837980357899474017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree086.table
  base := (74614444001264121966556543225275685116033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-4710737358576326764430597586324031000000000000)
      constant := (109960647270845205562496399571614164777050905193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 86 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92070074086322725757/20000000000000000000)
  centralHi := (230175185215806814393/50000000000000000000)
  directionLo := (231525197878184552361/50000000000000000000)
  directionHi := (463050395756369104723/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree087.table
  base := (77165730035659737980705128164093366734699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21815290000000000000000000000000000000000000000
      center := (148343972)
      previous := (74171986)
      next := (74171986)
      square := (2549169093664898906291260616511100000000000000)
      linear := (-233257937782815395721800965012656219000000000000)
      constant := (5504316915040214497147824022362127008739381174771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree087.table
  base := (7716572970480107522308443010962580245573/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-2382736680970802300737238045355915500000000000)
      constant := (56283395428903782368096019354629073675565777665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 87 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231525197878184552361/50000000000000000000)
  centralHi := (463050395756369104723/100000000000000000000)
  directionLo := (232867384182358293593/50000000000000000000)
  directionHi := (465734768364716587187/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree088.table
  base := (39877854740991709043153245919336436832091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-1061717064439592876760221878803830635500000000000)
      constant := (25349618412652177249127050451492975093352871824251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree088.table
  base := (15951141840021929103073531034479861325831/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-4820209365306882438518354595099631000000000000)
      constant := (115203451900616259351139719049351517530436609755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 88 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232867384182358293593/50000000000000000000)
  centralHi := (465734768364716587187/100000000000000000000)
  directionLo := (46840375736894166993/10000000000000000000)
  directionHi := (468403757368941669931/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree089.table
  base := (20596095659989419413180503517915789574633/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-1073773408856516472772339415050708285500000000000)
      constant := (25936526194006486098872578241537304297019271969426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree089.table
  base := (82384382399847404135373488764265669142731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-4874945368672160275562233099487431000000000000)
      constant := (117870630395382717138829115435176430855903526851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 89 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46840375736894166993/10000000000000000000)
  centralHi := (468403757368941669931/100000000000000000000)
  directionLo := (471057624257317950841/100000000000000000000)
  directionHi := (235528812128658975421/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree090.table
  base := (42525874717494854522378513562790307142487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (74171986)
      previous := (37085993)
      next := (37085993)
      square := (1274584546832449453145630308255550000000000000)
      linear := (-120647750363715563198272994588620659500000000000)
      constant := (2947794384556847011965288647038497468450242522623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree090.table
  base := (2126293730762022888463782504954218376319/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (1513714)
      previous := (756857)
      next := (756857)
      square := (26011929527192845982563883841950000000000000)
      linear := (-2464840686018719056303055801937615500000000000)
      constant := (60284163169416578007690644618957230126641963980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 90 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471057624257317950841/100000000000000000000)
  centralHi := (235528812128658975421/50000000000000000000)
  directionLo := (473696623193109436083/100000000000000000000)
  directionHi := (118424155798277359021/25000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree091.table
  base := (10969726225533743834470012353523707817173/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2003445000000000000000000000000000000000000000
      center := (13623426)
      previous := (6811713)
      next := (6811713)
      square := (234107365744735613843074954577550000000000000)
      linear := (-22405838728374768669317846684580889500000000000)
      constant := (553683432919408047249358401880240852096220928788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree091.table
  base := (87757809630105460703516344152965704761903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-4984417375402715949649990108263031000000000000)
      constant := (123296539728211515985245170211123007141704683463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 91 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473696623193109436083/100000000000000000000)
  centralHi := (118424155798277359021/25000000000000000000)
  directionLo := (95264200259732589203/20000000000000000000)
  directionHi := (14885031290583217063/3125000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree092.table
  base := (90502563694913555347896957471713589752067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-2219884884214574521617384047582682471000000000000)
      constant := (55475084899210870992527141887467005983644132733987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree092.table
  base := (90502563546608897374941889350419932013389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-5039153378767993786693868612650831000000000000)
      constant := (126055270561197712363071356951563697793168091669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 92 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95264200259732589203/20000000000000000000)
  centralHi := (14885031290583217063/3125000000000000000)
  directionLo := (23946549946274464909/5000000000000000000)
  directionHi := (478930998925489298181/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree093.table
  base := (23321502765598725085573784946346759326101/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (74171986)
      previous := (37085993)
      next := (37085993)
      square := (1274584546832449453145630308255550000000000000)
      linear := (-124666531836023428535645506670913209500000000000)
      constant := (3150145796693093770378152167942426473801819576858) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree093.table
  base := (93286010936125342828404606572213598271667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-5093889382133271623737747117038631000000000000)
      constant := (128844518835838792184085798419107804608652886507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 93 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23946549946274464909/5000000000000000000)
  centralHi := (478930998925489298181/100000000000000000000)
  directionLo := (240763424955584353533/50000000000000000000)
  directionHi := (481526849911168707067/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree094.table
  base := (96108151869228938523457635512978594497563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-2268110261882268905665854192570193071000000000000)
      constant := (57943594749160466796743831875168218861481067024443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree094.table
  base := (19221630352346587374693992677508399205949/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-5148625385498549460781625621426431000000000000)
      constant := (131664284550490957310750158795403471205240277145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 94 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240763424955584353533/50000000000000000000)
  centralHi := (481526849911168707067/100000000000000000000)
  directionLo := (121027195455964399863/25000000000000000000)
  directionHi := (484108781823857599453/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree095.table
  base := (49484493041930236736140760456461293808161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98168805000000000000000000000000000000000000000
      center := (667547874)
      previous := (333773937)
      next := (333773937)
      square := (11471260921492045078310672774299950000000000000)
      linear := (-1146111475358058048845044632531974185500000000000)
      constant := (29598998062322830298768848902468753389630212923521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree095.table
  base := (98968985992357162028882488434878408850663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-5203361388863827297825504125814231000000000000)
      constant := (134514567703770739150281463239964166640440367423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 95 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121027195455964399863/25000000000000000000)
  centralHi := (484108781823857599453/100000000000000000000)
  directionLo := (486677016195120438357/100000000000000000000)
  directionHi := (243338508097560219179/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree096.table
  base := (25467128419932144277516257446395915074437/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10907645000000000000000000000000000000000000000
      center := (74171986)
      previous := (37085993)
      next := (37085993)
      square := (1274584546832449453145630308255550000000000000)
      linear := (-128685313308331293873018018753205759500000000000)
      constant := (3359212692578321019741828730246112300432842948346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree096.table
  base := (101868513601847277671001743742412481820743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-5258097392229105134869382630202031000000000000)
      constant := (137395368294513880579374615813846922103141299103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 96 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486677016195120438357/100000000000000000000)
  centralHi := (243338508097560219179/50000000000000000000)
  directionLo := (122307942185440191067/25000000000000000000)
  directionHi := (489231768741760764269/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree097.table
  base := (104806734634478536453856824706895779055043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196337610000000000000000000000000000000000000000
      center := (1335095748)
      previous := (667547874)
      next := (667547874)
      square := (22942521842984090156621345548599900000000000000)
      linear := (-2340448328383810481738559410051458971000000000000)
      constant := (61747091774013912978258626260031294597375520106723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree097.table
  base := (104806734568198545287040922666390267203579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-5312833395594382971913261134589831000000000000)
      constant := (140306686321740708634701835098465168086170540659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 97 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell140.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122307942185440191067/25000000000000000000)
  centralHi := (489231768741760764269/100000000000000000000)
  directionLo := (49177324957728012659/10000000000000000000)
  directionHi := (491773249577280126591/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 4657
  qDenominator := 8862
  table := BinomialMassData.Q4657_8862.Degree098.table
  base := (107783648929298069543296897600906426301903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4006890000000000000000000000000000000000000000
      center := (27246852)
      previous := (13623426)
      next := (13623426)
      square := (468214731489471227686149909155100000000000000)
      linear := (-48256347290156279056383560868269679000000000000)
      constant := (1286567062185483849354704189371836832048483211167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4657_8862.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree098.table
  base := (107783648872897234193393741140166615306511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3027428)
      previous := (1513714)
      next := (1513714)
      square := (52023859054385691965127767683900000000000000)
      linear := (-5367569398959660808957139638977631000000000000)
      constant := (143248521784626973512498285720887795880061176231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 98 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell140.Kernel098
