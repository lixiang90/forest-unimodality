import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell167.Parameters
import ForestUnimodality.BinomialMassData.Q53_93.Batch000_049
import ForestUnimodality.BinomialMassData.Q53_93.Batch050_099
import ForestUnimodality.BinomialMassData.Q53_93.Batch100_149
import ForestUnimodality.BinomialMassData.Q107_187.Batch000_049
import ForestUnimodality.BinomialMassData.Q107_187.Batch050_099
import ForestUnimodality.BinomialMassData.Q107_187.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree000.table
  base := (2033837592763462014499253921/100000000000000000000000000)
  polynomial :=
    { denominator := 19375000000000000000000000000000000000000
      center := (53)
      previous := (0)
      next := (40)
      square := (1325883394900425303608582083125000000000)
      linear := (-4618276757178637493411743618750000000000)
      constant := (394056033597920765309230447193750000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree000.table
  base := (2033837592763462014499253921/100000000000000000000000000)
  polynomial :=
    { denominator := 116875000000000000000000000000000000000000
      center := (321)
      previous := (0)
      next := (240)
      square := (7998070801496113928219511275625000000000)
      linear := (-27858637212658232621548259893750000000000)
      constant := (2377047686542296229446003020168750000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree001.table
  base := (62024229386741037770782564911135467683993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (13144)
      previous := (0)
      next := (9920)
      square := (328819081935305475294928356615000000000000)
      linear := (-1520115675405488984186138286280000000000000)
      constant := (60364793905673443358879406639266184444317273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree001.table
  base := (30933245283567956516854770883605224498083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87422500000000000000000000000000000000000000
      center := (240108)
      previous := (0)
      next := (179520)
      square := (5982556959519093218308194434167500000000000)
      linear := (-27684609241149031523474000052460000000000000)
      constant := (1095586865756262365232306126169083595473464427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49476079170996267679/100000000000000000000)
  directionHi := (309225494818726673/625000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree002.table
  base := (78052008706175500899277282297215156852617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (78864)
      previous := (0)
      next := (59520)
      square := (1972914491611832851769570139690000000000000)
      linear := (-11369392290184055220036984930660000000000000)
      constant := (235419570880096345371566769917431297206094811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree002.table
  base := (9711302273474130370725647253839242260197/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43711250000000000000000000000000000000000000
      center := (120054)
      previous := (0)
      next := (89760)
      square := (2991278479759546609154097217083750000000000)
      linear := (-17265478923614852523014950852197500000000000)
      constant := (355435455344448128960705789865564462596828893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49476079170996267679/100000000000000000000)
  centralHi := (309225494818726673/625000000000000000)
  directionLo := (546638610755218117/781250000000000000)
  directionHi := (69969742176667918977/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree003.table
  base := (10149232020077694877700708176276637312667/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-4539363509311725511652380047880000000000000)
      constant := (54605632846573863799358097283579242287364935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree003.table
  base := (2017188260607791269070580325976932421171/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-165509225813241514274343213425320000000000000)
      constant := (1977072097347702733313503512899113745898217475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (546638610755218117/781250000000000000)
  centralHi := (69969742176667918977/100000000000000000000)
  directionLo := (85695082883465794441/100000000000000000000)
  directionHi := (42847541441732897221/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree004.table
  base := (34037071962285368850125004280289978675523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-5288929588562099283292431785540000000000000)
      constant := (41348734275896095044353071067838669507177603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree004.table
  base := (16892706307655305791215256354268176624681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (480216)
      previous := (0)
      next := (359040)
      square := (11965113919038186436616388868335000000000000)
      linear := (-96447310118782104182283410016530000000000000)
      constant := (748787891349556824145635154313163868388469889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85695082883465794441/100000000000000000000)
  centralHi := (42847541441732897221/50000000000000000000)
  directionLo := (49476079170996267679/50000000000000000000)
  directionHi := (98952158341992535359/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree005.table
  base := (11713217602531391747278955535225582560581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (39432)
      previous := (0)
      next := (29760)
      square := (986457245805916425884785069845000000000000)
      linear := (-9057743501718709582398725284800000000000000)
      constant := (51569429323371111050075774895930354522155023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree005.table
  base := (5808472667704939912231429908496553043037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87422500000000000000000000000000000000000000
      center := (240108)
      previous := (0)
      next := (179520)
      square := (5982556959519093218308194434167500000000000)
      linear := (-55070003665471725613697606660200000000000000)
      constant := (311701832055981917410658846287028463361960853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49476079170996267679/50000000000000000000)
  centralHi := (98952158341992535359/100000000000000000000)
  directionLo := (110631876286509095933/100000000000000000000)
  directionHi := (55315938143254547967/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree006.table
  base := (16395420929782224817236808769360860099367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-6788061747062846826572535260860000000000000)
      constant := (31277694093747908508563034036235786555491687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree006.table
  base := (1015615525984407278997340176867048534907/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21855625000000000000000000000000000000000000
      center := (60027)
      previous := (0)
      next := (44880)
      square := (1495639239879773304577048608541875000000000)
      linear := (-15479088067888099784063377078033750000000000)
      constant := (71028736792086255573792862648558820217162883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110631876286509095933/100000000000000000000)
  centralHi := (55315938143254547967/50000000000000000000)
  directionLo := (15148893555310475399/12500000000000000000)
  directionHi := (121191148442483803193/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree007.table
  base := (2879427504493927457154222529919903156551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2402500000000000000000000000000000000000000
      center := (6572)
      previous := (0)
      next := (4960)
      square := (164409540967652737647464178307500000000000)
      linear := (-1884406956578305149553146749630000000000000)
      constant := (7668066309387466704234515902595526933445511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree007.table
  base := (2851848277843968430179504830059847361913/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87422500000000000000000000000000000000000000
      center := (240108)
      previous := (0)
      next := (179520)
      square := (5982556959519093218308194434167500000000000)
      linear := (-68762700877633072658809409964070000000000000)
      constant := (279167780216731538356166098426645302398735697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15148893555310475399/12500000000000000000)
  centralHi := (121191148442483803193/100000000000000000000)
  directionLo := (65450700666499428779/50000000000000000000)
  directionHi := (130901401332998857559/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree008.table
  base := (398708290212175727189803468339012463733/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (19716)
      previous := (0)
      next := (14880)
      square := (493228622902958212942392534922500000000000)
      linear := (-6215395429172695777389479052135000000000000)
      constant := (23832106983653110656763525682146864664711195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree008.table
  base := (7889752379949647635484149274348280332069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-302436197934854984725461246464020000000000000)
      constant := (1158879611527159561641551087355965014932120861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65450700666499428779/50000000000000000000)
  centralHi := (130901401332998857559/100000000000000000000)
  directionLo := (139939484353335837953/100000000000000000000)
  directionHi := (69969742176667918977/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree009.table
  base := (5285840937311841629323862798523881779517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-9036759984813968141492690473840000000000000)
      constant := (34129057911136631447357031086311450390115837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree009.table
  base := (5220428819962143036201805840097050601679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-329821592359177678815684853071760000000000000)
      constant := (1246422623020687783359788618333923762490112951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139939484353335837953/100000000000000000000)
  centralHi := (69969742176667918977/50000000000000000000)
  directionLo := (74214118756494401519/50000000000000000000)
  directionHi := (148428237512988803039/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree010.table
  base := (3166465006917967427978946063279653979197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-9786326064064341913132742211500000000000000)
      constant := (37455905172084841097365361438811747474008317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree010.table
  base := (623026143888581356837950512776770212939/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-357206986783500372905908459679500000000000000)
      constant := (1369358758471616042772832829094454387881319455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74214118756494401519/50000000000000000000)
  centralHi := (148428237512988803039/100000000000000000000)
  directionLo := (78228549937581783193/50000000000000000000)
  directionHi := (156457099875163566387/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree011.table
  base := (1440455078594764613340994311536658788691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (78864)
      previous := (0)
      next := (59520)
      square := (1972914491611832851769570139690000000000000)
      linear := (-31607676429944147054318381847480000000000000)
      constant := (124763847683077601395059279359950187287796153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree011.table
  base := (1399720286001151555464972300884121117627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (87312)
      previous := (0)
      next := (65280)
      square := (2175475258006942988475707066970000000000000)
      linear := (-34962943746165733363284733298840000000000000)
      constant := (138327144856166445268029235736380621032936233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78228549937581783193/50000000000000000000)
  centralHi := (156457099875163566387/100000000000000000000)
  directionLo := (32818718141622532291/20000000000000000000)
  directionHi := (10255849419257041341/6250000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree012.table
  base := (-757129512594479735033847616222931881/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2402500000000000000000000000000000000000000
      center := (6572)
      previous := (0)
      next := (4960)
      square := (164409540967652737647464178307500000000000)
      linear := (-2821364555641272364103211421705000000000000)
      constant := (11604668288678102569759934692620809762462359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree012.table
  base := (-35636382274898072217614682113836109817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-411977775632145761086355672894980000000000000)
      constant := (1699301346143379474145766717160441265075809327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32818718141622532291/20000000000000000000)
  centralHi := (10255849419257041341/6250000000000000000)
  directionLo := (85695082883465794441/50000000000000000000)
  directionHi := (171390165766931588883/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree013.table
  base := (-1236110166968714754760499625954771301383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-12035024301815463228052897424480000000000000)
      constant := (51878765420167314882379188013827464779370937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree013.table
  base := (-315594523641064812944581418019019378443/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87422500000000000000000000000000000000000000
      center := (240108)
      previous := (0)
      next := (179520)
      square := (5982556959519093218308194434167500000000000)
      linear := (-109840792514117113794144819875680000000000000)
      constant := (474992218232520180136174406516825411355226733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85695082883465794441/50000000000000000000)
  centralHi := (171390165766931588883/100000000000000000000)
  directionLo := (22298567544992863369/12500000000000000000)
  directionHi := (178388540359942906953/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree014.table
  base := (-2307155854810412367764849936769609389121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (78864)
      previous := (0)
      next := (59520)
      square := (1972914491611832851769570139690000000000000)
      linear := (-38353771143197510999078847486420000000000000)
      constant := (173765238932659312881596503854933216131164157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree014.table
  base := (-46568093209441828085627572919316203627/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (480216)
      previous := (0)
      next := (359040)
      square := (11965113919038186436616388868335000000000000)
      linear := (-233374282240395574633401443055230000000000000)
      constant := (1060963082667925908674959840692170791884185925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22298567544992863369/12500000000000000000)
  centralHi := (178388540359942906953/100000000000000000000)
  directionLo := (23140317137346315901/12500000000000000000)
  directionHi := (185122537098770527209/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree015.table
  base := (-1624762548228623599458684234164171911511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (13144)
      previous := (0)
      next := (9920)
      square := (328819081935305475294928356615000000000000)
      linear := (-6767078230158105385666500449900000000000000)
      constant := (32257778666534195676866049771093230793037929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree015.table
  base := (-408344368100169417245332123159041368689/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43711250000000000000000000000000000000000000
      center := (120054)
      previous := (0)
      next := (89760)
      square := (2991278479759546609154097217083750000000000)
      linear := (-61766744863139230419628311589775000000000000)
      constant := (295502235912174753507279034643032732378314359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23140317137346315901/12500000000000000000)
  centralHi := (185122537098770527209/100000000000000000000)
  directionLo := (191620030664908205183/100000000000000000000)
  directionHi := (1497031489569595353/781250000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree016.table
  base := (-4086806839648260326324631051865257142763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-14283722539566584542973052637460000000000000)
      constant := (71637529507935957585918563411637487885804757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree016.table
  base := (-4100792452608818773998941388936536809569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-521519353329436537447250099325940000000000000)
      constant := (2625427040406389242227804569085798244306181639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191620030664908205183/100000000000000000000)
  centralHi := (1497031489569595353/781250000000000000)
  directionLo := (197904316683985070717/100000000000000000000)
  directionHi := (98952158341992535359/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree017.table
  base := (-1209008569901225138038731981244421381963/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (19716)
      previous := (0)
      next := (14880)
      square := (493228622902958212942392534922500000000000)
      linear := (-11274966464112718735959828281340000000000000)
      constant := (59453470451160993018655874481249833155800671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree017.table
  base := (-969477458285884146032346931818361064411/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20570000000000000000000000000000000000000000
      center := (56496)
      previous := (0)
      next := (42240)
      square := (1407660461063316051366633984510000000000000)
      linear := (-32288514573750543031616100349040000000000000)
      constant := (170915511404260951608599110336538156452532865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197904316683985070717/100000000000000000000)
  centralHi := (98952158341992535359/50000000000000000000)
  directionLo := (203995100363439470387/100000000000000000000)
  directionHi := (50998775090859867597/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree018.table
  base := (-5509716590720153966504852419776015578031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-15782854698067332086253156112780000000000000)
      constant := (87404829297312831038017081040115249029512209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree018.table
  base := (-5518926973216597489435725830173547179327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-576290142178081925627697312541420000000000000)
      constant := (3203994668790039120033681606205141228686114137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203995100363439470387/100000000000000000000)
  centralHi := (50998775090859867597/25000000000000000000)
  directionLo := (209909226530003756929/100000000000000000000)
  directionHi := (20990922653000375693/10000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree019.table
  base := (-6117162542372631249084144430573212310053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-16532420777317705857893207850440000000000000)
      constant := (96029189867857633762145248568549142970039067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree019.table
  base := (-3062313420768980490848207247133884752339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (480216)
      previous := (0)
      next := (359040)
      square := (11965113919038186436616388868335000000000000)
      linear := (-301837768301202309858960459574580000000000000)
      constant := (1760198856904991124357239207651060184095457509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209909226530003756929/100000000000000000000)
  centralHi := (20990922653000375693/10000000000000000000)
  directionLo := (215661229228990354921/100000000000000000000)
  directionHi := (107830614614495177461/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree020.table
  base := (-1333073821058513374670781099981808041783/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (78864)
      previous := (0)
      next := (59520)
      square := (1972914491611832851769570139690000000000000)
      linear := (-51845960569704238888599778764300000000000000)
      constant := (315412954672931930604788649933762237077698055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree020.table
  base := (-6671410354528925014754640256047405242569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-631060931026727313808144525756900000000000000)
      constant := (3854530722524728277943238052876278286072604639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215661229228990354921/100000000000000000000)
  centralHi := (107830614614495177461/50000000000000000000)
  directionLo := (110631876286509095933/50000000000000000000)
  directionHi := (221263752573018191867/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree021.table
  base := (-357981748915258630290469088098600327939/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2402500000000000000000000000000000000000000
      center := (6572)
      previous := (0)
      next := (4960)
      square := (164409540967652737647464178307500000000000)
      linear := (-4507888233954613350293327831440000000000000)
      constant := (28681280579275207962192013433318725424253105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree021.table
  base := (-7164517282622588345547879197664233048707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-658446325451050007898368132364640000000000000)
      constant := (4206210465402002177288613917810849434519764917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110631876286509095933/50000000000000000000)
  centralHi := (221263752573018191867/100000000000000000000)
  directionLo := (226727877890718381873/100000000000000000000)
  directionHi := (113363938945359190937/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree022.table
  base := (-7603994803437033580707167719339936660601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-18781119015068827172813363063420000000000000)
      constant := (124787724855240650389640172517634320869162439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree022.table
  base := (-380396720865783169553374663081831062741/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7947500000000000000000000000000000000000000
      center := (21828)
      previous := (0)
      next := (16320)
      square := (543868814501735747118926766742500000000000)
      linear := (-15587084542622106863377084976645000000000000)
      constant := (103984034734771713869109888053134295257731805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226727877890718381873/100000000000000000000)
  centralHi := (113363938945359190937/50000000000000000000)
  directionLo := (232063381477912615487/100000000000000000000)
  directionHi := (3625990335592384617/1562500000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree023.table
  base := (-4000766466398088248884186850815672268311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (39432)
      previous := (0)
      next := (29760)
      square := (986457245805916425884785069845000000000000)
      linear := (-29296027641478801416680122201620000000000000)
      constant := (202983742664531428248670878956353416850459387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree023.table
  base := (-4002353470191009275594430991085026015929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (480216)
      previous := (0)
      next := (359040)
      square := (11965113919038186436616388868335000000000000)
      linear := (-356608557149847698039407672790060000000000000)
      constant := (2480842712173568786362329687762912725248978799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232063381477912615487/100000000000000000000)
  centralHi := (3625990335592384617/1562500000000000000)
  directionLo := (237278940138179744651/100000000000000000000)
  directionHi := (59319735034544936163/25000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree024.table
  base := (-334184559643744543773957550776611473031/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-20280251173569574716093466538740000000000000)
      constant := (146327160676094454417090236655871909360430225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree024.table
  base := (-8357167270957300444041178502914054371559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-740602508724018090169038952187860000000000000)
      constant := (5365292591088794238150727066334318432680953329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237278940138179744651/100000000000000000000)
  centralHi := (59319735034544936163/25000000000000000000)
  directionLo := (48476459376993521277/20000000000000000000)
  directionHi := (121191148442483803193/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree025.table
  base := (-8665054525584755907013820872136287406831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-21029817252819948487733518276400000000000000)
      constant := (157799975852548707137430199983127027802035409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree025.table
  base := (-8667105430935562493432609223230578191791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-767987903148340784259262558795600000000000000)
      constant := (5786056433279312252341890375944099911211260521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48476459376993521277/20000000000000000000)
  centralHi := (121191148442483803193/50000000000000000000)
  directionLo := (247380395854981338397/100000000000000000000)
  directionHi := (123690197927490669199/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree026.table
  base := (-4467126035009444403969442238514938807791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (39432)
      previous := (0)
      next := (29760)
      square := (986457245805916425884785069845000000000000)
      linear := (-32669074998105483389060355021090000000000000)
      constant := (254609396413675970626209205299481431417138547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree026.table
  base := (-8935897107921640684420071652831969040529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-795373297572663478349486165403340000000000000)
      constant := (6223928844498838105736693955958038874621741399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247380395854981338397/100000000000000000000)
  centralHi := (123690197927490669199/50000000000000000000)
  directionLo := (252279493148971501729/100000000000000000000)
  directionHi := (25227949314897150173/10000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree027.table
  base := (-9163282906574405955851620067042128773233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-22528949411320696031013621751720000000000000)
      constant := (182144991638626837951180928951342514248923087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree027.table
  base := (-1145575076607273295208676317111347163383/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43711250000000000000000000000000000000000000
      center := (120054)
      previous := (0)
      next := (89760)
      square := (2991278479759546609154097217083750000000000)
      linear := (-102844836499623271554963721501385000000000000)
      constant := (834859102084002277932939735185274551043659873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252279493148971501729/100000000000000000000)
  centralHi := (25227949314897150173/10000000000000000000)
  directionLo := (64271312162599345831/25000000000000000000)
  directionHi := (10283409946015895333/4000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree028.table
  base := (-935297651885939020700369699753639578973/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (13144)
      previous := (0)
      next := (9920)
      square := (328819081935305475294928356615000000000000)
      linear := (-11639257745285534901326836744690000000000000)
      constant := (97507680403664956056848360993843761823034735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree028.table
  base := (-9354030673133684649494273026369561150533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-850144086421308866529933378618820000000000000)
      constant := (7150859859596804669210238225294562816127011523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64271312162599345831/25000000000000000000)
  centralHi := (10283409946015895333/4000000000000000000)
  directionLo := (65450700666499428779/25000000000000000000)
  directionHi := (261802802665997715117/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree029.table
  base := (-9503972515990568512344711360285467164227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (78864)
      previous := (0)
      next := (59520)
      square := (1972914491611832851769570139690000000000000)
      linear := (-72084244709464330722881175681120000000000000)
      constant := (625050271352596084915472862393486998165533559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree029.table
  base := (-9504814808447342571797564702536355206841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-877529480845631560620156985226560000000000000)
      constant := (7639868029536835872557994282123776194771977071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65450700666499428779/25000000000000000000)
  centralHi := (261802802665997715117/100000000000000000000)
  directionLo := (133218420173324783967/50000000000000000000)
  directionHi := (53287368069329913587/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree030.table
  base := (-4808382138722496124925410193155595530951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (13144)
      previous := (0)
      next := (9920)
      square := (328819081935305475294928356615000000000000)
      linear := (-12388823824535908672966888482350000000000000)
      constant := (111074353215777870075664269141377472694756089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree030.table
  base := (-2404359129344013575974941483098437956677/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87422500000000000000000000000000000000000000
      center := (240108)
      previous := (0)
      next := (179520)
      square := (5982556959519093218308194434167500000000000)
      linear := (-226228718817488563677595147958575000000000000)
      constant := (2036470104757594105272501043504030723092961987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133218420173324783967/50000000000000000000)
  centralHi := (53287368069329913587/20000000000000000000)
  directionLo := (270991646188661545947/100000000000000000000)
  directionHi := (67747911547165386487/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree031.table
  base := (-2422933120973698604560279989233324531969/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 77500000000000000000000000000000000000000
      center := (212)
      previous := (0)
      next := (160)
      square := (5303533579601701214434328332500000000000)
      linear := (-205864626841307992883659908890000000000000)
      constant := (1906539055768347805164842123391266939508961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree031.table
  base := (-605766776521436866709478924485823094531/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21855625000000000000000000000000000000000000
      center := (60027)
      previous := (0)
      next := (44880)
      square := (1495639239879773304577048608541875000000000)
      linear := (-58268766855892309300037762402627500000000000)
      constant := (541805249860873280145166153917865877207345461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270991646188661545947/100000000000000000000)
  centralHi := (67747911547165386487/25000000000000000000)
  directionLo := (275471150420829753553/100000000000000000000)
  directionHi := (137735575210414876777/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree032.table
  base := (-4864585457367484633123422666266425387881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (39432)
      previous := (0)
      next := (29760)
      square := (986457245805916425884785069845000000000000)
      linear := (-39415169711358847333820820660030000000000000)
      constant := (376704326370037402849193838148833895606739077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree032.table
  base := (-9729597755841511814560329976684857349429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-959685664118599642890827805049780000000000000)
      constant := (9208868721744377661160834153088187223347817299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275471150420829753553/100000000000000000000)
  centralHi := (137735575210414876777/50000000000000000000)
  directionLo := (139939484353335837953/50000000000000000000)
  directionHi := (279878968706671675907/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree033.table
  base := (-4864653158027625547487002396968322645061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (13144)
      previous := (0)
      next := (9920)
      square := (328819081935305475294928356615000000000000)
      linear := (-13513172943411469330426966088840000000000000)
      constant := (133162306261406463832516035360498441938096379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree033.table
  base := (-9729645940084181449235342225333883082763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (87312)
      previous := (0)
      next := (65280)
      square := (2175475258006942988475707066970000000000000)
      linear := (-89733732594811121543731946514320000000000000)
      constant := (887802440710766081943191920563893585679896423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139939484353335837953/50000000000000000000)
  centralHi := (279878968706671675907/100000000000000000000)
  directionLo := (35527304537857919311/12500000000000000000)
  directionHi := (284218436302863354489/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree034.table
  base := (-1938462742597951038215284505062282019559/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-27775911966073312432493983915340000000000000)
      constant := (281975859544485220346674634124855734896019005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree034.table
  base := (-4846291847987757331444674541655446917299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10285000000000000000000000000000000000000000
      center := (28248)
      previous := (0)
      next := (21120)
      square := (703830230531658025683316992255000000000000)
      linear := (-29836954499036618560919853478390000000000000)
      constant := (304110364886080829022211280590294745691115957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35527304537857919311/12500000000000000000)
  centralHi := (284218436302863354489/100000000000000000000)
  directionLo := (36061579698954598739/12500000000000000000)
  directionHi := (288492637591636789913/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree035.table
  base := (-7694662573630886566070067848859831451/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (39432)
      previous := (0)
      next := (29760)
      square := (986457245805916425884785069845000000000000)
      linear := (-42788217067985529306201053479500000000000000)
      constant := (447134743204335287346237602987210691204229375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree035.table
  base := (-9618542655126218237337678071045576877583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-1041841847391567725161498624873000000000000000)
      constant := (10930640793643546711847751206627857222167800073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36061579698954598739/12500000000000000000)
  centralHi := (288492637591636789913/100000000000000000000)
  directionLo := (58540886346113406079/20000000000000000000)
  directionHi := (73176107932641757599/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree036.table
  base := (-4753727066973683830089933272338260922351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (13144)
      previous := (0)
      next := (9920)
      square := (328819081935305475294928356615000000000000)
      linear := (-14637522062287029987887043695330000000000000)
      constant := (157333210030103180272461111024122931253620689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree036.table
  base := (-4753812158280297498526754459825858070643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (480216)
      previous := (0)
      next := (359040)
      square := (11965113919038186436616388868335000000000000)
      linear := (-534613620907945209625861115740370000000000000)
      constant := (5769244230524720815591905751929509569127684933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58540886346113406079/20000000000000000000)
  centralHi := (73176107932641757599/25000000000000000000)
  directionLo := (74214118756494401519/25000000000000000000)
  directionHi := (296856475025977606077/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree037.table
  base := (-9359771991088507259782566146098051181951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-30024610203824433747414139128320000000000000)
      constant := (331705555929628780052763038513569772814145089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree037.table
  base := (-9359906947936162301486721883701116453363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-1096612636240213113341945838088480000000000000)
      constant := (12163292671402717220220761569141385658742349253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74214118756494401519/25000000000000000000)
  centralHi := (296856475025977606077/100000000000000000000)
  directionLo := (300951240527404300753/100000000000000000000)
  directionHi := (150475620263702150377/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree038.table
  base := (-9175343960562602902936058067759693770761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (78864)
      previous := (0)
      next := (59520)
      square := (1972914491611832851769570139690000000000000)
      linear := (-92322528849224422557162572597940000000000000)
      constant := (1047621529991306389953316654616008802858896037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree038.table
  base := (-9175450905081050016417773912560918072689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-1123998030664535807432169444696220000000000000)
      constant := (12805051314120419605682124603412537255916138359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300951240527404300753/100000000000000000000)
  centralHi := (150475620263702150377/50000000000000000000)
  directionLo := (15249551762684555017/5000000000000000000)
  directionHi := (304991035253691100341/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree039.table
  base := (-8954218044790417472184339726546688324759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-31523742362325181290694242603640000000000000)
      constant := (367171236132300057209824979605918632519906601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree039.table
  base := (-8954302732842411637345128242625987560473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-1151383425088858501522393051303960000000000000)
      constant := (13463762761575788676983814845758981840997819663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15249551762684555017/5000000000000000000)
  centralHi := (304991035253691100341/100000000000000000000)
  directionLo := (308978015391472372497/100000000000000000000)
  directionHi := (154489007695736186249/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree040.table
  base := (-2174107826818728985860553079669663978193/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2402500000000000000000000000000000000000000
      center := (6572)
      previous := (0)
      next := (4960)
      square := (164409540967652737647464178307500000000000)
      linear := (-8068327110393888765583573585325000000000000)
      constant := (96399424679299053096766799691437452916956527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree040.table
  base := (-4348249163354823162058087275307897452651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (480216)
      previous := (0)
      next := (359040)
      square := (11965113919038186436616388868335000000000000)
      linear := (-589384409756590597806308328955850000000000000)
      constant := (7069712879269727817452564463287758133978247181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308978015391472372497/100000000000000000000)
  centralHi := (154489007695736186249/50000000000000000000)
  directionLo := (312914199750327132773/100000000000000000000)
  directionHi := (156457099875163566387/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree041.table
  base := (-4201006183254981067531572207891177077193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (39432)
      previous := (0)
      next := (29760)
      square := (986457245805916425884785069845000000000000)
      linear := (-49534311781238893250961519118440000000000000)
      constant := (606729805374126988580091788581244736486452581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree041.table
  base := (-4201032685234949760084584252380397773681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (480216)
      previous := (0)
      next := (359040)
      square := (11965113919038186436616388868335000000000000)
      linear := (-603077106968751944851420132259720000000000000)
      constant := (7416019668468533895217237241699894870252149111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312914199750327132773/100000000000000000000)
  centralHi := (156457099875163566387/50000000000000000000)
  directionLo := (9900046303529772653/3125000000000000000)
  directionHi := (316801481712952724897/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree042.table
  base := (-8070983321179502559093663242519343489307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-33772440600076302605614397816620000000000000)
      constant := (423837729492130124610730247808258910906775973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree042.table
  base := (-8071025215753600005658594524623436097239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-1233539608361826583793063871127180000000000000)
      constant := (15541602750123460679558629350564123063115649409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9900046303529772653/3125000000000000000)
  centralHi := (316801481712952724897/100000000000000000000)
  directionLo := (160320819940562469117/50000000000000000000)
  directionHi := (64128327976224987647/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree043.table
  base := (-7703361236383184536453977716833624909333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-34522006679326676377254449554280000000000000)
      constant := (443651260045771847983670044257892886462130987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree043.table
  base := (-1925848582823726002319768862001815251053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87422500000000000000000000000000000000000000
      center := (240108)
      previous := (0)
      next := (179520)
      square := (5982556959519093218308194434167500000000000)
      linear := (-315231250696537319470821869433730000000000000)
      constant := (4067028855550867398279092815513341022485927643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160320819940562469117/50000000000000000000)
  centralHi := (64128327976224987647/20000000000000000000)
  directionLo := (162218173793653358663/50000000000000000000)
  directionHi := (324436347587306717327/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree044.table
  base := (-7299159291007403942026638379536112368199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (78864)
      previous := (0)
      next := (59520)
      square := (1972914491611832851769570139690000000000000)
      linear := (-105814718275731150446683503875820000000000000)
      constant := (1391781347736300008209355352000037388042482283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree044.table
  base := (-729918542043664335607209139503693274089/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (43656)
      previous := (0)
      next := (32640)
      square := (1087737629003471494237853533485000000000000)
      linear := (-58559563509566907816977776561030000000000000)
      constant := (773253495861540865682628395433948795408355345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (162218173793653358663/50000000000000000000)
  centralHi := (324436347587306717327/100000000000000000000)
  directionLo := (32818718141622532291/10000000000000000000)
  directionHi := (328187181416225322911/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree045.table
  base := (-1714596915878648185680371775072351442929/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2402500000000000000000000000000000000000000
      center := (6572)
      previous := (0)
      next := (4960)
      square := (164409540967652737647464178307500000000000)
      linear := (-9005284709456855980133638257400000000000000)
      constant := (121166321827403047937218777249467970263345231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree045.table
  base := (-3429204141418451904731540775881704124979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (480216)
      previous := (0)
      next := (359040)
      square := (11965113919038186436616388868335000000000000)
      linear := (-657847895817397333031867345475200000000000000)
      constant := (8885993433845252717100882740073817688453609349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32818718141622532291/10000000000000000000)
  centralHi := (328187181416225322911/100000000000000000000)
  directionLo := (331895628859527287799/100000000000000000000)
  directionHi := (1659478144297636439/500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree046.table
  base := (-127621084315917628242942541745736614567/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (13144)
      previous := (0)
      next := (9920)
      square := (328819081935305475294928356615000000000000)
      linear := (-18385352458538898846087302383630000000000000)
      constant := (252932883341515519317901075784198677835027825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree046.table
  base := (-3190535239468937458778951652267140973719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (480216)
      previous := (0)
      next := (359040)
      square := (11965113919038186436616388868335000000000000)
      linear := (-671540593029558680076979148779070000000000000)
      constant := (9274672517016092917180239938456230347290020289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331895628859527287799/100000000000000000000)
  centralHi := (1659478144297636439/500000000000000000)
  directionLo := (335563095208927546629/100000000000000000000)
  directionHi := (33556309520892754663/10000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree047.table
  base := (-1173433004225742461158981797959909513729/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (78864)
      previous := (0)
      next := (59520)
      square := (1972914491611832851769570139690000000000000)
      linear := (-112560812988984514391443969514760000000000000)
      constant := (1582585644587810763880817171212917904359596465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree047.table
  base := (-5867177842348042357528736402717347709777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-1370466580483440054244181904165880000000000000)
      constant := (19343651203983485109848933936185707067936808087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335563095208927546629/100000000000000000000)
  centralHi := (33556309520892754663/10000000000000000000)
  directionLo := (42398863722305854997/12500000000000000000)
  directionHi := (339190909778446839977/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree048.table
  base := (-42533798174252786078292334071367536373/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-38269837075578545235454708242580000000000000)
      constant := (549653627339059798886772863203596974693193375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree048.table
  base := (-265836743747561610312004084817905667223/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87422500000000000000000000000000000000000000
      center := (240108)
      previous := (0)
      next := (179520)
      square := (5982556959519093218308194434167500000000000)
      linear := (-349462993726940687083601377693405000000000000)
      constant := (5038726305029506936646313231935533283614394565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42398863722305854997/12500000000000000000)
  centralHi := (339190909778446839977/100000000000000000000)
  directionLo := (68556066306772635553/20000000000000000000)
  directionHi := (171390165766931588883/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree049.table
  base := (-945947418740794529064599171356010859909/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-39019403154828919007094759980240000000000000)
      constant := (572241000627862265945579437352164367818137255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree049.table
  base := (-472974505158605160033674315199880466813/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (480216)
      previous := (0)
      next := (359040)
      square := (11965113919038186436616388868335000000000000)
      linear := (-712618684666042721212314558690680000000000000)
      constant := (10491553480462091245804052350837861899780081015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68556066306772635553/20000000000000000000)
  centralHi := (171390165766931588883/50000000000000000000)
  directionLo := (86583138549243468439/25000000000000000000)
  directionHi := (346332554196973873757/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree050.table
  base := (-4106204789483198157762815657514260081701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (78864)
      previous := (0)
      next := (59520)
      square := (1972914491611832851769570139690000000000000)
      linear := (-119306907702237878336204435153700000000000000)
      constant := (1785871996107173600759357655119386388184456017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree050.table
  base := (-4106211054994306365641041150009922087881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-1452622763756408136514852723989100000000000000)
      constant := (21828256332589151136994308536605303034508889311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86583138549243468439/25000000000000000000)
  centralHi := (346332554196973873757/100000000000000000000)
  directionLo := (174924355441669797441/50000000000000000000)
  directionHi := (349848710883339594883/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree051.table
  base := (-3446130025921518378193445608411888994773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-40518535313329666550374863455560000000000000)
      constant := (618802619480349645727967172152646174676023147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree051.table
  base := (-43076686962486591694253876655743818923/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1285625000000000000000000000000000000000000
      center := (3531)
      previous := (0)
      next := (2640)
      square := (87978778816457253210414624031875000000000)
      linear := (-5441206463899745700753957097782500000000000)
      constant := (83420416406850579464820377700096299822376945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174924355441669797441/50000000000000000000)
  centralHi := (349848710883339594883/100000000000000000000)
  directionLo := (353329878324589508567/100000000000000000000)
  directionHi := (44166234790573688571/12500000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree052.table
  base := (-2749514478857613531470331856698722005371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-41268101392580040322014915193220000000000000)
      constant := (642776861351256630674037214943232528152838469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree052.table
  base := (-1374759179109291137293158435202762490573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (480216)
      previous := (0)
      next := (359040)
      square := (11965113919038186436616388868335000000000000)
      linear := (-753696776302526762347649968602290000000000000)
      constant := (11784698847587383865429998281460634598467152763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353329878324589508567/100000000000000000000)
  centralHi := (44166234790573688571/12500000000000000000)
  directionLo := (71355416143977162781/20000000000000000000)
  directionHi := (178388540359942906953/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree053.table
  base := (-2016359444979314772515697708429765991229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (78864)
      previous := (0)
      next := (59520)
      square := (1972914491611832851769570139690000000000000)
      linear := (-126053002415491242280964900792640000000000000)
      constant := (2001640169206985448054347270443306984647286793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree053.table
  base := (-1008181247904556315614107871215673443099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (480216)
      previous := (0)
      next := (359040)
      square := (11965113919038186436616388868335000000000000)
      linear := (-767389473514688109392761771906160000000000000)
      constant := (12232694793430639433335025771312924115368271069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71355416143977162781/20000000000000000000)
  centralHi := (178388540359942906953/50000000000000000000)
  directionLo := (72038258651119158901/20000000000000000000)
  directionHi := (180095646627797897253/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree054.table
  base := (-623332964076051085868366374762122135499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (13144)
      previous := (0)
      next := (9920)
      square := (328819081935305475294928356615000000000000)
      linear := (-21383616775540393932647509334270000000000000)
      constant := (346056101834425237706270744287093600627785461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree054.table
  base := (-1246668326549736355848088676409267119601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-1562164341453698912875747150420060000000000000)
      constant := (25378328904265278549354396650604164338094672631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72038258651119158901/20000000000000000000)
  centralHi := (180095646627797897253/50000000000000000000)
  directionLo := (363573445327451409577/100000000000000000000)
  directionHi := (181786722663725704789/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree055.table
  base := (-440434706072640714426017148133293562469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-43516799630331161636935070406200000000000000)
      constant := (717473302403456113806448240680893904886467291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree055.table
  base := (-110109147729243842242864741524606841583/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7947500000000000000000000000000000000000000
      center := (21828)
      previous := (0)
      next := (16320)
      square := (543868814501735747118926766742500000000000)
      linear := (-36126130360864127431044789932450000000000000)
      constant := (597913991397569165542594883245380774850607643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363573445327451409577/100000000000000000000)
  centralHi := (181786722663725704789/50000000000000000000)
  directionLo := (366924423495367762271/100000000000000000000)
  directionHi := (11466388234230242571/3125000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree056.table
  base := (10058340456692487547266240457154817287/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3603750000000000000000000000000000000000000
      center := (9858)
      previous := (0)
      next := (7440)
      square := (246614311451479106471196267461250000000000)
      linear := (-16599887141093075778215670803947500000000000)
      constant := (278736257010001509201042644938769886691192105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree056.table
  base := (402332137502322107783046620776014197469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-1616935130302344301056194363635540000000000000)
      constant := (27255049718486814574767604419763036440471293461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366924423495367762271/100000000000000000000)
  centralHi := (11466388234230242571/3125000000000000000)
  directionLo := (23140317137346315901/6250000000000000000)
  directionHi := (370245074197541054417/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree057.table
  base := (1281638576846796153535894143535132237841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-45015931788831909180215173881520000000000000)
      constant := (769582352088724948048483970198307262080565201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree057.table
  base := (256327482780689948119521124872419978619/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-1644320524726666995146417970243280000000000000)
      constant := (28218831179692216646247409887904448271161639055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23140317137346315901/6250000000000000000)
  centralHi := (370245074197541054417/100000000000000000000)
  directionLo := (373536206247369508439/100000000000000000000)
  directionHi := (9338405156184237711/2500000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree058.table
  base := (1098739902964992660588039253649696342539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (13144)
      previous := (0)
      next := (9920)
      square := (328819081935305475294928356615000000000000)
      linear := (-22882748934041141475927612809590000000000000)
      constant := (398165151120034936158539682862117358185179979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree058.table
  base := (1098739446437190083142260799346139847173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (480216)
      previous := (0)
      next := (359040)
      square := (11965113919038186436616388868335000000000000)
      linear := (-835852959575494844618320788425510000000000000)
      constant := (14599779996515268156725140355100975164315792637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373536206247369508439/100000000000000000000)
  centralHi := (9338405156184237711/2500000000000000000)
  directionLo := (188399296567033433093/50000000000000000000)
  directionHi := (376798593134066866187/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree059.table
  base := (3149857022378701481657606850579748030273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (78864)
      previous := (0)
      next := (59520)
      square := (1972914491611832851769570139690000000000000)
      linear := (-139545191841997970170485832070520000000000000)
      constant := (2470621606625827907622447902382011413571277059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree059.table
  base := (3149856305729159096472091435043557616633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-1699091313575312383326865183458760000000000000)
      constant := (30197236149106094440866146800646608166296039377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188399296567033433093/50000000000000000000)
  centralHi := (376798593134066866187/100000000000000000000)
  directionLo := (5938015236648571783/1562500000000000000)
  directionHi := (380032975145508594113/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree060.table
  base := (2069385002678093170558629739991882802817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (13144)
      previous := (0)
      next := (9920)
      square := (328819081935305475294928356615000000000000)
      linear := (-23632315013291515247567664547250000000000000)
      constant := (425606525891059556999645610641132199373507137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree060.table
  base := (2069384721512803137957572197783080290061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (480216)
      previous := (0)
      next := (359040)
      square := (11965113919038186436616388868335000000000000)
      linear := (-863238353999817538708544395033250000000000000)
      constant := (15605929820297453713574669891853276534663143109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5938015236648571783/1562500000000000000)
  centralHi := (380032975145508594113/100000000000000000000)
  directionLo := (191620030664908205183/50000000000000000000)
  directionHi := (383240061329816410367/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree061.table
  base := (516421858220012401336211116998827206087/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (13144)
      previous := (0)
      next := (9920)
      square := (328819081935305475294928356615000000000000)
      linear := (-24007098052916702133387690416080000000000000)
      constant := (439673925397335410562936863023644364725248035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree061.table
  base := (1032843628216182436157978648894131285331/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-1753862102423957771507312396674240000000000000)
      constant := (32243430461773151106061265643533464384583698695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191620030664908205183/50000000000000000000)
  centralHi := (383240061329816410367/100000000000000000000)
  directionLo := (193210265655202786827/50000000000000000000)
  directionHi := (77284106262081114731/20000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree062.table
  base := (1245240523502495535581118100614878926263/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 930000000000000000000000000000000000000000
      center := (2544)
      previous := (0)
      next := (1920)
      square := (63642402955220414573211939990000000000000)
      linear := (-4719073759846817229524074119660000000000000)
      constant := (87865638624143249406717021286145918700712295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree062.table
  base := (6226202271570259610333575781035335481331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-1781247496848280465597536003281980000000000000)
      constant := (33291948608153434944908451348730304646446663739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193210265655202786827/50000000000000000000)
  centralHi := (77284106262081114731/20000000000000000000)
  directionLo := (194787518483828183539/50000000000000000000)
  directionHi := (389575036967656367079/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree063.table
  base := (732472200473329575646729788545501875511/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (13144)
      previous := (0)
      next := (9920)
      square := (328819081935305475294928356615000000000000)
      linear := (-24756664132167075905027742153740000000000000)
      constant := (468502148322071634381585119500646136511830355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree063.table
  base := (7324721733502988723558715906916323493901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-1808632891272603159687759609889720000000000000)
      constant := (34357414076204216559711405847614086916258224069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194787518483828183539/50000000000000000000)
  centralHi := (389575036967656367079/100000000000000000000)
  directionLo := (15708168159959862907/4000000000000000000)
  directionHi := (98176050999749143169/25000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree064.table
  base := (8459776659632396427235233875023297383571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-50262894343584525581695536045140000000000000)
      constant := (966525943297714691076395451716777388785611731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree064.table
  base := (8459776447032288004832737338380704912667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-1836018285696925853777983216497460000000000000)
      constant := (35439826863133332798579973580118954870091052323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15708168159959862907/4000000000000000000)
  centralHi := (98176050999749143169/25000000000000000000)
  directionLo := (79161726673594028287/20000000000000000000)
  directionHi := (98952158341992535359/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree065.table
  base := (9631366515281878480250185919049318652629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (78864)
      previous := (0)
      next := (59520)
      square := (1972914491611832851769570139690000000000000)
      linear := (-153037381268504698060006763348400000000000000)
      constant := (2989529617037630393238942164520369185675529407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree065.table
  base := (9631366348678901503422064446893325244433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-1863403680121248547868206823105200000000000000)
      constant := (36539186966720977560172952140090662690472577577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79161726673594028287/20000000000000000000)
  centralHi := (98952158341992535359/25000000000000000000)
  directionLo := (79777780530359428443/20000000000000000000)
  directionHi := (49861112831474642777/12500000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree066.table
  base := (2167898303634405979033073439363669575249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-51762026502085273124975639520460000000000000)
      constant := (1026956083737206755521372786236622432309071445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree066.table
  base := (10839491387645353139389053058999562256097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (87312)
      previous := (0)
      next := (65280)
      square := (2175475258006942988475707066970000000000000)
      linear := (-171889915867779203814402766337540000000000000)
      constant := (3423226762290073991222818368038879608412132363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79777780530359428443/20000000000000000000)
  centralHi := (49861112831474642777/12500000000000000000)
  directionLo := (50243195911997873339/12500000000000000000)
  directionHi := (401945567295982986713/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree067.table
  base := (6042075812605059413500652536308922963879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (13144)
      previous := (0)
      next := (9920)
      square := (328819081935305475294928356615000000000000)
      linear := (-26255796290667823448307845629060000000000000)
      constant := (528932288715146224549273186351677874968287719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree067.table
  base := (6042075761485612248735188561410005087333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (480216)
      previous := (0)
      next := (359040)
      square := (11965113919038186436616388868335000000000000)
      linear := (-959087234484946968024327018160340000000000000)
      constant := (19394374558555248478425390028210911467898947677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50243195911997873339/12500000000000000000)
  centralHi := (401945567295982986713/100000000000000000000)
  directionLo := (404979161783695086267/100000000000000000000)
  directionHi := (101244790445923771567/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree068.table
  base := (13365346801400931978960207331327445210141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (78864)
      previous := (0)
      next := (59520)
      square := (1972914491611832851769570139690000000000000)
      linear := (-159783475981758062004767228987340000000000000)
      constant := (3267706060174510435498836407764777024540836503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree068.table
  base := (2673069344267422603037844978148935790413/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20570000000000000000000000000000000000000000
      center := (56496)
      previous := (0)
      next := (42240)
      square := (1407660461063316051366633984510000000000000)
      linear := (-114444697846718625302286920172260000000000000)
      constant := (2349350068312640031303825560827701804604397705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (404979161783695086267/100000000000000000000)
  centralHi := (101244790445923771567/25000000000000000000)
  directionLo := (203995100363439470387/50000000000000000000)
  directionHi := (16319608029075157631/4000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree069.table
  base := (3670769254513442375214141381943683378787/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2402500000000000000000000000000000000000000
      center := (6572)
      previous := (0)
      next := (4960)
      square := (164409540967652737647464178307500000000000)
      linear := (-13502681184959098609973948683360000000000000)
      constant := (280267102898317020292135450568880379727014307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree069.table
  base := (14683076955368921270752696506607684190543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-1972945257818539324229101249536160000000000000)
      constant := (41106100516846719816651089566304734108459098167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203995100363439470387/50000000000000000000)
  centralHi := (16319608029075157631/4000000000000000000)
  directionLo := (41097917988542151951/10000000000000000000)
  directionHi := (410979179885421519511/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree070.table
  base := (16037342251395999309630012113102769532171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-54760290819086768211535846471100000000000000)
      constant := (1153363752012740757673514358550691761520416331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree070.table
  base := (641493688093123037239843723896280280021/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-2000330652242862018319324856143900000000000000)
      constant := (42290197182910869639421508798233225627801358725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41097917988542151951/10000000000000000000)
  centralHi := (410979179885421519511/100000000000000000000)
  directionLo := (25871661070004849911/6250000000000000000)
  directionHi := (413946577120077598577/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree071.table
  base := (4357035620375149845289334686299698282431/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (19716)
      previous := (0)
      next := (14880)
      square := (493228622902958212942392534922500000000000)
      linear := (-41632392673752856487381923656570000000000000)
      constant := (889591030973078729887010551147749530148248573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree071.table
  base := (8714071221549726518508926507958729023773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (480216)
      previous := (0)
      next := (359040)
      square := (11965113919038186436616388868335000000000000)
      linear := (-1013858023333592356204774231375820000000000000)
      constant := (21745620579419446615378731760307293795232318037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25871661070004849911/6250000000000000000)
  centralHi := (413946577120077598577/100000000000000000000)
  directionLo := (416892853284345762663/100000000000000000000)
  directionHi := (52111606660543220333/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree072.table
  base := (18855477691456213328950879453925355494741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-56259422977587515754815949946420000000000000)
      constant := (1219341279431108914208626284217142266630446101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree072.table
  base := (18855477661408973038041925219091394474457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-2055101441091507406499772069359380000000000000)
      constant := (44709232444061702302847866004524486973377286833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (416892853284345762663/100000000000000000000)
  centralHi := (52111606660543220333/12500000000000000000)
  directionLo := (419818453060007513859/100000000000000000000)
  directionHi := (20990922653000375693/5000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree073.table
  base := (10159673933362266204342190233035184379363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (13144)
      previous := (0)
      next := (9920)
      square := (328819081935305475294928356615000000000000)
      linear := (-28504494528418944763228000842040000000000000)
      constant := (626511733199890633024026738367531812188567843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree073.table
  base := (20319347843218395648466093454193145518207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-2082486835515830100589995675967120000000000000)
      constant := (45944171038088393631145492349821010105626180583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (419818453060007513859/100000000000000000000)
  centralHi := (20990922653000375693/5000000000000000000)
  directionLo := (84544761148123760727/20000000000000000000)
  directionHi := (105680951435154700909/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree074.table
  base := (5454938248660598053885846089633079440011/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (19716)
      previous := (0)
      next := (14880)
      square := (493228622902958212942392534922500000000000)
      linear := (-43318916352066197473572040066305000000000000)
      constant := (965375951643464545780951714125372168025551713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree074.table
  base := (21819752976256848642573162115291950035493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-2109872229940152794680219282574860000000000000)
      constant := (47196056940489867084789237943360364200791154717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84544761148123760727/20000000000000000000)
  centralHi := (105680951435154700909/25000000000000000000)
  directionLo := (212804662983431306277/50000000000000000000)
  directionHi := (85121865193372522511/20000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree075.table
  base := (5839173266008920279307960568592548283557/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2402500000000000000000000000000000000000000
      center := (6572)
      previous := (0)
      next := (4960)
      square := (164409540967652737647464178307500000000000)
      linear := (-14627030303834659267434026289850000000000000)
      constant := (330443671698721244477409051890479938900498277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree075.table
  base := (23356693049657881527628594908338629768667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-2137257624364475488770442889182600000000000000)
      constant := (48464890150886133756498668785475943544380516323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212804662983431306277/50000000000000000000)
  centralHi := (85121865193372522511/20000000000000000000)
  directionLo := (428475414417328972207/100000000000000000000)
  directionHi := (26779713401083060763/6250000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree076.table
  base := (12465084032459826648417566920923368118127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (13144)
      previous := (0)
      next := (9920)
      square := (328819081935305475294928356615000000000000)
      linear := (-29628843647294505420688078448530000000000000)
      constant := (678421860100491337961550146371047356761520047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree076.table
  base := (12465084026838986713062787989059595564153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (480216)
      previous := (0)
      next := (359040)
      square := (11965113919038186436616388868335000000000000)
      linear := (-1082321509394399091430333247895170000000000000)
      constant := (24875335334468236232354124516263384997282866257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428475414417328972207/100000000000000000000)
  centralHi := (26779713401083060763/6250000000000000000)
  directionLo := (215661229228990354921/50000000000000000000)
  directionHi := (431322458457980709843/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree077.table
  base := (13270088994133013310716763648346145638991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (39432)
      previous := (0)
      next := (29760)
      square := (986457245805916425884785069845000000000000)
      linear := (-90010880060759076919524312952080000000000000)
      constant := (2088562553601354463927888018223336937877211053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree077.table
  base := (26540177979477929312037924457922809438199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (87312)
      previous := (0)
      next := (65280)
      square := (2175475258006942988475707066970000000000000)
      linear := (-199275310292101897904626372945280000000000000)
      constant := (4641218044939253218050260833253166611204034621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215661229228990354921/50000000000000000000)
  centralHi := (431322458457980709843/100000000000000000000)
  directionLo := (217075416376642697151/50000000000000000000)
  directionHi := (434150832753285394303/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree078.table
  base := (28186722825821713862181213860885300542397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-60756819453089758384656260372380000000000000)
      constant := (1428368633386714661169190543546630773821243517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree078.table
  base := (28186722818952843867944990572624134050939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-2219413807637443571041113709005820000000000000)
      constant := (52373073626788652123987646483263773343627285891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217075416376642697151/50000000000000000000)
  centralHi := (434150832753285394303/100000000000000000000)
  directionLo := (218480449920871568033/50000000000000000000)
  directionHi := (436960899841743136067/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree079.table
  base := (7467450642491871436384522652401676207469/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2402500000000000000000000000000000000000000
      center := (6572)
      previous := (0)
      next := (4960)
      square := (164409540967652737647464178307500000000000)
      linear := (-15376596383085033039074078027510000000000000)
      constant := (366206128287773913060755962006140510835377709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree079.table
  base := (29869802564599585968022168427315096672601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-2246799202061766265131337315613560000000000000)
      constant := (53709696066044695648673620341424551615544184369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218480449920871568033/50000000000000000000)
  centralHi := (436960899841743136067/100000000000000000000)
  directionLo := (439753010678313113649/100000000000000000000)
  directionHi := (8795060213566262273/2000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree080.table
  base := (15794708606803764023404440710983304775899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (39432)
      previous := (0)
      next := (29760)
      square := (986457245805916425884785069845000000000000)
      linear := (-93383927417385758891904545771550000000000000)
      constant := (2252614012530840307555239647845764867668916817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree080.table
  base := (7897354302353320366430284573523161253477/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87422500000000000000000000000000000000000000
      center := (240108)
      previous := (0)
      next := (179520)
      square := (5982556959519093218308194434167500000000000)
      linear := (-568546149121522239805390230555325000000000000)
      constant := (13765816452963740632145035636925531425872837213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (439753010678313113649/100000000000000000000)
  centralHi := (8795060213566262273/2000000000000000000)
  directionLo := (110631876286509095933/25000000000000000000)
  directionHi := (442527505146036383733/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree081.table
  base := (1333822670003316466482092918575599817697/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-63005517690840879699576415585360000000000000)
      constant := (1539123118988709088681710741100908785620170425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree081.table
  base := (16672783373403109504607055712234728239149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (480216)
      previous := (0)
      next := (359040)
      square := (11965113919038186436616388868335000000000000)
      linear := (-1150784995455205826655892264414520000000000000)
      constant := (28216891431994543542722573578675321211794801381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110631876286509095933/25000000000000000000)
  centralHi := (442527505146036383733/100000000000000000000)
  directionLo := (89056942507793281823/20000000000000000000)
  directionHi := (111321178134741602279/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree082.table
  base := (35138251173103582674607933964953425041/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1201250000000000000000000000000000000000000
      center := (3286)
      previous := (0)
      next := (2480)
      square := (82204770483826368823732089153750000000000)
      linear := (-7969385471261406683902058415377500000000000)
      constant := (197120730631187195170470756641680030183050125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree082.table
  base := (7027650234108821043797621904093131550509/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-2328955385334734347402008135436780000000000000)
      constant := (57821247222229062314080444832268043585948746105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89056942507793281823/20000000000000000000)
  centralHi := (111321178134741602279/25000000000000000000)
  directionLo := (224012476009174899447/50000000000000000000)
  directionHi := (89604990403669959779/20000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree083.table
  base := (36967470476694705688950697169588683470917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (78864)
      previous := (0)
      next := (59520)
      square := (1972914491611832851769570139690000000000000)
      linear := (-193513949548024881728569557182040000000000000)
      constant := (4845812559591551418803678479240834174446653711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree083.table
  base := (36967470474695753679908513874398025940187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-2356340779759057041492231742044520000000000000)
      constant := (59225658886367480556735193090865354569102399203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224012476009174899447/50000000000000000000)
  centralHi := (89604990403669959779/20000000000000000000)
  directionLo := (225374266521923111429/50000000000000000000)
  directionHi := (450748533043846222859/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree084.table
  base := (38833224655154140607660369883858215206277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-65254215928592001014496570798340000000000000)
      constant := (1654038143426288066760470207712067744813232197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree084.table
  base := (19416612326796592716236998417945698214767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (480216)
      previous := (0)
      next := (359040)
      square := (11965113919038186436616388868335000000000000)
      linear := (-1191863087091689867791227674326130000000000000)
      constant := (30323508928103069128587295003268303120872187223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (225374266521923111429/50000000000000000000)
  centralHi := (450748533043846222859/100000000000000000000)
  directionLo := (453455755781436763747/100000000000000000000)
  directionHi := (113363938945359190937/25000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree085.table
  base := (2036775685150928212386638579739853875899/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2402500000000000000000000000000000000000000
      center := (6572)
      previous := (0)
      next := (4960)
      square := (164409540967652737647464178307500000000000)
      linear := (-16500945501960593696534155634000000000000000)
      constant := (423316928932890022315657794888962497873694695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree085.table
  base := (5091939212724975951408372856799935141479/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2571250000000000000000000000000000000000000
      center := (7062)
      previous := (0)
      next := (5280)
      square := (175957557632914506420829248063750000000000)
      linear := (-17728761533880164924063815847500000000000000)
      constant := (456509736261433258819763591028343716586022303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (453455755781436763747/100000000000000000000)
  centralHi := (113363938945359190937/25000000000000000000)
  directionLo := (45614691148954271059/10000000000000000000)
  directionHi := (456146911489542710591/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree086.table
  base := (21337168807518156443517059114542914470833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (39432)
      previous := (0)
      next := (29760)
      square := (986457245805916425884785069845000000000000)
      linear := (-100130022130639122836665011410490000000000000)
      constant := (2599439355161929537406107763175747222419411539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree086.table
  base := (42674337614084868315671976014328497425071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-2438496963032025123762902561867740000000000000)
      constant := (63540577712230921220462344934147373226457307799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45614691148954271059/10000000000000000000)
  centralHi := (456146911489542710591/100000000000000000000)
  directionLo := (458822282884760733633/100000000000000000000)
  directionHi := (229411141442380366817/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree087.table
  base := (8929939277229091590370715222748924276637/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-67502914166343122329416726011320000000000000)
      constant := (1773113706550602360425456084236278581149240785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree087.table
  base := (44649696385402795753618026846287998659827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-2465882357456347817853126168475480000000000000)
      constant := (65012778598057693720101150637419375025135490363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (458822282884760733633/100000000000000000000)
  centralHi := (229411141442380366817/50000000000000000000)
  directionLo := (11537053612212860313/2500000000000000000)
  directionHi := (461482144488514412521/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree088.table
  base := (46661590011455963902746771371306854249677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-68252480245593496101056777748980000000000000)
      constant := (1813730125054808771573377862616945886933939597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree088.table
  base := (46661590010876345968745537463502745076419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (87312)
      previous := (0)
      next := (65280)
      square := (2175475258006942988475707066970000000000000)
      linear := (-226660704716424591994849979553020000000000000)
      constant := (6045629708078608032226756973742555226597936001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11537053612212860313/2500000000000000000)
  centralHi := (461482144488514412521/100000000000000000000)
  directionLo := (18565070518233009239/4000000000000000000)
  directionHi := (3625990335592384617/781250000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree089.table
  base := (48710018486235037569832122194169189505469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (78864)
      previous := (0)
      next := (59520)
      square := (1972914491611832851769570139690000000000000)
      linear := (-207006138974531609618090488459920000000000000)
      constant := (5564426476848072132434742931426179773344267127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree089.table
  base := (9742003697156545495805138836223503124551/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-2520653146304993206033573381690960000000000000)
      constant := (68008022284486753828306807569647868403812119595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18565070518233009239/4000000000000000000)
  centralHi := (3625990335592384617/781250000000000000)
  directionLo := (466756397387317525581/100000000000000000000)
  directionHi := (233378198693658762791/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree090.table
  base := (5079498180589497919570129575434047339649/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (13144)
      previous := (0)
      next := (9920)
      square := (328819081935305475294928356615000000000000)
      linear := (-34875806202047121822168440612150000000000000)
      constant := (948174904114919699336598009981960597467013445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree090.table
  base := (3174686362846378715572022164344531453163/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21855625000000000000000000000000000000000000
      center := (60027)
      previous := (0)
      next := (44880)
      square := (1495639239879773304577048608541875000000000)
      linear := (-159252408795582243757737311768668750000000000)
      constant := (4345691567797733518038048295020963920385656947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466756397387317525581/100000000000000000000)
  centralHi := (233378198693658762791/50000000000000000000)
  directionLo := (11734282490637267479/2500000000000000000)
  directionHi := (469371299625490699161/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree091.table
  base := (26458239982991500374260865272964931737523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (13144)
      previous := (0)
      next := (9920)
      square := (328819081935305475294928356615000000000000)
      linear := (-35250589241672308707988466480980000000000000)
      constant := (969176536445987852929815949737684299399759603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree091.table
  base := (33072799978567290835030614783622713423/6250000000000000000000000000000000000)
  polynomial :=
    { denominator := 21855625000000000000000000000000000000000000
      center := (60027)
      previous := (0)
      next := (44880)
      square := (1495639239879773304577048608541875000000000)
      linear := (-160963995947102412138376287181652500000000000)
      constant := (4441940949346258743960336175337460891568888700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11734282490637267479/2500000000000000000)
  centralHi := (469371299625490699161/100000000000000000000)
  directionLo := (117992928634054394779/25000000000000000000)
  directionHi := (471971714536217579117/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree092.table
  base := (55074512962172597080694712277296589790523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (78864)
      previous := (0)
      next := (59520)
      square := (1972914491611832851769570139690000000000000)
      linear := (-213752233687784973562850954098860000000000000)
      constant := (5942455858794825582772138753726406068366077809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree092.table
  base := (11014902592391563223159419684109348256721/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-2602809329577961288304244201514180000000000000)
      constant := (72627992598664838130339220398637778995946383245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117992928634054394779/25000000000000000000)
  centralHi := (471971714536217579117/100000000000000000000)
  directionLo := (237278940138179744651/50000000000000000000)
  directionHi := (474557880276359489303/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree093.table
  base := (5726908079025614826770598045271692516017/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 155000000000000000000000000000000000000000
      center := (424)
      previous := (0)
      next := (320)
      square := (10607067159203402428868656665000000000000)
      linear := (-1161295332932989757407371555440000000000000)
      constant := (32641071747495070018048078563352112339982635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree093.table
  base := (5726908079008862380114345160044287342703/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (480216)
      previous := (0)
      next := (359040)
      square := (11965113919038186436616388868335000000000000)
      linear := (-1315097362001141991197233904060960000000000000)
      constant := (37100938655995412605252019347095808420434906035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237278940138179744651/50000000000000000000)
  centralHi := (474557880276359489303/100000000000000000000)
  directionLo := (119282507137081461687/25000000000000000000)
  directionHi := (477130028548325846749/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree094.table
  base := (14875045861534625793437331635771238030369/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2402500000000000000000000000000000000000000
      center := (6572)
      previous := (0)
      next := (4960)
      square := (164409540967652737647464178307500000000000)
      linear := (-18187469180273934682724272043735000000000000)
      constant := (516784139781824426550731498033996159747184609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree094.table
  base := (7437522930750981604619975569559226152289/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43711250000000000000000000000000000000000000
      center := (120054)
      previous := (0)
      next := (89760)
      square := (2991278479759546609154097217083750000000000)
      linear := (-332197514803325834560586426841207500000000000)
      constant := (9474088666171874969841569289395406579319394041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119282507137081461687/25000000000000000000)
  centralHi := (477130028548325846749/100000000000000000000)
  directionLo := (479688384842348385427/100000000000000000000)
  directionHi := (119922096210587096357/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree095.table
  base := (15441955231457837436786088741551122890761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (19716)
      previous := (0)
      next := (14880)
      square := (493228622902958212942392534922500000000000)
      linear := (-55124582100259584376902854934450000000000000)
      constant := (1583241713956689391220662566034079387294063963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree095.table
  base := (30883910462864734312291496892890864093463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (480216)
      previous := (0)
      next := (359040)
      square := (11965113919038186436616388868335000000000000)
      linear := (-1342482756425464685287457510668700000000000000)
      constant := (38700244325338987065572057548510625626484307647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479688384842348385427/100000000000000000000)
  centralHi := (119922096210587096357/25000000000000000000)
  directionLo := (120558292166796748241/25000000000000000000)
  directionHi := (96446633733437398593/20000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree096.table
  base := (64071993225448220449384984690079814316091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-74249008879596486274177191650260000000000000)
      constant := (2155303626785823892088348814784446701557763451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree096.table
  base := (4004499576585548896964741190702062618841/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21855625000000000000000000000000000000000000
      center := (60027)
      previous := (0)
      next := (44880)
      square := (1495639239879773304577048608541875000000000)
      linear := (-169521931704703254041571164246571250000000000)
      constant := (4939075954735244040290731895214580427718250929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120558292166796748241/25000000000000000000)
  centralHi := (96446633733437398593/20000000000000000000)
  directionLo := (48476459376993521277/10000000000000000000)
  directionHi := (484764593769935212771/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree097.table
  base := (6641270034120001442366160961803753904881/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (13144)
      previous := (0)
      next := (9920)
      square := (328819081935305475294928356615000000000000)
      linear := (-37499287479423430022908621693960000000000000)
      constant := (1100040291827185245830964070447052037512953205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree097.table
  base := (33206350170569041085473094767511793963227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (480216)
      previous := (0)
      next := (359040)
      square := (11965113919038186436616388868335000000000000)
      linear := (-1369868150849787379377681117276440000000000000)
      constant := (40333444602250169401846278177155784923100084963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48476459376993521277/10000000000000000000)
  centralHi := (484764593769935212771/100000000000000000000)
  directionLo := (243641434172774172059/50000000000000000000)
  directionHi := (487282868345548344119/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree098.table
  base := (68789942269390943717824003753669968252013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (78864)
      previous := (0)
      next := (59520)
      square := (1972914491611832851769570139690000000000000)
      linear := (-227244423114291701452371885376740000000000000)
      constant := (6735959467633022004378815097575590518470553479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree098.table
  base := (68789942269342664657438049863552567730711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-2767121696123897452845585841160620000000000000)
      constant := (82325510436758076524174191405576649740975232959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell167.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243641434172774172059/50000000000000000000)
  centralHi := (487282868345548344119/100000000000000000000)
  directionLo := (97957639047335086567/20000000000000000000)
  directionHi := (122447048809168858209/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree099.table
  base := (71203719006414830796383601651098300364471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-76497707117347607589097346863240000000000000)
      constant := (2291021343452268884869774978284235466650256631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree099.table
  base := (71203719006377198946290699701285330904743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (87312)
      previous := (0)
      next := (65280)
      square := (2175475258006942988475707066970000000000000)
      linear := (-254046099140747286085073586160760000000000000)
      constant := (7636461724764640271917426618948656066946177997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 99 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 99 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97957639047335086567/20000000000000000000)
  centralHi := (122447048809168858209/25000000000000000000)
  directionLo := (246140386062168992183/50000000000000000000)
  directionHi := (492280772124337984367/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree100.table
  base := (73654030548751700021681724547189765871513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-77247273196597981360737398600900000000000000)
      constant := (2337185146374772445304647987879849365002523993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree100.table
  base := (18413507637180592572856696562859303775701/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87422500000000000000000000000000000000000000
      center := (240108)
      previous := (0)
      next := (179520)
      square := (5982556959519093218308194434167500000000000)
      linear := (-705473121243135710256508263594025000000000000)
      constant := (21423398702834042821772370403234126993732488269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 100 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 100 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246140386062168992183/50000000000000000000)
  centralHi := (492280772124337984367/100000000000000000000)
  directionLo := (247380395854981338397/50000000000000000000)
  directionHi := (98952158341992535359/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree101.table
  base := (3045635075718584710863929074264517387283/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (78864)
      previous := (0)
      next := (59520)
      square := (1972914491611832851769570139690000000000000)
      linear := (-233990517827545065397132351015680000000000000)
      constant := (7151433693925645368660099804213605090688422225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree101.table
  base := (761408768929417608790129836637147713971/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87422500000000000000000000000000000000000000
      center := (240108)
      previous := (0)
      next := (179520)
      square := (5982556959519093218308194434167500000000000)
      linear := (-712319469849216383779064165245960000000000000)
      constant := (21850764488353323329408905061855402960246297475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 101 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 101 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247380395854981338397/50000000000000000000)
  centralHi := (98952158341992535359/20000000000000000000)
  directionLo := (248614220944621228707/50000000000000000000)
  directionHi := (99445688377848491483/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree102.table
  base := (78664258035696745174664124007895914760181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-78746405355098728904017502076220000000000000)
      constant := (2430899598250370995460449124685107974084533941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree102.table
  base := (15732851607135786872024304649644780946991/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20570000000000000000000000000000000000000000
      center := (56496)
      previous := (0)
      next := (42240)
      square := (1407660461063316051366633984510000000000000)
      linear := (-169215486695364013482734133387740000000000000)
      constant := (5242909905795590462355556092269036572039802435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 102 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 102 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248614220944621228707/50000000000000000000)
  centralHi := (99445688377848491483/20000000000000000000)
  directionLo := (99936781183653989859/20000000000000000000)
  directionHi := (31230244119891871831/6250000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree103.table
  base := (81224173973668574689105613850863487503099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-79495971434349102675657553813880000000000000)
      constant := (2478450247197088456278250933855249811490478139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree103.table
  base := (16244834794730939454142808530967717360127/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-2904048668245510923296703874199320000000000000)
      constant := (90872826146556734798072024083370980541831405315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 103 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 103 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99936781183653989859/20000000000000000000)
  centralHi := (31230244119891871831/6250000000000000000)
  directionLo := (50212736257235887143/10000000000000000000)
  directionHi := (502127362572358871431/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree104.table
  base := (83820624703675327398227124392688906789989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (78864)
      previous := (0)
      next := (59520)
      square := (1972914491611832851769570139690000000000000)
      linear := (-240736612540798429341892816654620000000000000)
      constant := (7579389534436863138403482752689562118275538287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree104.table
  base := (16764124940732903146072397622810813385271/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-2931434062669833617386927480807060000000000000)
      constant := (92633131197396324786453625695047876666347707995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 104 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50212736257235887143/10000000000000000000)
  centralHi := (502127362572358871431/100000000000000000000)
  directionLo := (504558986297943003459/100000000000000000000)
  directionHi := (25227949314897150173/5000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree105.table
  base := (1350837659727882692221839171913728296669/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 600625000000000000000000000000000000000000
      center := (1643)
      previous := (0)
      next := (1240)
      square := (41102385241913184411866044576875000000000)
      linear := (-5062193974553115638683603580575000000000000)
      constant := (160933649443309901372396345885914496572395636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree105.table
  base := (86453610222576069887795544994128720011383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-2958819457094156311477151087414800000000000000)
      constant := (94410383550934273732310204255746937210078052127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 105 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504558986297943003459/100000000000000000000)
  centralHi := (25227949314897150173/5000000000000000000)
  directionLo := (506978947357917936491/100000000000000000000)
  directionHi := (126744736839479484123/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree106.table
  base := (89123130527333492335086223932892384876711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-81744669672100223990577709026860000000000000)
      constant := (2623875886036157447189432960314389581866519271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree106.table
  base := (89123130527326931771124867950266937384779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-2986204851518479005567374694022540000000000000)
      constant := (96204583207063491591892743763606004533408336851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 106 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506978947357917936491/100000000000000000000)
  centralHi := (126744736839479484123/25000000000000000000)
  directionLo := (254693705985384146557/50000000000000000000)
  directionHi := (101877482394153658623/20000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree107.table
  base := (9182918561492746454175113823001458379201/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (39432)
      previous := (0)
      next := (29760)
      square := (986457245805916425884785069845000000000000)
      linear := (-123741353627025896643326641146780000000000000)
      constant := (4009913494458510087791816268454621022536182415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree107.table
  base := (918291856149223547036575234694755661357/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87422500000000000000000000000000000000000000
      center := (240108)
      previous := (0)
      next := (179520)
      square := (5982556959519093218308194434167500000000000)
      linear := (-753397561485700424914399575157570000000000000)
      constant := (24503932541419813767165996627777305268049823325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 107 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254693705985384146557/50000000000000000000)
  centralHi := (101877482394153658623/20000000000000000000)
  directionLo := (511784542443802133723/100000000000000000000)
  directionHi := (127946135610950533431/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree108.table
  base := (94571775482437143978755409547574088663041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-83243801830600971533857812502180000000000000)
      constant := (2723137721898691232363032194367938699205182401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree108.table
  base := (47285887741216582208621042672476275542387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (480216)
      previous := (0)
      next := (359040)
      square := (11965113919038186436616388868335000000000000)
      linear := (-1520487820183562196873910953619010000000000000)
      constant := (49921912213339566933820472637615462879441731003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 108 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511784542443802133723/100000000000000000000)
  centralHi := (127946135610950533431/25000000000000000000)
  directionLo := (64271312162599345831/12500000000000000000)
  directionHi := (514170497300794766649/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree109.table
  base := (97350900126996842585808727231179056172861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-83993367909851345305497864239840000000000000)
      constant := (2773462062812457042468958017970093072982119421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree109.table
  base := (24337725031748435888345217598541244552951/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87422500000000000000000000000000000000000000
      center := (240108)
      previous := (0)
      next := (179520)
      square := (5982556959519093218308194434167500000000000)
      linear := (-767090258697861771959511378461440000000000000)
      constant := (25422216497490730053853578643190281280772143519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 109 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64271312162599345831/12500000000000000000)
  centralHi := (514170497300794766649/100000000000000000000)
  directionLo := (12913635785108150777/2500000000000000000)
  directionHi := (516545431404326031081/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree110.table
  base := (100166559545802515609055109874483643104943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (78864)
      previous := (0)
      next := (59520)
      square := (1972914491611832851769570139690000000000000)
      linear := (-254228801967305157231413747932500000000000000)
      constant := (8472746057132828405511598154934136343071550669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree110.table
  base := (50083279772900051240092761464291995068081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (43656)
      previous := (0)
      next := (32640)
      square := (1087737629003471494237853533485000000000000)
      linear := (-140715746782534990087648596384250000000000000)
      constant := (4706857038883298245388481386073984252321429499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 110 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12913635785108150777/2500000000000000000)
  centralHi := (516545431404326031081/100000000000000000000)
  directionLo := (64863687009134777409/12500000000000000000)
  directionHi := (518909496073078219273/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree111.table
  base := (103018753736109909221951006521125199213739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-85492500068352092848777967715160000000000000)
      constant := (2875497590591511282540447942922731316444403179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree111.table
  base := (12877344217013503792730685678348074140329/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43711250000000000000000000000000000000000000
      center := (120054)
      previous := (0)
      next := (89760)
      square := (2991278479759546609154097217083750000000000)
      linear := (-390391477955011559502311590882655000000000000)
      constant := (13178723877874011888452616706482975054613164801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 111 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64863687009134777409/12500000000000000000)
  centralHi := (518909496073078219273/100000000000000000000)
  directionLo := (521262839194346051931/100000000000000000000)
  directionHi := (130315709798586512983/25000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree112.table
  base := (105907482695232783843198832453167842429777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-86242066147602466620418019452820000000000000)
      constant := (2927208777451581008341076712890214296575015697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree112.table
  base := (105907482695231321051718820372563732665553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-3150517218064415170108716333668980000000000000)
      constant := (107325674492547587401993562134465461167581722857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 112 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521262839194346051931/100000000000000000000)
  centralHi := (130315709798586512983/25000000000000000000)
  directionLo := (523605605331995430233/100000000000000000000)
  directionHi := (261802802665997715117/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree113.table
  base := (21766549284108241668082516471318496586247/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (78864)
      previous := (0)
      next := (59520)
      square := (1972914491611832851769570139690000000000000)
      linear := (-260974896680558521176174213571440000000000000)
      constant := (8938146738865873846262588231321166128290750505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree113.table
  base := (108832746420540069583032209679446120626667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-3177902612488737864198939940276720000000000000)
      constant := (109238505264007073132783239781266681392193918323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 113 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523605605331995430233/100000000000000000000)
  centralHi := (261802802665997715117/50000000000000000000)
  directionLo := (525937935830093979013/100000000000000000000)
  directionHi := (262968967915046989507/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree114.table
  base := (55897272454729960434339307059011931490819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (13144)
      previous := (0)
      next := (9920)
      square := (328819081935305475294928356615000000000000)
      linear := (-43870599153051607081849061464070000000000000)
      constant := (1516008998550083638573422012751150466162677059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree114.table
  base := (111794544909459034435453799919073011768377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-3205288006913060558289163546884460000000000000)
      constant := (111168283337280498679964862009731184148528375313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 114 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (525937935830093979013/100000000000000000000)
  centralHi := (262968967915046989507/50000000000000000000)
  directionLo := (264129984456211797379/50000000000000000000)
  directionHi := (528259968912423594759/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree115.table
  base := (114792878159466752552671122493888320559757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-88490764385353587935338174665800000000000000)
      constant := (3085116029883785189229832459236876676057926477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree115.table
  base := (57396439079733031293503123426090158736721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (480216)
      previous := (0)
      next := (359040)
      square := (11965113919038186436616388868335000000000000)
      linear := (-1616336700668691626189693576746100000000000000)
      constant := (56557504356139833437256451534578071760864396649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 115 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264129984456211797379/50000000000000000000)
  centralHi := (528259968912423594759/100000000000000000000)
  directionLo := (26528591988903662577/5000000000000000000)
  directionHi := (530571839778073251541/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree116.table
  base := (58913873084045555300500864011619729035263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (39432)
      previous := (0)
      next := (29760)
      square := (986457245805916425884785069845000000000000)
      linear := (-133860495696905942560467339605190000000000000)
      constant := (4708014516955656167995955718473219678808663229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree116.table
  base := (29456936542022643399675963986805969958279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87422500000000000000000000000000000000000000
      center := (240108)
      previous := (0)
      next := (179520)
      square := (5982556959519093218308194434167500000000000)
      linear := (-815014698940426486617402690024985000000000000)
      constant := (28769670347229545997264118051866997963471058351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 116 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26528591988903662577/5000000000000000000)
  centralHi := (530571839778073251541/100000000000000000000)
  directionLo := (532873680693299135869/100000000000000000000)
  directionHi := (53287368069329913587/10000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree117.table
  base := (30224787233228129439681541202341037835583/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2402500000000000000000000000000000000000000
      center := (6572)
      previous := (0)
      next := (4960)
      square := (164409540967652737647464178307500000000000)
      linear := (-22497474135963583869654569535280000000000000)
      constant := (798174735339449491701814161302842237359995263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree117.table
  base := (120899148932912099839275919128868511614771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-3287444190186028640559834366707680000000000000)
      constant := (117059301367111408690997664033980332982656927099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 117 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (532873680693299135869/100000000000000000000)
  centralHi := (53287368069329913587/10000000000000000000)
  directionLo := (267582810539914360429/50000000000000000000)
  directionHi := (535165621079828720859/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree118.table
  base := (124007086451559205271384301609002889581483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-90739462623104709250258329878780000000000000)
      constant := (3247183820043587483886654771799771776887805163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree118.table
  base := (31001771612889720012826827271532895789087/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87422500000000000000000000000000000000000000
      center := (240108)
      previous := (0)
      next := (179520)
      square := (5982556959519093218308194434167500000000000)
      linear := (-828707396152587833662514493328855000000000000)
      constant := (29764217161694100715231482240438853832848583303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 118 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267582810539914360429/50000000000000000000)
  centralHi := (535165621079828720859/100000000000000000000)
  directionLo := (537447787599775598589/100000000000000000000)
  directionHi := (53744778759977559859/10000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree119.table
  base := (63575779360853378380856840485868564261159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (39432)
      previous := (0)
      next := (29760)
      square := (986457245805916425884785069845000000000000)
      linear := (-137233543053532624532847572424660000000000000)
      constant := (4953196471038358348645423455706254070764921397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree119.table
  base := (12715155872170650369736160357152699635279/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10285000000000000000000000000000000000000000
      center := (28248)
      previous := (0)
      next := (21120)
      square := (703830230531658025683316992255000000000000)
      linear := (-98300440559843353786478869997740000000000000)
      constant := (3560923036112702476081107433565320515748844515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 119 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537447787599775598589/100000000000000000000)
  centralHi := (53744778759977559859/10000000000000000000)
  directionLo := (539720304237322719237/100000000000000000000)
  directionHi := (269860152118661359619/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree120.table
  base := (65166282870538400308066579299717870925071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (13144)
      previous := (0)
      next := (9920)
      square := (328819081935305475294928356615000000000000)
      linear := (-46119297390802728396769216677050000000000000)
      constant := (1678770211650781348658743880777028873958993231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree120.table
  base := (130332565741076603712387012610141125860729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-3369600373458996722830505186530900000000000000)
      constant := (123102845110198180450595039328744025030223832401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 120 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (539720304237322719237/100000000000000000000)
  centralHi := (269860152118661359619/50000000000000000000)
  directionLo := (108396658475464618379/20000000000000000000)
  directionHi := (67747911547165386487/12500000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree121.table
  base := (133550107507435748648391144486914630780561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9610000000000000000000000000000000000000000
      center := (26288)
      previous := (0)
      next := (19840)
      square := (657638163870610950589856713230000000000000)
      linear := (-92988160860855830565178485091760000000000000)
      constant := (3413412147869412400301283367054454960180119121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree121.table
  base := (133550107507435595452585096838350467719687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (87312)
      previous := (0)
      next := (65280)
      square := (2175475258006942988475707066970000000000000)
      linear := (-308816887989392674265520799376240000000000000)
      constant := (11377386753981562311911736463474386136880884973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 121 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108396658475464618379/20000000000000000000)
  centralHi := (67747911547165386487/12500000000000000000)
  directionLo := (272118435440479472237/50000000000000000000)
  directionHi := (21769474835238357779/4000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree122.table
  base := (136804184018593578957231436605851161815073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28830000000000000000000000000000000000000000
      center := (78864)
      previous := (0)
      next := (59520)
      square := (1972914491611832851769570139690000000000000)
      linear := (-281213180820318613010455610488260000000000000)
      constant := (10409238463181050191003685730468428899512855459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree122.table
  base := (136804184018593459775370927452546244403757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-3424371162307642111010952399746380000000000000)
      constant := (127216610778552316348662785674310169620554978533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 122 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272118435440479472237/50000000000000000000)
  centralHi := (21769474835238357779/4000000000000000000)
  directionLo := (54648115615859278097/10000000000000000000)
  directionHi := (546481156158592780971/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree123.table
  base := (35023698818100665256832513819737421649477/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2402500000000000000000000000000000000000000
      center := (6572)
      previous := (0)
      next := (4960)
      square := (164409540967652737647464178307500000000000)
      linear := (-23621823254839144527114647141770000000000000)
      constant := (881635610718077953623024261597310162205147397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree123.table
  base := (140094795272402568313543775389535207492789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-3451756556731964805101176006354120000000000000)
      constant := (129298914564388472787123450762408986670815338541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 123 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54648115615859278097/10000000000000000000)
  centralHi := (546481156158592780971/100000000000000000000)
  directionLo := (137179065559984169753/25000000000000000000)
  directionHi := (548716262239936679013/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree124.table
  base := (71710970633378310620536583616311713159087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 155000000000000000000000000000000000000000
      center := (424)
      previous := (0)
      next := (320)
      square := (10607067159203402428868656665000000000000)
      linear := (-1536078372558176643227397424270000000000000)
      constant := (57803242150052797221409062612545663107931697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree124.table
  base := (35855485316689137280513225142942486935153/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87422500000000000000000000000000000000000000
      center := (240108)
      previous := (0)
      next := (179520)
      square := (5982556959519093218308194434167500000000000)
      linear := (-869785487789071874797849903240465000000000000)
      constant := (32849541412807999256466154258185735825635365257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 124 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137179065559984169753/25000000000000000000)
  centralHi := (548716262239936679013/100000000000000000000)
  directionLo := (275471150420829753553/50000000000000000000)
  directionHi := (550942300841659507107/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree125.table
  base := (14678562199958924707533528852888169239583/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14415000000000000000000000000000000000000000
      center := (39432)
      previous := (0)
      next := (29760)
      square := (986457245805916425884785069845000000000000)
      linear := (-143979637766785988477608038063600000000000000)
      constant := (5462282798526873909708449240286257959588588945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree125.table
  base := (146785621999589190979951375906329168856307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-3506527345580610193281623219569600000000000000)
      constant := (133514364039010635724700991391799674705736199483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 125 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275471150420829753553/50000000000000000000)
  centralHi := (550942300841659507107/100000000000000000000)
  directionLo := (110631876286509095933/20000000000000000000)
  directionHi := (276579690716272739833/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree126.table
  base := (75092918734436714177070984889728984340253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4805000000000000000000000000000000000000000
      center := (13144)
      previous := (0)
      next := (9920)
      square := (328819081935305475294928356615000000000000)
      linear := (-48367995628553849711689371890030000000000000)
      constant := (1849852500007145648923899217583069553950983133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree126.table
  base := (30037167493774676944999704774765488077887/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-3533912740004932887371846826177340000000000000)
      constant := (135647509727653502903338179587403791762978152515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 126 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110631876286509095933/20000000000000000000)
  centralHi := (276579690716272739833/50000000000000000000)
  directionLo := (69420951412038947703/12500000000000000000)
  directionHi := (4442940890370492653/800000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree127.table
  base := (19202823459077516752056808307243765474359/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1201250000000000000000000000000000000000000
      center := (3286)
      previous := (0)
      next := (2480)
      square := (82204770483826368823732089153750000000000)
      linear := (-12185694667044759149377349439715000000000000)
      constant := (469793802036311005375525059176732508620858999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree127.table
  base := (153622587672620100085275958949110336030489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-3561298134429255581462070432785080000000000000)
      constant := (137797602717091044162197467596126169340650169841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 127 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69420951412038947703/12500000000000000000)
  centralHi := (4442940890370492653/800000000000000000)
  directionLo := (557567095592185857793/100000000000000000000)
  directionHi := (278783547796092928897/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree128.table
  base := (7854793630443871146974312846094349677147/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7207500000000000000000000000000000000000000
      center := (19716)
      previous := (0)
      next := (14880)
      square := (493228622902958212942392534922500000000000)
      linear := (-73676342561706335224994135441535000000000000)
      constant := (2863093585883472769891880820726690050596074005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree128.table
  base := (157095872608877396552224487850209967378179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (960432)
      previous := (0)
      next := (718080)
      square := (23930227838076372873232777736670000000000000)
      linear := (-3588683528853578275552294039392820000000000000)
      constant := (139964643007255002093635048988089672349247541451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 128 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell167.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (557567095592185857793/100000000000000000000)
  centralHi := (278783547796092928897/50000000000000000000)
  directionLo := (139939484353335837953/25000000000000000000)
  directionHi := (559757937413343351813/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 53
  qDenominator := 93
  table := BinomialMassData.Q53_93.Degree129.table
  base := (5018927883616546482278673886186116475621/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 600625000000000000000000000000000000000000
      center := (1643)
      previous := (0)
      next := (1240)
      square := (41102385241913184411866044576875000000000)
      linear := (-6186543093428676296143681187065000000000000)
      constant := (242314255917179822325770187019607840866143562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_93.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree129.table
  base := (40151423068932366728396014619947395581981/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87422500000000000000000000000000000000000000
      center := (240108)
      previous := (0)
      next := (179520)
      square := (5982556959519093218308194434167500000000000)
      linear := (-904017230819475242410629411500140000000000000)
      constant := (35537157649519595708811350500375632976106293589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 129 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell167.Kernel129
