import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell031.Parameters
import ForestUnimodality.BinomialMassData.Q1677_3572.Batch000_049
import ForestUnimodality.BinomialMassData.Q1677_3572.Batch050_099
import ForestUnimodality.BinomialMassData.Q1677_3572.Batch100_149
import ForestUnimodality.BinomialMassData.Q1677_3572.Batch150_199
import ForestUnimodality.BinomialMassData.Q841_1786.Batch000_049
import ForestUnimodality.BinomialMassData.Q841_1786.Batch050_099
import ForestUnimodality.BinomialMassData.Q841_1786.Batch100_149
import ForestUnimodality.BinomialMassData.Q841_1786.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree000.table
  base := (49334396919698905546036727/625000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (158)
      previous := (79)
      next := (79)
      square := (704343398896500744177373580000000000000)
      linear := (54594114078804160256064293000000000000)
      constant := (789350350715182488736587632000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree000.table
  base := (49334396919698905546036727/625000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (158)
      previous := (79)
      next := (79)
      square := (704343398896500744177373580000000000000)
      linear := (54594114078804160256064293000000000000)
      constant := (789350350715182488736587632000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree001.table
  base := (9132611501875443312074720943520086518699/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-483862580719392976683467663530633000000000000)
      constant := (364242958809352227494360124663714369212499942550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree001.table
  base := (455641039410515910797110563735606789540773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-485435027357429414594843650047983000000000000)
      constant := (363454532968056899060552457374715489212499888077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49906795889839124337/100000000000000000000)
  directionHi := (24953397944919562169/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree002.table
  base := (274866380088576266477064868004594046135317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-1011261183116814252158973541449823000000000000)
      constant := (219646252268886870367693188191767785996562406333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree002.table
  base := (273788699737272952349375129949484588359647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-1014406076392887127981725514484523000000000000)
      constant := (218789692630906829572092977353243706502812140503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49906795889839124337/100000000000000000000)
  centralHi := (24953397944919562169/50000000000000000000)
  directionLo := (17644716900499081521/25000000000000000000)
  directionHi := (14115773520399265217/20000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree003.table
  base := (86965566079519342983227417550085374760351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-1538659785514235527634479419369013000000000000)
      constant := (139754114415792563393257047857142183034534289198) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree003.table
  base := (173037571197330222954594795710669477516471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-1543377125428344841368607378921063000000000000)
      constant := (139048016362553352413104746992190405676032282479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17644716900499081521/25000000000000000000)
  centralHi := (14115773520399265217/20000000000000000000)
  directionLo := (86441106124170981383/100000000000000000000)
  directionHi := (10805138265521372673/12500000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree004.table
  base := (23298950148997375026677136248472639807427/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-2066058387911656803109985297288203000000000000)
      constant := (94797709837440267592577655085219737708964268615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree004.table
  base := (28955334463653207725722362565549080439111/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-2072348174463802554755489243357603000000000000)
      constant := (94272283086089481264435581848524496588354511356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86441106124170981383/100000000000000000000)
  centralHi := (10805138265521372673/12500000000000000000)
  directionLo := (49906795889839124337/50000000000000000000)
  directionHi := (3992543671187129947/4000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree005.table
  base := (10333568773286052147990170026153387802873/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-2593456990309078078585491175207393000000000000)
      constant := (68916826042843047325747503752357196100106167816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree005.table
  base := (82177484025453577988169487414090235957173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-2601319223499260268142371107794143000000000000)
      constant := (68543404632090492583837531555656697073811651677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49906795889839124337/50000000000000000000)
  centralHi := (3992543671187129947/4000000000000000000)
  directionLo := (111594988148887387979/100000000000000000000)
  directionHi := (5579749407444369399/5000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree006.table
  base := (15450635702801370862169394260423035341763/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-3120855592706499354060997053126583000000000000)
      constant := (53618641013161242858194757227738891941014250348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree006.table
  base := (61443993313422566426472457890748128633779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-3130290272534717981529252972230683000000000000)
      constant := (53358966687239760813387524901206597430878429771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111594988148887387979/100000000000000000000)
  centralHi := (5579749407444369399/5000000000000000000)
  directionLo := (122246184627334606587/100000000000000000000)
  directionHi := (30561546156833651647/25000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree007.table
  base := (24094872421455709889039691383630335534413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-3648254195103920629536502931045773000000000000)
      constant := (44352126242548215664995022028195550883164224874) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree007.table
  base := (9584352482097608352559342243751164702861/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-3659261321570175694916134836667223000000000000)
      constant := (44174225017650671394698950716800536205659007945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122246184627334606587/100000000000000000000)
  centralHi := (30561546156833651647/25000000000000000000)
  directionLo := (132040970656574784211/100000000000000000000)
  directionHi := (33010242664143696053/25000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree008.table
  base := (38749178190970363541584787373002533574501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-4175652797501341905012008808964963000000000000)
      constant := (38660358833763977527285218759906031396452247949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree008.table
  base := (38541457148813187933466827056795131316689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-4188232370605633408303016701103763000000000000)
      constant := (38541542160515923194609908726674664673362326361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132040970656574784211/100000000000000000000)
  centralHi := (33010242664143696053/25000000000000000000)
  directionLo := (17644716900499081521/12500000000000000000)
  directionHi := (141157735203992652169/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree009.table
  base := (7950231614926204901510953613085504778543/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-4703051399898763180487514686884153000000000000)
      constant := (35203691136991905628630031887422940300577347228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree009.table
  base := (6326643959090803567447082049179473479199/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-4717203419641091121689898565540303000000000000)
      constant := (35129291736557066643217764908704564232568816755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17644716900499081521/12500000000000000000)
  centralHi := (141157735203992652169/100000000000000000000)
  directionLo := (37430096917379343253/25000000000000000000)
  directionHi := (149720387669517373013/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree010.table
  base := (26415279346192279793863729369506614987353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-5230450002296184455963020564803343000000000000)
      constant := (33240726600876748745316312768184123115049662497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree010.table
  base := (6568669183441406449687947313863786381799/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-5246174468676548835076780429976843000000000000)
      constant := (33201927827554238354619801601478905345516923004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37430096917379343253/25000000000000000000)
  centralHi := (149720387669517373013/100000000000000000000)
  directionLo := (3945478643325533921/2500000000000000000)
  directionHi := (157819145733021356841/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree011.table
  base := (11033099478210423077794495605005219721959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-5757848604693605731438526442722533000000000000)
      constant := (32351976832876612869448689755473727924112965182) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree011.table
  base := (21944699800043835996506976694794414437531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-5775145517712006548463662294413383000000000000)
      constant := (32343877300489707024129498319292056498794658419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3945478643325533921/2500000000000000000)
  centralHi := (157819145733021356841/100000000000000000000)
  directionLo := (82761058227723708309/50000000000000000000)
  directionHi := (165522116455447416619/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree012.table
  base := (3689310854362053622638357187257290443953/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-6285247207091027006914032320641723000000000000)
      constant := (32292520509355695757829460572847956036199379485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree012.table
  base := (18339270438424288821956486982053559502693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-6304116566747464261850544158849923000000000000)
      constant := (32312700862007994946272663579374054971863030157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82761058227723708309/50000000000000000000)
  centralHi := (165522116455447416619/100000000000000000000)
  directionLo := (86441106124170981383/50000000000000000000)
  directionHi := (172882212248341962767/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree013.table
  base := (960585508793206324986455812134918406209/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-6812645809488448282389538198560913000000000000)
      constant := (32913252887692510079582602158199743269807373456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree013.table
  base := (15273309235094562500120607810742055839913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-6833087615782921975237426023286463000000000000)
      constant := (32960807118643800189013500782626338187482781937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86441106124170981383/50000000000000000000)
  centralHi := (172882212248341962767/100000000000000000000)
  directionLo := (89970755787465216623/50000000000000000000)
  directionHi := (179941511574930433247/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree014.table
  base := (12714828573280797903926009085011309732389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-7340044411885869557865044076480103000000000000)
      constant := (34118630016446474634859788943551173434783875661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree014.table
  base := (12628126077426202719132642243707866931867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-7362058664818379688624307887723003000000000000)
      constant := (34193546758771674489808224323213951776950407283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89970755787465216623/50000000000000000000)
  centralHi := (179941511574930433247/100000000000000000000)
  directionLo := (18673413149143593669/10000000000000000000)
  directionHi := (186734131491435936691/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree015.table
  base := (5200839250361298062466016269024811567863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-7867443014283290833340549954399293000000000000)
      constant := (35843853527315311812629554429428703919961562974) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree015.table
  base := (5161555004881089335714378277586140650227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-7891029713853837402011189752159543000000000000)
      constant := (35946636656413874288195862560348388050765741846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18673413149143593669/10000000000000000000)
  centralHi := (186734131491435936691/100000000000000000000)
  directionLo := (193288189343919691331/100000000000000000000)
  directionHi := (48322047335979922833/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree016.table
  base := (8371617012420484787256458338074218107887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-8394841616680712108816055832318483000000000000)
      constant := (38042431417444983686909689656366575155916380263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree016.table
  base := (8300324091118447932494050933170255031801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-8420000762889295115398071616596083000000000000)
      constant := (38173875055919615936789433153877934704854675649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193288189343919691331/100000000000000000000)
  centralHi := (48322047335979922833/25000000000000000000)
  directionLo := (199627183559356497349/100000000000000000000)
  directionHi := (3992543671187129947/2000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree017.table
  base := (1316133369739950904097696508657128798869/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-8922240219078133384291561710237673000000000000)
      constant := (40679294065085152944975469431780757017646425905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree017.table
  base := (6515992845505681413454495759485623368699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-8948971811924752828784953481032623000000000000)
      constant := (40840353247736684942995430058785729369745648851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199627183559356497349/100000000000000000000)
  centralHi := (3992543671187129947/2000000000000000000)
  directionLo := (20577099088994803289/10000000000000000000)
  directionHi := (205770990889948032891/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree018.table
  base := (1248572530955548919541848581228224146783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-9449638821475554659767067588156863000000000000)
      constant := (43726899267791770042466446365978640970511826268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree018.table
  base := (4935689957475185934279342355371061309891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-9477942860960210542171835345469163000000000000)
      constant := (43918618001036836379091512771953396470511268059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20577099088994803289/10000000000000000000)
  centralHi := (205770990889948032891/100000000000000000000)
  directionLo := (52934150701497244563/25000000000000000000)
  directionHi := (211736602805988978253/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree019.table
  base := (1792268308659231584524551804873218206221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (349022)
      previous := (174511)
      next := (174511)
      square := (1555894568162370143887818238220000000000000)
      linear := (-27637222780811567687652558077773000000000000)
      constant := (130645313435461983949349340925676878035084378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree019.table
  base := (441441065069926653599071758671101899813/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (349022)
      previous := (174511)
      next := (174511)
      square := (1555894568162370143887818238220000000000000)
      linear := (-27719983130181906525093399473423000000000000)
      constant := (131264351607048283511811310223525212773495336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52934150701497244563/25000000000000000000)
  centralHi := (211736602805988978253/100000000000000000000)
  directionLo := (217538679879719788129/100000000000000000000)
  directionHi := (21753867987971978813/10000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree020.table
  base := (2328307686311942969855923190447659418997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-10504436026270397210718079343995243000000000000)
      constant := (50969050722651858458472698170547930556019738653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree020.table
  base := (1140224349558907792516046444263524377251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-10535884959031125968945599074342243000000000000)
      constant := (51225402992187747716656077616672916502228865398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217538679879719788129/100000000000000000000)
  centralHi := (21753867987971978813/10000000000000000000)
  directionLo := (111594988148887387979/50000000000000000000)
  directionHi := (223189976297774775959/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree021.table
  base := (603121898197486300912785418336582863569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-11031834628667818486193585221914433000000000000)
      constant := (55129738743788160764712701452809259835940470962) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree021.table
  base := (1163118246515513581039055928472887506671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-11064856008066583682332480938778783000000000000)
      constant := (55420117706420050525606439350594076169307282279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111594988148887387979/50000000000000000000)
  centralHi := (223189976297774775959/100000000000000000000)
  directionLo := (228701669857898784871/100000000000000000000)
  directionHi := (28587708732237348109/12500000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree022.table
  base := (100985013982834543543618572948291523877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-11559233231065239761669091099833623000000000000)
      constant := (59631964050349081145615022833718087754848379546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree022.table
  base := (20398099028396240527922455026780563339/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-11593827057102041395719362803215323000000000000)
      constant := (59957534891318279075976298656395890067632977688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228701669857898784871/100000000000000000000)
  centralHi := (28587708732237348109/12500000000000000000)
  directionLo := (58520905490998146869/25000000000000000000)
  directionHi := (234083621963992587477/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree023.table
  base := (-698445273157876807569110402587985497359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-12086631833462661037144596977752813000000000000)
      constant := (64464616858638910265065555089670017553116562809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree023.table
  base := (-733262212038071205649434156743150713727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-12122798106137499109106244667651863000000000000)
      constant := (64826561594058438684775475194541382706489117577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58520905490998146869/25000000000000000000)
  centralHi := (234083621963992587477/100000000000000000000)
  directionLo := (239344584956024138229/100000000000000000000)
  directionHi := (23934458495602413823/10000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree024.table
  base := (-1506898851168816868991406198012497971977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-12614030435860082312620102855672003000000000000)
      constant := (69618210121897563423794199789906413504744913327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree024.table
  base := (-384524611549579979049911958964708624579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-12651769155172956822493126532088403000000000000)
      constant := (70017727565565512364792298355577620288152404116) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239344584956024138229/100000000000000000000)
  centralHi := (23934458495602413823/10000000000000000000)
  directionLo := (122246184627334606587/50000000000000000000)
  directionHi := (9779694770186768527/4000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree025.table
  base := (-2233573250630434711434031990510466489783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-13141429038257503588095608733591193000000000000)
      constant := (75084623780145594666897414462165056508189036433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree025.table
  base := (-113074250666019231222792455290244371839/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-13180740204208414535880008396524943000000000000)
      constant := (75522929844359976810675737899811760818427225780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122246184627334606587/50000000000000000000)
  centralHi := (9779694770186768527/4000000000000000000)
  directionLo := (249533979449195621687/100000000000000000000)
  directionHi := (31191747431149452711/12500000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree026.table
  base := (-2887196358925149309954546899845078694069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-13668827640654924863571114611510383000000000000)
      constant := (80856897788317781365134523643949912340493370019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree026.table
  base := (-1456064018132650244244702487038327994403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-13709711253243872249266890260961483000000000000)
      constant := (81335225741472422396656940278483647758382644106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249533979449195621687/100000000000000000000)
  centralHi := (31191747431149452711/12500000000000000000)
  directionLo := (127237863051590942473/50000000000000000000)
  directionHi := (254475726103181884947/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree027.table
  base := (-434406987484765905687796953266262886497/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-14196226243052346139046620489429573000000000000)
      constant := (86929061068537468253693989557579956419406830776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree027.table
  base := (-1748746700869470834470531538283922447131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-14238682302279329962653772125398023000000000000)
      constant := (87448661593015136479207101930097482156915662362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127237863051590942473/50000000000000000000)
  centralHi := (254475726103181884947/100000000000000000000)
  directionLo := (5186466367450258883/2000000000000000000)
  directionHi := (259323318372512944151/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree028.table
  base := (-4004179207637832647319438418751954804973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-14723624845449767414522126367348763000000000000)
      constant := (93295988149615296761175972142102241392729086123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree028.table
  base := (-2011993418362872702426218094084133394141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-14767653351314787676040653989834563000000000000)
      constant := (93858129158410106566489727788930157817951307382) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5186466367450258883/2000000000000000000)
  centralHi := (259323318372512944151/100000000000000000000)
  directionLo := (264081941313149568423/100000000000000000000)
  directionHi := (33010242664143696053/12500000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree029.table
  base := (-4479485286273407100604903237462293833749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-15251023447847188689997632245267953000000000000)
      constant := (99953277907275333999604980107180765744570693699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree029.table
  base := (-4497106252755378952792986350799040613741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-15296624400350245389427535854271103000000000000)
      constant := (100559244133605911034420756919113720361612853291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264081941313149568423/100000000000000000000)
  centralHi := (33010242664143696053/12500000000000000000)
  directionLo := (268756320862806566507/100000000000000000000)
  directionHi := (67189080215701641627/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree030.table
  base := (-122647854540179197952124957676045964767/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-15778422050244609965473138123187143000000000000)
      constant := (106897150396716618850264795481192370357700824680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree030.table
  base := (-4921571354828204371907933264276019326089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-15825595449385703102814417718707643000000000000)
      constant := (107548242794569716159296893016249717664429653039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268756320862806566507/100000000000000000000)
  centralHi := (67189080215701641627/25000000000000000000)
  directionLo := (54670155763341995231/20000000000000000000)
  directionHi := (68337694704177494039/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree031.table
  base := (-5287537457005881434954513769714342640857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-16305820652642031240948644001106333000000000000)
      constant := (114124358753803886865920668060010865175391226207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree031.table
  base := (-265071714908717698439290799640214766243/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-16354566498421160816201299583144183000000000000)
      constant := (114821893754165408163361412192126862997485717860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54670155763341995231/20000000000000000000)
  centralHi := (68337694704177494039/25000000000000000000)
  directionLo := (5557385592369561781/2000000000000000000)
  directionHi := (277869279618478089051/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree032.table
  base := (-5627852751094064112991603528968817746411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-16833219255039452516424149879025523000000000000)
      constant := (121632113790113656018644070791452841256942294461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree032.table
  base := (-564017437270697721189602841151564186289/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-16883537547456618529588181447580723000000000000)
      constant := (122377422456131035916132864770415198912080232390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5557385592369561781/2000000000000000000)
  centralHi := (277869279618478089051/100000000000000000000)
  directionLo := (282315470407985304337/100000000000000000000)
  directionHi := (141157735203992652169/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree033.table
  base := (-5929864827414520582397570667927765480257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-17360617857436873791899655756944713000000000000)
      constant := (129418019359963480298885604733185342845534535607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree033.table
  base := (-742597391462588327917207306235928099949/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-17412508596492076242975063312017263000000000000)
      constant := (130212446479095296987495855180840929480990159192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282315470407985304337/100000000000000000000)
  centralHi := (141157735203992652169/50000000000000000000)
  directionLo := (35836589434645931391/12500000000000000000)
  directionHi := (286692715477167451129/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree034.table
  base := (-6196155107778529519288517291519891695411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-17888016459834295067375161634863903000000000000)
      constant := (137480016911111377337655160377735078387386193461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree034.table
  base := (-775726745558133555747303492034519256971/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-17941479645527533956361945176453803000000000000)
      constant := (138324920055918698984601761519102984224381864168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35836589434645931391/12500000000000000000)
  centralHi := (286692715477167451129/100000000000000000000)
  directionLo := (72751031514878773869/25000000000000000000)
  directionHi := (291004126059515095477/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree035.table
  base := (-803617669833141589970439509526084678129/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-18415415062231716342850667512783093000000000000)
      constant := (145816337887896401733695328318328921396085656632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree035.table
  base := (-3218740895183982850547277204845562291883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-18470450694562991669748827040890343000000000000)
      constant := (146713086470754227011036885384935939891800387066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72751031514878773869/25000000000000000000)
  centralHi := (291004126059515095477/100000000000000000000)
  directionLo := (295252586203156256119/100000000000000000000)
  directionHi := (7381314655078906403/2500000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree036.table
  base := (-414383058918060410749156900132175962399/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-18942813664629137618326173390702283000000000000)
      constant := (154425462860806874313901160070433005575374077584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree036.table
  base := (-6637674293479103430007311094373971063117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-18999421743598449383135708905326883000000000000)
      constant := (155375437202032178851304618766941529149688411467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295252586203156256119/100000000000000000000)
  centralHi := (7381314655078906403/2500000000000000000)
  directionLo := (37430096917379343253/12500000000000000000)
  directionHi := (11977631013561389841/4000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree037.table
  base := (-6801354836486295173872908637697532733899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-19470212267026558893801679268621473000000000000)
      constant := (163306086424461182909654111146027888718884976349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree037.table
  base := (-3404007952711050272928608774262166607079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-19528392792633907096522590769763423000000000000)
      constant := (164310676848378731226739967483953007502702917058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37430096917379343253/12500000000000000000)
  centralHi := (11977631013561389841/4000000000000000000)
  directionLo := (303571188045954622397/100000000000000000000)
  directionHi := (151785594022977311199/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree038.table
  base := (-694402544090533323233462608291061014589/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (349022)
      previous := (174511)
      next := (174511)
      square := (1555894568162370143887818238220000000000000)
      linear := (-55395043959623213765310762178783000000000000)
      constant := (477720462731050746679063660944821962187728990) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree038.table
  base := (-3474950783755978821998760516889784667429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (349022)
      previous := (174511)
      next := (174511)
      square := (1555894568162370143887818238220000000000000)
      linear := (-55560564658363891440192444970083000000000000)
      constant := (480658429405089136364484985762949931339298678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303571188045954622397/100000000000000000000)
  centralHi := (151785594022977311199/50000000000000000000)
  directionLo := (153823075713319428759/50000000000000000000)
  directionHi := (307646151426638857519/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree039.table
  base := (-7059349061574405726019840755658695373803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-20525009471821401444752691024459853000000000000)
      constant := (181877501163036282112466760523391481032856171453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree039.table
  base := (-7064529154465370800353608138988594369017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-20586334890704822523296354498636503000000000000)
      constant := (182995530458612565284771332286466303909021762367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153823075713319428759/50000000000000000000)
  centralHi := (307646151426638857519/100000000000000000000)
  directionLo := (311667840438522737971/100000000000000000000)
  directionHi := (77916960109630684493/25000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree040.table
  base := (-3574181906243490397130119849972188775233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-21052408074218822720228196902379043000000000000)
      constant := (191566500932876093419386533411407326066758438766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree040.table
  base := (-7152927315676754926393838270820094423677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-21115305939740280236683236363073043000000000000)
      constant := (192743368883073965621581193021588606521933200027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311667840438522737971/100000000000000000000)
  centralHi := (77916960109630684493/25000000000000000000)
  directionLo := (315638291466042713681/100000000000000000000)
  directionHi := (157819145733021356841/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree041.table
  base := (-7211961588302510093246513065086596383069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-21579806676616243995703702780298233000000000000)
      constant := (201523375114924468408123690596244024300918009019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree041.table
  base := (-1443195876476078086055431357562187450769/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-21644276988775737950070118227509583000000000000)
      constant := (202760503877011933560802719248571966397858558595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315638291466042713681/100000000000000000000)
  centralHi := (157819145733021356841/50000000000000000000)
  directionLo := (319559414374842970123/100000000000000000000)
  directionHi := (79889853593710742531/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree042.table
  base := (-7250908659623021246010077708166021621889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-22107205279013665271179208658217423000000000000)
      constant := (211747512647456090752719451736639452723646238839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree042.table
  base := (-3627221948485198078189651772487162077693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-22173248037811195663457000091946123000000000000)
      constant := (213046330541552821424107321595775961176611589686) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319559414374842970123/100000000000000000000)
  centralHi := (79889853593710742531/25000000000000000000)
  directionLo := (40429125406301816883/12500000000000000000)
  directionHi := (64686600650082907013/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree043.table
  base := (-726586336717809766205067572558782004769/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-22634603881411086546654714536136613000000000000)
      constant := (222238388537314494892851656997557407490789657190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree043.table
  base := (-113577691280054489983025116610072832457/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-22702219086846653376843881956382663000000000000)
      constant := (223600329432391955108737835128689859409119859648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40429125406301816883/12500000000000000000)
  centralHi := (64686600650082907013/20000000000000000000)
  directionLo := (319590572258308417/97656250000000000)
  directionHi := (327260745992507819009/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree044.table
  base := (-7257391323679119315361393945988350848957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-23162002483808507822130220414055803000000000000)
      constant := (232995551737208603579639493280588652603850089307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree044.table
  base := (-3630061889096928109261873740898167524991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-23231190135882111090230763820819203000000000000)
      constant := (234422054487695775014432138720469516410726904082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319590572258308417/97656250000000000)
  centralHi := (327260745992507819009/100000000000000000000)
  directionLo := (331044232910894833237/100000000000000000000)
  directionHi := (165522116455447416619/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree045.table
  base := (-90324730930727055809922926743900544637/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-23689401086205929097605726291974993000000000000)
      constant := (244018614730519296337640009605733282866381518960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree045.table
  base := (-7228378844981097598317168386195738965931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-23760161184917568803617645685255743000000000000)
      constant := (245511122661449903417200063634788266657357289981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331044232910894833237/100000000000000000000)
  centralHi := (165522116455447416619/50000000000000000000)
  directionLo := (334784964446662163937/100000000000000000000)
  directionHi := (167392482223331081969/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree046.table
  base := (-1793010579628815175287378966511833263273/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-24216799688603350373081232169894183000000000000)
      constant := (255307244583086500164596125001477825804144837692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree046.table
  base := (-7174149923024887170423968374450570965687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-24289132233953026517004527549692283000000000000)
      constant := (256867205021300966691977135193583579633983867537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334784964446662163937/100000000000000000000)
  centralHi := (167392482223331081969/50000000000000000000)
  directionLo := (21155272382835549343/6250000000000000000)
  directionHi := (338484358125368789489/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree047.table
  base := (-7095941549094977968019958187271963517291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (57038)
      previous := (28519)
      next := (28519)
      square := (254267967001636768648031862380000000000000)
      linear := (-11201538384337153304009387979997000000000000)
      constant := (120806317453753293799710604881668821170257949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree047.table
  base := (-7097791220877481954523878114471783441621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (57038)
      previous := (28519)
      next := (28519)
      square := (254267967001636768648031862380000000000000)
      linear := (-11234994695784737089357813225047000000000000)
      constant := (121543693573559608886680295090747186177574819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21155272382835549343/6250000000000000000)
  centralHi := (338484358125368789489/100000000000000000000)
  directionLo := (34214375483345151331/10000000000000000000)
  directionHi := (342143754833451513311/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree048.table
  base := (-1749496084101663578520355345199296177347/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-25271596893398192924032243925732563000000000000)
      constant := (278680100997257607436954978069998269850683248788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree048.table
  base := (-699960690694384137033675613918793211757/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-25347074332023941943778291278565363000000000000)
      constant := (280379322350736164949002792153193786720775921070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34214375483345151331/10000000000000000000)
  centralHi := (342143754833451513311/100000000000000000000)
  directionLo := (345764424496683925533/100000000000000000000)
  directionHi := (172882212248341962767/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree049.table
  base := (-6878435443742748437888191021733314894617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-25798995495795614199507749803651753000000000000)
      constant := (290763870673613436568075464183067209270602567967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree049.table
  base := (-6879858178601570149051190480236264679691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-25876045381059399657165173143001903000000000000)
      constant := (292534906469942359931673587749542245467445091741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345764424496683925533/100000000000000000000)
  centralHi := (172882212248341962767/50000000000000000000)
  directionLo := (174673785614436935181/50000000000000000000)
  directionHi := (349347571228873870363/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree050.table
  base := (-6737522341309581348454838941979191380491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-26326394098193035474983255681570943000000000000)
      constant := (303112282888519952914604523230037348312818832541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree050.table
  base := (-6738769332684446021527798280749237525663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-26405016430094857370552055007438443000000000000)
      constant := (304956592596325961760992090364332076284397566313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174673785614436935181/50000000000000000000)
  centralHi := (349347571228873870363/100000000000000000000)
  directionLo := (352894338009981630421/100000000000000000000)
  directionHi := (176447169004990815211/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree051.table
  base := (-6575440458940308479307035060789405483169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-26853792700590456750458761559490133000000000000)
      constant := (315725181796652136509232543259469032386852364119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree051.table
  base := (-1644133244601080645354355790174256784093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-26933987479130315083938936871874983000000000000)
      constant := (317644227133863587000555028403661681907127284972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352894338009981630421/100000000000000000000)
  centralHi := (176447169004990815211/50000000000000000000)
  directionLo := (356405810945182582939/100000000000000000000)
  directionHi := (17820290547259129147/5000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree052.table
  base := (-3196178849488028704635327452591868144451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-27381191302987878025934267437409323000000000000)
      constant := (328602433504455957505352408658215865680151389002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree052.table
  base := (-6393314513856513327561208543681723602809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-27462958528165772797325818736311523000000000000)
      constant := (330597678186009525996025030885522999194663565759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356405810945182582939/100000000000000000000)
  centralHi := (17820290547259129147/5000000000000000000)
  directionLo := (359883023149860866493/100000000000000000000)
  directionHi := (179941511574930433247/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree053.table
  base := (-6188418313518193035373872516244859799963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-27908589905385299301409773315328513000000000000)
      constant := (341743922978237434567193899065390509297379305613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree053.table
  base := (-247570238805591716756583686267330395423/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-27991929577201230510712700600748063000000000000)
      constant := (343816832490206091994392742949973607587508101825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359883023149860866493/100000000000000000000)
  centralHi := (179941511574930433247/50000000000000000000)
  directionLo := (363326958299922131807/100000000000000000000)
  directionHi := (11353967446872566619/3125000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree054.table
  base := (-2981873117788974298378512623939210010147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-28435988507782720576885279193247703000000000000)
      constant := (355149551387740692759437791598458261333236569994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree054.table
  base := (-5964479312425964871693499891140473556659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-28520900626236688224099582465184603000000000000)
      constant := (357301592785448995453455290710811497502715837109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363326958299922131807/100000000000000000000)
  centralHi := (11353967446872566619/3125000000000000000)
  directionLo := (366738553882003819761/100000000000000000000)
  directionHi := (183369276941001909881/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree055.table
  base := (-5718447941040182543200663199644212587917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-28963387110180141852360785071166893000000000000)
      constant := (368819233823877827596165036361075262315978176267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree055.table
  base := (-71488615933673819085134406431597186039/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-29049871675272145937486464329621143000000000000)
      constant := (371051875551731515414028086159834967947230839120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366738553882003819761/100000000000000000000)
  centralHi := (183369276941001909881/50000000000000000000)
  directionLo := (289155237635950753/78125000000000000)
  directionHi := (370118704174016963841/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree056.table
  base := (-5452614907524576944704846922512971939717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-29490785712577563127836290949086083000000000000)
      constant := (382752897337912501230336155066930451039644618067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree056.table
  base := (-5453175794005770262282030218444069824911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-29578842724307603650873346194057683000000000000)
      constant := (385067609068833373132067903143933662962194547961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289155237635950753/78125000000000000)
  centralHi := (370118704174016963841/100000000000000000000)
  directionLo := (18673413149143593669/5000000000000000000)
  directionHi := (373468262982871873381/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree057.table
  base := (-5166325726920012041528577709734998065403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (349022)
      previous := (174511)
      next := (174511)
      square := (1555894568162370143887818238220000000000000)
      linear := (-83152865138434859842968966279793000000000000)
      constant := (1099585815115849080341376308569868889273524773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree057.table
  base := (-206672644035870700468021369666479931089/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (349022)
      previous := (174511)
      next := (174511)
      square := (1555894568162370143887818238220000000000000)
      linear := (-83401146186545876355291490466743000000000000)
      constant := (1106229173820890573898654506727007145805609975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18673413149143593669/5000000000000000000)
  centralHi := (373468262982871873381/100000000000000000000)
  directionLo := (37678804616313613741/10000000000000000000)
  directionHi := (376788046163136137411/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree058.table
  base := (-2429823960185605357766107970890963758597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-30545582917372405678787302704924463000000000000)
      constant := (411411925735935539797450450816405190183341161894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree058.table
  base := (-243003825722914462012633194517666286729/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-30636784822378519077647109922930763000000000000)
      constant := (413895190707162776118821278573075349746284913580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37678804616313613741/10000000000000000000)
  centralHi := (376788046163136137411/100000000000000000000)
  directionLo := (190039416968838120193/50000000000000000000)
  directionHi := (380078833937676240387/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree059.table
  base := (-2266319748813200259595152433588322561777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-31072981519769826954262808582843653000000000000)
      constant := (426137190515438852299483693295986688522866986254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree059.table
  base := (-2266506991915755905212192907265025727729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-31165755871413976791033991787367303000000000000)
      constant := (428706940528261528007200836458725554496896473358) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190039416968838120193/50000000000000000000)
  centralHi := (380078833937676240387/100000000000000000000)
  directionLo := (76668274607796864271/20000000000000000000)
  directionHi := (95835343259746080339/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree060.table
  base := (-130792196773501672365642311897287888817/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-31600380122167248229738314460762843000000000000)
      constant := (441126233852015185429011624593553134451224709344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree060.table
  base := (-4185677411935366166158044906625484718893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-31694726920449434504420873651803843000000000000)
      constant := (443783942215053954280237071593274143836403496043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76668274607796864271/20000000000000000000)
  centralHi := (95835343259746080339/25000000000000000000)
  directionLo := (193288189343919691331/50000000000000000000)
  directionHi := (386576378687839382663/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree061.table
  base := (-3817823135149444341748635596850594602733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-32127778724564669505213820338682033000000000000)
      constant := (456379021600970710128283892007611540684645171883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree061.table
  base := (-1909054396096034605060480842287058555713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-32223697969484892217807755516240383000000000000)
      constant := (459126162279927501491114831897014775383610447726) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193288189343919691331/50000000000000000000)
  centralHi := (386576378687839382663/100000000000000000000)
  directionLo := (389784536424155572449/100000000000000000000)
  directionHi := (7795690728483111449/2000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree062.table
  base := (-3430094798450720086048920972790931384091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-32655177326962090780689326216601223000000000000)
      constant := (471895524427639856333552308893477318058688016141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree062.table
  base := (-857586046166901130635164110191729055279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-32752669018520349931194637380676923000000000000)
      constant := (474733571966818611099765261540300564426387266916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389784536424155572449/100000000000000000000)
  centralHi := (7795690728483111449/2000000000000000000)
  directionLo := (15718660152131742071/4000000000000000000)
  directionHi := (12280203243852923493/3125000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree063.table
  base := (-755549222532199945042961300240899455559/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-33182575929359512056164832094520413000000000000)
      constant := (487675717129864748236010063357127753880255724036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree063.table
  base := (-3022414554312649242794013732020443085653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-33281640067555807644581519245113463000000000000)
      constant := (490606146582758330572069403310182701181789100803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15718660152131742071/4000000000000000000)
  centralHi := (12280203243852923493/3125000000000000000)
  directionLo := (198061455984862176317/50000000000000000000)
  directionHi := (79224582393944870527/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree064.table
  base := (-1297078280719641970668589304719734502793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-33709974531756933331640337972439603000000000000)
      constant := (503719578055903758458800766770213056880964449886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree064.table
  base := (-518869298156948131121571667388418977569/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-33810611116591265357968401109550003000000000000)
      constant := (506743864923850846457859135513785495373782892595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198061455984862176317/50000000000000000000)
  centralHi := (79224582393944870527/20000000000000000000)
  directionLo := (399254367118712994699/100000000000000000000)
  directionHi := (3992543671187129947/1000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree065.table
  base := (-1072998569274698369519612249593151194767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-34237373134154354607115843850358793000000000000)
      constant := (520027088604328160255185356459679789845768501234) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree065.table
  base := (-1073081413290243784823486934954114881413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-34339582165626723071355282973986543000000000000)
      constant := (523146708782344570559273535122608134583864169126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399254367118712994699/100000000000000000000)
  centralHi := (3992543671187129947/1000000000000000000)
  directionLo := (402361451855609691227/100000000000000000000)
  directionHi := (100590362963902422807/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree066.table
  base := (-838869330667502511738079469763942987477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-34764771736551775882591349728277983000000000000)
      constant := (536598232794358983481340147117221767357158907654) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree066.table
  base := (-838941583921702582586172847574609466497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-34868553214662180784742164838423083000000000000)
      constant := (539814662523339962839328659618930473511102867694) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402361451855609691227/100000000000000000000)
  centralHi := (100590362963902422807/25000000000000000000)
  directionLo := (202722363230690571701/50000000000000000000)
  directionHi := (405444726461381143403/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree067.table
  base := (-74337396642946598972169197893415028997/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-35292170338949197158066855606197173000000000000)
      constant := (553432996896722667340988259610251256256661941552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree067.table
  base := (-237904870036713819729756511452486217883/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-35397524263697638498129046702859623000000000000)
      constant := (556747712721296604075852303734182085090177097665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202722363230690571701/50000000000000000000)
  centralHi := (405444726461381143403/100000000000000000000)
  directionLo := (204252365036083634857/50000000000000000000)
  directionHi := (81700946014433453943/20000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree068.table
  base := (-27239639368686031687005923356419329049/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-35819568941346618433542361484116363000000000000)
      constant := (570531369116501505644692739426714308061730099975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree068.table
  base := (-681100830102584803040185736768030531931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-35926495312733096211515928567296163000000000000)
      constant := (573945847847891745517932837356113444820342155981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204252365036083634857/50000000000000000000)
  centralHi := (81700946014433453943/20000000000000000000)
  directionLo := (20577099088994803289/5000000000000000000)
  directionHi := (411541981779896065781/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree069.table
  base := (-152529281943932352463433167982692007821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-36346967543744039709017867362035553000000000000)
      constant := (587893339320655464073707499688339374741055151371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree069.table
  base := (-30525004224170546922833511678440605323/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-36455466361768553924902810431732703000000000000)
      constant := (591409058003975957342120109303983980588628894865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20577099088994803289/5000000000000000000)
  centralHi := (411541981779896065781/100000000000000000000)
  directionLo := (207278490830159683921/50000000000000000000)
  directionHi := (414556981660319367843/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree070.table
  base := (197987922073249505484479401156453045569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-36874366146141460984493373239954743000000000000)
      constant := (605518898803923434761701841254151472149471906962) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree070.table
  base := (98973104395249399947567673615673735127/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-36984437410804011638289692296169243000000000000)
      constant := (609137334689396305728814864843345766617613164092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207278490830159683921/50000000000000000000)
  centralHi := (414556981660319367843/100000000000000000000)
  directionLo := (417550211734234942667/100000000000000000000)
  directionHi := (104387552933558735667/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree071.table
  base := (24112875397262487112360143705810061653/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-37401764748538882259968879117873933000000000000)
      constant := (623408040087698198113142230525078349114204927880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree071.table
  base := (241110583324549304613935164680010772147/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-37513408459839469351676574160605783000000000000)
      constant := (627130670605337525358315554341451715140951412012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417550211734234942667/100000000000000000000)
  centralHi := (104387552933558735667/25000000000000000000)
  directionLo := (16820885474685070589/4000000000000000000)
  directionHi := (210261068433563382363/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree072.table
  base := (1553080176661241873505566387649732610369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-37929163350936303535444384995793123000000000000)
      constant := (641560756747230747408516237803029857620406148681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree072.table
  base := (776508433477405751095278441956359789083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-38042379508874927065063456025042323000000000000)
      constant := (645389059484587371244482387427512270314888898534) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16820885474685070589/4000000000000000000)
  centralHi := (210261068433563382363/50000000000000000000)
  directionLo := (84694641122395591301/20000000000000000000)
  directionHi := (211736602805988978253/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree073.table
  base := (2161664405204446587188360210005964906829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-38456561953333724810919890873712313000000000000)
      constant := (659977043263173778642408765398941288208985879221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree073.table
  base := (540402317581688298943911022074536595277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-38571350557910384778450337889478863000000000000)
      constant := (663912495945781293229728167737177095033468193492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84694641122395591301/20000000000000000000)
  centralHi := (211736602805988978253/50000000000000000000)
  directionLo := (42640385099958304897/10000000000000000000)
  directionHi := (426403850999583048971/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree074.table
  base := (2790261755696454097406384469207167977067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-38983960555731146086395396751631503000000000000)
      constant := (678656894894036160347766967079342781396144102083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree074.table
  base := (697553437271705382360260568318741213783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-39100321606945842491837219753915403000000000000)
      constant := (682700975368238859387400610439521534448760158268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42640385099958304897/10000000000000000000)
  centralHi := (426403850999583048971/100000000000000000000)
  directionLo := (429314491280302213449/100000000000000000000)
  directionHi := (8586289825606044269/2000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree075.table
  base := (429858390041399750179386830636392443319/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-39511359158128567361870902629550693000000000000)
      constant := (697600307566603052677804557541175509140258345848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree075.table
  base := (3438825328023864536459107518468177214009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-39629292655981300205224101618351943000000000000)
      constant := (701754493784482911792784722617886466951134263041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429314491280302213449/100000000000000000000)
  centralHi := (8586289825606044269/2000000000000000000)
  directionLo := (108051382655213726729/25000000000000000000)
  directionHi := (432205530620854906917/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree076.table
  base := (4107476111262853914502539036140761322441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (349022)
      previous := (174511)
      next := (174511)
      square := (1555894568162370143887818238220000000000000)
      linear := (-110910686317246505920627170380803000000000000)
      constant := (1985615727927399420561522240088687941761272169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree076.table
  base := (4107439735303495900524977727812918301273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (349022)
      previous := (174511)
      next := (174511)
      square := (1555894568162370143887818238220000000000000)
      linear := (-111241727714727861270390535963403000000000000)
      constant := (1997432265340563409729444621325836736527512057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108051382655213726729/25000000000000000000)
  centralHi := (432205530620854906917/100000000000000000000)
  directionLo := (217538679879719788129/50000000000000000000)
  directionHi := (435077359759439576259/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree077.table
  base := (2398042479588942227425002332740242280789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-40566156362923409912821914385389073000000000000)
      constant := (736277802533765263710935776567168865433145814522) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree077.table
  base := (4796053303080332034559716491131991961877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-40687234754052215631997865347225023000000000000)
      constant := (740656634453700663449902456720383924358006851773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217538679879719788129/50000000000000000000)
  centralHi := (435077359759439576259/100000000000000000000)
  directionLo := (437930356622185846853/100000000000000000000)
  directionHi := (218965178311092923427/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree078.table
  base := (5504690426154194531675971208121410075471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-41093554965320831188297420263308263000000000000)
      constant := (756011879240447534534418719644990991843274273479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree078.table
  base := (344041430134483359442637280971431843363/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-41216205803087673345384747211661563000000000000)
      constant := (760505251270426233988085930388626226632927695792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437930356622185846853/100000000000000000000)
  centralHi := (218965178311092923427/50000000000000000000)
  directionLo := (440764886903692611423/100000000000000000000)
  directionHi := (13773902715740394107/3125000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree079.table
  base := (1246657946159004090249310562224208456753/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-41620953567718252463772926141227453000000000000)
      constant := (776009505683815935482353964365939586048146115485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree079.table
  base := (6233265768669371211667903748872070326887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-41745176852123131058771629076098103000000000000)
      constant := (780618896081938955745558139044809123110105711263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440764886903692611423/100000000000000000000)
  centralHi := (13773902715740394107/3125000000000000000)
  directionLo := (443581304614176680291/100000000000000000000)
  directionHi := (110895326153544170073/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree080.table
  base := (1396376096781723732542412300901587609571/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-42148352170115673739248432019146643000000000000)
      constant := (796270679958611899851859977908048890688323921895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree080.table
  base := (3490929820602582322882030475242925140349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-42274147901158588772158510940534643000000000000)
      constant := (800997567037018327937371540983319630820492339402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443581304614176680291/100000000000000000000)
  centralHi := (110895326153544170073/25000000000000000000)
  directionLo := (446379952595549551917/100000000000000000000)
  directionHi := (223189976297774775959/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree081.table
  base := (7750460633248340002308721584292017122449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-42675750772513095014723937897065833000000000000)
      constant := (816795400428273389513942501099947720262279832601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree081.table
  base := (7750442506708799080362755321448078714301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-42803118950194046485545392804971183000000000000)
      constant := (821641262546308369938615949166507879422640618149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446379952595549551917/100000000000000000000)
  centralHi := (223189976297774775959/50000000000000000000)
  directionLo := (449161163008552119037/100000000000000000000)
  directionHi := (224580581504276059519/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree082.table
  base := (1067378552004611999080085426031182455261/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-43203149374910516290199443774985023000000000000)
      constant := (837583665687075418549590691040294331842123433512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree082.table
  base := (8539012654100661503606276527911682383649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-43332089999229504198932274669407723000000000000)
      constant := (842549981245310355432598444346357854205158511401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449161163008552119037/100000000000000000000)
  centralHi := (224580581504276059519/50000000000000000000)
  directionLo := (45192525779290671527/10000000000000000000)
  directionHi := (451925257792906715271/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree083.table
  base := (146055973721537126161150589388681874901/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-43730547977307937565674949652904213000000000000)
      constant := (858635474527603717179126115207595817237307363136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree083.table
  base := (9347568614421505950819301716849815486961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-43861061048264961912319156533844263000000000000)
      constant := (863723721962604202684034654989046150010261562489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45192525779290671527/10000000000000000000)
  centralHi := (451925257792906715271/100000000000000000000)
  directionLo := (11366813727557275953/2500000000000000000)
  directionHi := (454672549102291038121/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree084.table
  base := (407044841568640365155860566663579914871/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-44257946579705358841150455530823403000000000000)
      constant := (879950825912810333730927034977864415488349101975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree084.table
  base := (10176109126612539979613737483415951994627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-44390032097300419625706038398280803000000000000)
      constant := (885162483692559838718534638396971309502163306523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11366813727557275953/2500000000000000000)
  centralHi := (454672549102291038121/100000000000000000000)
  directionLo := (228701669857898784871/50000000000000000000)
  directionHi := (457403339715797569743/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree085.table
  base := (11024643462226345245105641219579063184567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-44785345182102780116625961408742593000000000000)
      constant := (901529718952005779996690197776512896857469769583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree085.table
  base := (11024633108130486333900790649527149931873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-44919003146335877339092920262717343000000000000)
      constant := (906866265571904209631507642539064268686022191977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228701669857898784871/50000000000000000000)
  centralHi := (457403339715797569743/100000000000000000000)
  directionLo := (230058961713706874303/50000000000000000000)
  directionHi := (460117923427413748607/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree086.table
  base := (1486643578494316010329635108906885138609/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-45312743784500201392101467286661783000000000000)
      constant := (923372152880233230042696568542529768675188867528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree086.table
  base := (11893139629714547440096400859937791049527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-45447974195371335052479802127153883000000000000)
      constant := (928835066859599221658696632069094764534654256623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230058961713706874303/50000000000000000000)
  centralHi := (460117923427413748607/100000000000000000000)
  directionLo := (462816585414941072029/100000000000000000000)
  directionHi := (46281658541494107203/10000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree087.table
  base := (1597704464074158323375387471484404489943/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-45840142386897622667576973164580973000000000000)
      constant := (945478127040548383424835958803896371008804443256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree087.table
  base := (511265115748747970964704231997215011497/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-45976945244406792765866683991590423000000000000)
      constant := (951068886919562850588120672772153641342581778825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462816585414941072029/100000000000000000000)
  centralHi := (46281658541494107203/10000000000000000000)
  directionLo := (93099920517932883647/20000000000000000000)
  directionHi := (116374900647416104559/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree088.table
  base := (1369010400869225865589510976582727210059/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-46367540989295043943052479042500163000000000000)
      constant := (967847640868795704181924487244507866309343394910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree088.table
  base := (1711262151938200962833026626426891946769/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-46505916293442250479253565856026963000000000000)
      constant := (973567725205831738952513659472729672448471938248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93099920517932883647/20000000000000000000)
  centralHi := (116374900647416104559/25000000000000000000)
  directionLo := (468167243927985174953/100000000000000000000)
  directionHi := (234083621963992587477/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree089.table
  base := (7309276454378555793222698200671751294081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-46894939591692465218527984920419353000000000000)
      constant := (990480693880529396347452997842516564295427198738) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree089.table
  base := (14618547007469620447019216241599344404073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-47034887342477708192640447720463503000000000000)
      constant := (996331581249820346947864994251539550095683609777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468167243927985174953/100000000000000000000)
  centralHi := (234083621963992587477/50000000000000000000)
  directionLo := (470819770786142364373/100000000000000000000)
  directionHi := (235409885393071182187/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree090.table
  base := (194587273639486425255557884837964818379/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-47422338194089886494003490798338543000000000000)
      constant := (1013377285659777006187728819482814999016121213680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree090.table
  base := (15566976765317395099129498935855448453307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-47563858391513165906027329584900043000000000000)
      constant := (1019360454649380452964215127365212086513641213843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470819770786142364373/100000000000000000000)
  centralHi := (235409885393071182187/50000000000000000000)
  directionLo := (473457437199064070521/100000000000000000000)
  directionHi := (236728718599532035261/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree091.table
  base := (3307078101605795163083031108164824674187/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-47949736796487307769478996676257733000000000000)
      constant := (1036537415849386094617323286763717509358028744815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree091.table
  base := (4133846514071799568406101761256831200731/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-48092829440548623619414211449336583000000000000)
      constant := (1042654345059406645475133616112901780636766940876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473457437199064070521/100000000000000000000)
  centralHi := (236728718599532035261/50000000000000000000)
  directionLo := (59510061270539549623/12500000000000000000)
  directionHi := (95216098032863279397/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree092.table
  base := (876188918742954898486282356263205099489/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-48477135398884729044954502554176923000000000000)
      constant := (1059961084142730982850584502361615933867648071220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree092.table
  base := (8761887254516486261367540955763821656307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-48621800489584081332801093313773123000000000000)
      constant := (1066213252183769382314954631926974273632000721686) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59510061270539549623/12500000000000000000)
  centralHi := (95216098032863279397/20000000000000000000)
  directionLo := (478689169912048276459/100000000000000000000)
  directionHi := (23934458495602413823/5000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree093.table
  base := (18532145161567123038617518938609203996701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-49004534001282150320430008432096113000000000000)
      constant := (1083648290276587984515347176149532997617965215749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree093.table
  base := (18532141804937963312959118375144883572267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-49150771538619539046187975178209663000000000000)
      constant := (1090037175768388051197691215314824048759820746883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478689169912048276459/100000000000000000000)
  centralHi := (23934458495602413823/5000000000000000000)
  directionLo := (120320927540441787499/25000000000000000000)
  directionHi := (481283710161767149997/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree094.table
  base := (9780245292410678455136723583198974625261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (57038)
      previous := (28519)
      next := (28519)
      square := (254267967001636768648031862380000000000000)
      linear := (-22422785243856754909871215169767000000000000)
      constant := (501402912641473301708391441860095159679438442) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree094.table
  base := (3912097534131185492232705184333491009771/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (57038)
      previous := (28519)
      next := (28519)
      square := (254267967001636768648031862380000000000000)
      linear := (-22489697866751922480568065659867000000000000)
      constant := (504357680215157520979265344555854951272636655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120320927540441787499/25000000000000000000)
  centralHi := (481283710161767149997/100000000000000000000)
  directionLo := (483864338366722322299/100000000000000000000)
  directionHi := (4838643383667223223/1000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree095.table
  base := (10304407200723263389530645397864886940747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (349022)
      previous := (174511)
      next := (174511)
      square := (1555894568162370143887818238220000000000000)
      linear := (-138668507496058151998285374481813000000000000)
      constant := (3135216939595819173414056825211277070504220246) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree095.table
  base := (10304405935853239605171371740899048589079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (349022)
      previous := (174511)
      next := (174511)
      square := (1555894568162370143887818238220000000000000)
      linear := (-139082309242909846185489581460063000000000000)
      constant := (3153684408524842025235274506052639496666551022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483864338366722322299/100000000000000000000)
  centralHi := (4838643383667223223/1000000000000000000)
  directionLo := (486431275946619220743/100000000000000000000)
  directionHi := (60803909493327402593/12500000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree096.table
  base := (10838558201379459504444441296742906433971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-50586729808474414146856526065853683000000000000)
      constant := (1156291133617401960145872569978612035985727479958) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree096.table
  base := (2167711420697563375323918065257326837173/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-50737684685725912186348620771519283000000000000)
      constant := (1163099043254564926927339308788928988289767716770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486431275946619220743/100000000000000000000)
  centralHi := (60803909493327402593/12500000000000000000)
  directionLo := (122246184627334606587/25000000000000000000)
  directionHi := (488984738509338426349/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree097.table
  base := (284567455121247513959701604937748478247/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-51114128410871835422332031943772873000000000000)
      constant := (1181032489152158031944210870189470310398367352240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree097.table
  base := (2276539450399364996386082138064709348981/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-51266655734761369899735502635955823000000000000)
      constant := (1187983030789038008704231575225937362556355494690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122246184627334606587/25000000000000000000)
  centralHi := (488984738509338426349/100000000000000000000)
  directionLo := (491524936062287832221/100000000000000000000)
  directionHi := (245762468031143916111/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree098.table
  base := (23873654268654669878651995848600498235007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-51641527013269256697807537821692063000000000000)
      constant := (1206037381675859205015957193855989935217008097143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree098.table
  base := (11936826307440171700956538889900220454843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-51795626783796827613122384500392363000000000000)
      constant := (1213132033962960311238882417180750420802988191014) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491524936062287832221/100000000000000000000)
  centralHi := (245762468031143916111/50000000000000000000)
  directionLo := (49405207321397428259/10000000000000000000)
  directionHi := (494052073213974282591/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree099.table
  base := (25001889847861708321617129193051643212647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-52168925615666677973283043699611253000000000000)
      constant := (1231305811083432150177889922625776846828282137503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree099.table
  base := (6250472103215889314592787046009069190083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-52324597832832285326509266364828903000000000000)
      constant := (1238546052675237504856091815589620494366249993068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49405207321397428259/10000000000000000000)
  centralHi := (494052073213974282591/100000000000000000000)
  directionLo := (99313269873268449971/20000000000000000000)
  directionHi := (3879424604424548827/781250000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree100.table
  base := (1046004121373057756325601900273634936449/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-52696324218064099248758549577530443000000000000)
      constant := (1256837777284769538299427114569435922660907965025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree100.table
  base := (26150101789289803432013787691949377053977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-52853568881867743039896148229265443000000000000)
      constant := (1264225086839223974123028989927166888782316904673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99313269873268449971/20000000000000000000)
  centralHi := (3879424604424548827/781250000000000000)
  directionLo := (249533979449195621687/50000000000000000000)
  directionHi := (3992543671187129947/800000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree101.table
  base := (27318293731171292805782325577282589645553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-53223722820461520524234055455449633000000000000)
      constant := (1282633280202616437030974579939536244330256594297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree101.table
  base := (341478658138219100532971080673092180433/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-53382539930903200753283030093701983000000000000)
      constant := (1290169136380675977999479690957062275395529233360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249533979449195621687/50000000000000000000)
  centralHi := (3992543671187129947/800000000000000000)
  directionLo := (125389272835387615833/25000000000000000000)
  directionHi := (501557091341550463333/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree102.table
  base := (5701292371071744154958503527775824180693/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-53751121422858941799709561333368823000000000000)
      constant := (1308692319770754647730576768061827459585347260785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree102.table
  base := (28506460918413281325311436213923437274671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-53911510979938658466669911958138523000000000000)
      constant := (1316378201235994207723849132097121752131249114279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125389272835387615833/25000000000000000000)
  centralHi := (501557091341550463333/100000000000000000000)
  directionLo := (252016965773629245393/50000000000000000000)
  directionHi := (504033931547258490787/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree103.table
  base := (14857303667867690934650289678646456584853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-54278520025256363075185067211288013000000000000)
      constant := (1335014895932443005827045557951936420314268879994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree103.table
  base := (14857303261529754686233057720164799631981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-54440482028974116180056793822575063000000000000)
      constant := (1342852281350714847230100384440694690103447232938) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252016965773629245393/50000000000000000000)
  centralHi := (504033931547258490787/100000000000000000000)
  directionLo := (253249329923583668197/50000000000000000000)
  directionHi := (101299731969433467279/20000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree104.table
  base := (30942730111352011136622321137645693277603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-54805918627653784350660573089207203000000000000)
      constant := (1361601008639077580933127895301617042458531234747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree104.table
  base := (30942729406529930697587847447138211491531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-54969453078009573893443675687011603000000000000)
      constant := (1369591376678214018813094443538464771615709904419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253249329923583668197/50000000000000000000)
  centralHi := (101299731969433467279/20000000000000000000)
  directionLo := (127237863051590942473/25000000000000000000)
  directionHi := (508951452206363769893/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree105.table
  base := (8047707532505054510688482519794026078881/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-55333317230051205626136078967126393000000000000)
      constant := (1388450657849040793205872973516970082710310298276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree105.table
  base := (6438165903758936496705611476641041257027/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-55498424127045031606830557551448143000000000000)
      constant := (1396595487178595458399158995523962011046874620615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127237863051590942473/25000000000000000000)
  centralHi := (508951452206363769893/100000000000000000000)
  directionLo := (31962030023123521969/6250000000000000000)
  directionHi := (102278496073995270301/20000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree106.table
  base := (33458907347072800562365145069485190622591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-55860715832448626901611584845045583000000000000)
      constant := (1415563843526712827057383201204174106276794570359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree106.table
  base := (33458906817062764258294089186766071388589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-56027395176080489320217439415884683000000000000)
      constant := (1423864612817735525452903968813388359862758909461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31962030023123521969/6250000000000000000)
  centralHi := (102278496073995270301/20000000000000000000)
  directionLo := (513821912003513831583/100000000000000000000)
  directionHi := (16056934750109807237/3125000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree107.table
  base := (34746961724298902139719128850002860166893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-56388114434846048177087090722964773000000000000)
      constant := (1442940565641622473138142793228219651837228655957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree107.table
  base := (34746961264753894791191259173229343445743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-56556366225115947033604321280321223000000000000)
      constant := (1451398753566463311287193118597150040201464309607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513821912003513831583/100000000000000000000)
  centralHi := (16056934750109807237/3125000000000000000)
  directionLo := (516239910827259436369/100000000000000000000)
  directionHi := (51623991082725943637/10000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree108.table
  base := (7210998645805874728404302155936352593443/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-56915513037243469452562596600883963000000000000)
      constant := (1470580824167717751141354011515774151196442634535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree108.table
  base := (2253437051913489866194067214932508981111/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-57085337274151404746991203144757763000000000000)
      constant := (1479197909399856751378140016421153423671647773424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516239910827259436369/100000000000000000000)
  centralHi := (51623991082725943637/10000000000000000000)
  directionLo := (5186466367450258883/1000000000000000000)
  directionHi := (518646636745025888301/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree109.table
  base := (9345750458337793320758173771958749722829/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-57442911639640890728038102478803153000000000000)
      constant := (1498484619082739433807621876659099106530881052884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree109.table
  base := (7476600297593327153743109055297392866521/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-57614308323186862460378085009194303000000000000)
      constant := (1507262080296638345245164327420913757720071524645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5186466367450258883/1000000000000000000)
  centralHi := (518646636745025888301/100000000000000000000)
  directionLo := (260521122983778851431/50000000000000000000)
  directionHi := (521042245967557702863/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree110.table
  base := (3873098751343261944615002203679865249407/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-57970310242038312003513608356722343000000000000)
      constant := (1526651950367682970463468214253054166132743627430) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree110.table
  base := (38730987214044094771277604563937814732669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-58143279372222320173764966873630843000000000000)
      constant := (1535591266238656404245523048957412651420752161381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260521122983778851431/50000000000000000000)
  centralHi := (521042245967557702863/100000000000000000000)
  directionLo := (523426891130850254277/100000000000000000000)
  directionHi := (261713445565425127139/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree111.table
  base := (20049475124471936623335148818438077323339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-58497708844435733278989114234641533000000000000)
      constant := (1555082818006336351420125346953749790646838724422) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree111.table
  base := (40098949989447361299125454777738575486699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-58672250421257777887151848738067383000000000000)
      constant := (1564185467210439737102534657663856344783292630851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523426891130850254277/100000000000000000000)
  centralHi := (261713445565425127139/50000000000000000000)
  directionLo := (525800721409639212657/100000000000000000000)
  directionHi := (262900360704819606329/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree112.table
  base := (8297378004511845741422979567260408809031/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-59025107446833154554464620112560723000000000000)
      constant := (1583777221984883209771558923489729664721764809595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree112.table
  base := (10371722449414392568634464925550568451671/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-59201221470293235600538730602503923000000000000)
      constant := (1593044683198815391378835431441281477044866349116) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (525800721409639212657/100000000000000000000)
  centralHi := (262900360704819606329/50000000000000000000)
  directionLo := (264081941313149568423/50000000000000000000)
  directionHi := (528163882626299136847/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree113.table
  base := (42894806819529679408494550848415184600889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-59552506049230575829940125990479913000000000000)
      constant := (1612735162291561965097952368063992652044794332161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree113.table
  base := (42894806624626386387387676162533859310909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-59730192519328693313925612466940463000000000000)
      constant := (1622168914192580536129699790092090910073625071141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264081941313149568423/50000000000000000000)
  centralHi := (528163882626299136847/100000000000000000000)
  directionLo := (106103303471075235797/20000000000000000000)
  directionHi := (265258258677688089493/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree114.table
  base := (22161350313657927547866203471826498938459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (349022)
      previous := (174511)
      next := (174511)
      square := (1555894568162370143887818238220000000000000)
      linear := (-166426328674869798075943578582823000000000000)
      constant := (4548356340488568169331758731126173972310111862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree114.table
  base := (5540337557302854871098307393707778119353/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (349022)
      previous := (174511)
      next := (174511)
      square := (1555894568162370143887818238220000000000000)
      linear := (-166922890771091831100588626956723000000000000)
      constant := (4574953352305320860737377595657190854925206216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106103303471075235797/20000000000000000000)
  centralHi := (265258258677688089493/50000000000000000000)
  directionLo := (532858765023966944449/100000000000000000000)
  directionHi := (10657175300479338889/2000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree115.table
  base := (9154114287054563495494716993438211671039/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-60607303254025418380891137746318293000000000000)
      constant := (1671441651850827846468493866485364537294291897555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree115.table
  base := (45770571288930207623543502630722116241539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-60788134617399608740699376195813543000000000000)
      constant := (1681212421159668706605891563926544078374699034011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (532858765023966944449/100000000000000000000)
  centralHi := (10657175300479338889/2000000000000000000)
  directionLo := (267595381004071743093/50000000000000000000)
  directionHi := (535190762008143486187/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree116.table
  base := (5904802404297425450587498920794362002799/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-61134701856422839656366643624237483000000000000)
      constant := (1701190201087732259744607732024953148478160478008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree116.table
  base := (23619209553792940328512154984985447534897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-61317105666435066454086258060250083000000000000)
      constant := (1711131697118095917635519961067309118302512155506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267595381004071743093/50000000000000000000)
  centralHi := (535190762008143486187/100000000000000000000)
  directionLo := (107502528345122626603/20000000000000000000)
  directionHi := (67189080215701641627/12500000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree117.table
  base := (24363122008502917717004831641062126630207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-61662100458820260931842149502156673000000000000)
      constant := (1731202286621001990086173646675351792138263883886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree117.table
  base := (48726243907158108619604120253930402211301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-61846076715470524167473139924686623000000000000)
      constant := (1741315988051735512448224687488848773812999771149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107502528345122626603/20000000000000000000)
  centralHi := (67189080215701641627/12500000000000000000)
  directionLo := (539824534724791299739/100000000000000000000)
  directionHi := (26991226736239564987/5000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree118.table
  base := (502340457767141992742556688986291271133/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-62189499061217682207317655380075863000000000000)
      constant := (1761477908445503129658100180806926750287373971700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree118.table
  base := (50234045681554434246715028302908569100853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-62375047764505981880860021789123163000000000000)
      constant := (1771765293955729067090833331773522784520906123997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (539824534724791299739/100000000000000000000)
  centralHi := (26991226736239564987/5000000000000000000)
  directionLo := (542126568770455550247/100000000000000000000)
  directionHi := (67765821096306943781/12500000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree119.table
  base := (1035236490161743184442779849390661742259/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-62716897663615103482793161257995053000000000000)
      constant := (1792017066556915629361637437611777782785134864550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree119.table
  base := (647022805320716470773678976004836776731/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-62904018813541439594246903653559703000000000000)
      constant := (1802479614825995604506400577480725546121388737520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542126568770455550247/100000000000000000000)
  centralHi := (67765821096306943781/12500000000000000000)
  directionLo := (10888377378522798691/2000000000000000000)
  directionHi := (544418868926139934551/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree120.table
  base := (53309580206580921976560641607643920746369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-63244296266012524758268667135914243000000000000)
      constant := (1822819760951616045772617326709730846955271212681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree120.table
  base := (1332739503379577727020032474349825271139/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-63432989862576897307633785517996243000000000000)
      constant := (1833458950659119132458053725222311212505780976440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10888377378522798691/2000000000000000000)
  centralHi := (544418868926139934551/100000000000000000000)
  directionLo := (54670155763341995231/10000000000000000000)
  directionHi := (546701557633419952311/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree121.table
  base := (54877312868399031672455986846971871106313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-63771694868409946033744173013833433000000000000)
      constant := (1853885991626576898957899924397761877141858195537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree121.table
  base := (6859664100820133141257678519675321272097/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-63961960911612355021020667382432783000000000000)
      constant := (1864703301452252165213438619195970372684899844424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54670155763341995231/10000000000000000000)
  centralHi := (546701557633419952311/100000000000000000000)
  directionLo := (17155461087132198991/3125000000000000000)
  directionHi := (548974754788230367713/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree122.table
  base := (11293004498076811111289380286771905399883/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-64299093470807367309219678891752623000000000000)
      constant := (1885215758579280297325736596874293524446156492335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree122.table
  base := (56465022436829571920047757929680596011491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-64490931960647812734407549246869323000000000000)
      constant := (1896212667203032966737886139584540092608767486459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17155461087132198991/3125000000000000000)
  centralHi := (548974754788230367713/100000000000000000000)
  directionLo := (110247715562870095119/20000000000000000000)
  directionHi := (137809644453587618899/25000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree123.table
  base := (29036354534962317788450353901886330897057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-64826492073204788584695184769671813000000000000)
      constant := (1916809061807643816009210917048165534375054415186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree123.table
  base := (11614541804709427808612230791926064735549/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-65019903009683270447794431111305863000000000000)
      constant := (1927987047909514572947267019414741843486494072505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110247715562870095119/20000000000000000000)
  centralHi := (137809644453587618899/25000000000000000000)
  directionLo := (69186642716773032709/12500000000000000000)
  directionHi := (553493141734184261673/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree124.table
  base := (1194007452097514736979689368082162733657/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-65353890675602209860170690647591003000000000000)
      constant := (1948665901309956899084447743700992086489602049650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree124.table
  base := (5970037256471607303162699984251445012261/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-65548874058718728161181312975742403000000000000)
      constant := (1960026443570103925183637093309234267735825221890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69186642716773032709/12500000000000000000)
  centralHi := (553493141734184261673/100000000000000000000)
  directionLo := (555738559236956178101/100000000000000000000)
  directionHi := (277869279618478089051/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree125.table
  base := (61348013093490229702287158025090694241527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-65881289277999631135646196525510193000000000000)
      constant := (1980786277084826299742907475190263111532211464623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree125.table
  base := (12269602611743406902471663055427589030659/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-66077845107754185874568194840178943000000000000)
      constant := (1992330854183509682883028287213809689724549944455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555738559236956178101/100000000000000000000)
  centralHi := (277869279618478089051/50000000000000000000)
  directionLo := (69746867593054617487/12500000000000000000)
  directionHi := (557974940744436939897/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree126.table
  base := (15753907633590051171943004835389435166511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-66408687880397052411121702403429383000000000000)
      constant := (2013170189131129282002365198423785024236396121756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree126.table
  base := (31507815252126468602234629837433249359949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-66606816156789643587955076704615483000000000000)
      constant := (2024900279748697485887914213336902267537683940202) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69746867593054617487/12500000000000000000)
  centralHi := (557974940744436939897/100000000000000000000)
  directionLo := (56020239447430781007/10000000000000000000)
  directionHi := (560202394474307810071/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree127.table
  base := (32351612463183322790265508640984713319267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-66936086482794473686597208281348573000000000000)
      constant := (2045817637447973487493284225741793443303472299766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree127.table
  base := (32351612450150432471319866225651151321909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-67135787205825101301341958569052023000000000000)
      constant := (2057734720264851610725176522787584553441010020282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56020239447430781007/10000000000000000000)
  centralHi := (560202394474307810071/100000000000000000000)
  directionLo := (562421026501266256603/100000000000000000000)
  directionHi := (140605256625316564151/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree128.table
  base := (33205398134318139639292405892723189096847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-67463485085191894962072714159267763000000000000)
      constant := (2078728622034662525453764234392080172844183086606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree128.table
  base := (6641079624607087012149155895276485196153/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-67664758254860559014728840433488563000000000000)
      constant := (2090834175731342114466853995566453682431870136970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562421026501266256603/100000000000000000000)
  centralHi := (140605256625316564151/25000000000000000000)
  directionLo := (282315470407985304337/50000000000000000000)
  directionHi := (22585237632638824347/4000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree129.table
  base := (2129323267515768376405402175878202860459/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-67990883687589316237548220037186953000000000000)
      constant := (2111903142890666476878983784115790463271845410912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree129.table
  base := (34069172270485338858559431580356114711643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-68193729303896016728115722297925103000000000000)
      constant := (2124198646147696687987407914748399421141369997414) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell031.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282315470407985304337/50000000000000000000)
  centralHi := (22585237632638824347/4000000000000000000)
  directionLo := (141708059845479097831/25000000000000000000)
  directionHi := (22673289575276655653/4000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree130.table
  base := (17471467450371028154710429414321296206763/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-68518282289986737513023725915106143000000000000)
      constant := (2145341200015596617868834533600814665855147790348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree130.table
  base := (69885869784575457078509335678803785368161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-68722700352931474441502604162361643000000000000)
      constant := (2157828131513576550509019165217619314838054621289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 130 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141708059845479097831/25000000000000000000)
  centralHi := (22673289575276655653/4000000000000000000)
  directionLo := (569025022190332356627/100000000000000000000)
  directionHi := (142256255547583089157/25000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree131.table
  base := (71653371991237297637332284224092394547329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-69045680892384158788499231793025333000000000000)
      constant := (2179042793409183765236759879019807478939372963721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree131.table
  base := (14330674395320388441739201721106334956467/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-69251671401966932154889486026798183000000000000)
      constant := (2191722631828755811845672435388023834023498263415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 131 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569025022190332356627/100000000000000000000)
  centralHi := (142256255547583089157/25000000000000000000)
  directionLo := (285604693656589918351/50000000000000000000)
  directionHi := (571209387313179836703/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree132.table
  base := (73440851129553236404244229091395575892693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-69573079494781580063974737670944523000000000000)
      constant := (2213007923071259731648781555251010981600052140157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree132.table
  base := (3672042555844314151445748087623546906579/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-69780642451002389868276367891234723000000000000)
      constant := (2225882147093103809915907515869273683142090339420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 132 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285604693656589918351/50000000000000000000)
  centralHi := (571209387313179836703/100000000000000000000)
  directionLo := (35836589434645931391/6250000000000000000)
  directionHi := (573385430954334902257/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree133.table
  base := (18812076804081940688513903258073729880401/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (349022)
      previous := (174511)
      next := (174511)
      square := (1555894568162370143887818238220000000000000)
      linear := (-194184149853681444153601782683833000000000000)
      constant := (6225032102497898753186621211578595977223223236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree133.table
  base := (3762415360268254875312156237986671718191/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (349022)
      previous := (174511)
      next := (174511)
      square := (1555894568162370143887818238220000000000000)
      linear := (-194763472299273816015687672453383000000000000)
      constant := (6261237333259196678063578773202067656509678380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 133 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35836589434645931391/6250000000000000000)
  centralHi := (573385430954334902257/100000000000000000000)
  directionLo := (115110649499805780709/20000000000000000000)
  directionHi := (287776623749514451773/50000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree134.table
  base := (77075740251546415687483605591533259966967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-70627876699576422614925749426782903000000000000)
      constant := (2281728791200617388082108891542679606127397867183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree134.table
  base := (15415148048411853911802898867820378684293/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-70838584549073305295050131620107803000000000000)
      constant := (2294996222469171038300597226501856482807053842785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 134 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115110649499805780709/20000000000000000000)
  centralHi := (287776623749514451773/50000000000000000000)
  directionLo := (144428232390404820941/25000000000000000000)
  directionHi := (115542585912323856753/20000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree135.table
  base := (19730787558817467349658282372431683466977/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-71155275301973843890401255304702093000000000000)
      constant := (2316484529667935930769412234258062974196229366692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree135.table
  base := (3946157511353005104020474776088636978953/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-71367555598108763008437013484544343000000000000)
      constant := (2329950782580979731875707220757706416904581817940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 135 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144428232390404820941/25000000000000000000)
  centralHi := (115542585912323856753/20000000000000000000)
  directionLo := (579864568031759073993/100000000000000000000)
  directionHi := (289932284015879536997/50000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree136.table
  base := (40395268583810739410703304283805382467121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-71682673904371265165876761182621283000000000000)
      constant := (2351503804403795447230965839515393874886046348658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree136.table
  base := (80790537160517489737989639754407023118473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-71896526647144220721823895348980883000000000000)
      constant := (2365170357642115614859034179635124634178803175377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 136 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (579864568031759073993/100000000000000000000)
  centralHi := (289932284015879536997/50000000000000000000)
  directionLo := (72751031514878773869/12500000000000000000)
  directionHi := (582008252119030190953/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree137.table
  base := (16535580209755328044751021092062036942133/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-72210072506768686441352267060540473000000000000)
      constant := (2386786615408335807045251014261989969987335093585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree137.table
  base := (82677901042629823702822982708875144962813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-72425497696179678435210777213417423000000000000)
      constant := (2400654947652736894091555153061588513975450264037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 137 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72751031514878773869/12500000000000000000)
  centralHi := (582008252119030190953/100000000000000000000)
  directionLo := (36509004337256409499/6250000000000000000)
  directionHi := (116828813879220510397/20000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree138.table
  base := (2114631046973842720369149867775754084397/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-72737471109166107716827772938459663000000000000)
      constant := (2422332962681731137355399276239955679253932130120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree138.table
  base := (84585241873635381241558263804742130394609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-72954468745215136148597659077853963000000000000)
      constant := (2436404552613033583541281911638490766141050552441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 138 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36509004337256409499/6250000000000000000)
  centralHi := (116828813879220510397/20000000000000000000)
  directionLo := (586272105840478084557/100000000000000000000)
  directionHi := (293136052920239042279/50000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree139.table
  base := (43256279829203125891412209242556153005791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-73264869711563528992303278816378853000000000000)
      constant := (2458142846224183645062221168683900500316630054318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree139.table
  base := (86512559653804988117523242281611035661729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-73483439794250593861984540942290503000000000000)
      constant := (2472419172523221652942354413643693608277410129321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 139 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586272105840478084557/100000000000000000000)
  centralHi := (293136052920239042279/50000000000000000000)
  directionLo := (588392445874875929903/100000000000000000000)
  directionHi := (36774527867179745619/6250000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree140.table
  base := (88459854387416446496232311608193663732809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-73792268313960950267778784694298043000000000000)
      constant := (2494216266035918352225891701218593873950064804241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree140.table
  base := (88459854383435771807699393018204661382343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-74012410843286051575371422806727043000000000000)
      constant := (2508698807383538046304164059237759659014688043007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 140 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (588392445874875929903/100000000000000000000)
  centralHi := (36774527867179745619/6250000000000000000)
  directionLo := (295252586203156256119/50000000000000000000)
  directionHi := (590505172406312512239/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree141.table
  base := (90427126066289460495028143264304386790197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (57038)
      previous := (28519)
      next := (28519)
      square := (254267967001636768648031862380000000000000)
      linear := (-33644032103376356515733042359537000000000000)
      constant := (1145565062072059128291555912655668383631261117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree141.table
  base := (45213563031422924675575123797297481133813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (57038)
      previous := (28519)
      next := (28519)
      square := (254267967001636768648031862380000000000000)
      linear := (-33744401037719107871778318094687000000000000)
      constant := (1152215236393950405496330929205833281378612986) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 141 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295252586203156256119/50000000000000000000)
  centralHi := (590505172406312512239/100000000000000000000)
  directionLo := (592610366863927657471/100000000000000000000)
  directionHi := (578721061390554353/97656250000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree142.table
  base := (46207187347674336503295748403776720931847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-74847065518755792818729796450136423000000000000)
      constant := (2567153714468222310014181719563384098160760916606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree142.table
  base := (92414374692369815802149339531765217694977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-75070352941356967002145186535600123000000000000)
      constant := (2582053121955583673745482678810246382085641713673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 142 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (592610366863927657471/100000000000000000000)
  centralHi := (578721061390554353/97656250000000000)
  directionLo := (9292314206806337341/1562500000000000000)
  directionHi := (23788324369424223593/4000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree143.table
  base := (47210800137465808781271452327172056608207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-75374464121153214094205302328055613000000000000)
      constant := (2604017743089318604857553088694560172740316127886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree143.table
  base := (47210800136177459141969847379456124035943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-75599323990392424715532068400036663000000000000)
      constant := (2619127801667856642187610055605653724812677418814) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 143 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9292314206806337341/1562500000000000000)
  centralHi := (23788324369424223593/4000000000000000000)
  directionLo := (298399239051718701747/50000000000000000000)
  directionHi := (119359695620687480699/20000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree144.table
  base := (96448802805386542339747654952061824326083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-75901862723550635369680808205974803000000000000)
      constant := (2641145307980745209086554165617744041747010562267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree144.table
  base := (48224401401578908484954912525376906745727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-76128295039427882428918950264473203000000000000)
      constant := (2656467496331339769366385648328144649814946500846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 144 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298399239051718701747/50000000000000000000)
  centralHi := (119359695620687480699/20000000000000000000)
  directionLo := (598881550678069492049/100000000000000000000)
  directionHi := (11977631013561389841/2000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree145.table
  base := (24623995571767374872120582994498938140941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-76429261325948056645156314083893993000000000000)
      constant := (2678536409142786056132370862188275682386221038036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree145.table
  base := (49247991142570924169260302328777211900363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-76657266088463340142305832128909743000000000000)
      constant := (2694072205946322797593221602687718340205465147974) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 145 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (598881550678069492049/100000000000000000000)
  centralHi := (11977631013561389841/2000000000000000000)
  directionLo := (24038296113279216549/4000000000000000000)
  directionHi := (300478701415990206863/50000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree146.table
  base := (20112627744068377457002463695897839458309/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-76956659928345477920631819961813183000000000000)
      constant := (2716191046575729342689012731612641261390945268705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree146.table
  base := (50281569359337359041659776215016506880707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-77186237137498797855692713993346283000000000000)
      constant := (2731941930513098953405731694044361759791025832886) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 146 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24038296113279216549/4000000000000000000)
  centralHi := (300478701415990206863/50000000000000000000)
  directionLo := (603026109131726769797/100000000000000000000)
  directionHi := (301513054565863384899/50000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree147.table
  base := (102650272105568379745184065625852925369349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-77484058530742899196107325839732373000000000000)
      constant := (2754109220279865877685742510529356480482861990701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree147.table
  base := (20530054420825312278082926564832459718737/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-77715208186534255569079595857782823000000000000)
      constant := (2770076670031963400737942532545525894351235509565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 147 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (603026109131726769797/100000000000000000000)
  centralHi := (301513054565863384899/50000000000000000000)
  directionLo := (605087742869196869683/100000000000000000000)
  directionHi := (151271935717299217421/25000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree148.table
  base := (13094672805389398451293949826895477427257/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-78011457133140320471582831717651563000000000000)
      constant := (2792290930255487695512042224978602551631109339144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree148.table
  base := (104757382441868317163778246621936981017951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-78244179235569713282466477722219363000000000000)
      constant := (2808476424503211944447888005222411637575784006999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 148 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605087742869196869683/100000000000000000000)
  centralHi := (151271935717299217421/25000000000000000000)
  directionLo := (303571188045954622397/50000000000000000000)
  directionHi := (121428475218381848959/20000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree149.table
  base := (106884469733348602581973877691469771378619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-78538855735537741747058337595570753000000000000)
      constant := (2830736176502886895118948621348035222216108342931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree149.table
  base := (53442234866135185195297069733874370257933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-78773150284605170995853359586655903000000000000)
      constant := (2847141193927139947673212802855393489875636825834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 149 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303571188045954622397/50000000000000000000)
  centralHi := (121428475218381848959/20000000000000000000)
  directionLo := (152297519908097862023/25000000000000000000)
  directionHi := (609190079632391448093/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree150.table
  base := (21806306795326756704238678695065873665251/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-79066254337935163022533843473489943000000000000)
      constant := (2869444959022354672075120917640528316942403723495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree150.table
  base := (10903153397570142337218813246224355549343/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-79302121333640628709240241451092443000000000000)
      constant := (2886070978304041431695406900155360486084680260070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 150 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152297519908097862023/25000000000000000000)
  centralHi := (609190079632391448093/100000000000000000000)
  directionLo := (122246184627334606587/20000000000000000000)
  directionHi := (76403865392084129117/12500000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree151.table
  base := (111198575173333749203272092955547315976619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-79593652940332584298009349351409133000000000000)
      constant := (2908417277814180515339872978220357159578238844931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree151.table
  base := (111198575172527562153433724597201725055847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-79831092382676086422627123315528983000000000000)
      constant := (2925265777634208331464868624019808833944060134303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 151 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122246184627334606587/20000000000000000000)
  centralHi := (76403865392084129117/12500000000000000000)
  directionLo := (38329060943245321153/6250000000000000000)
  directionHi := (613264975091925138449/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree152.table
  base := (22677118664761709452039924622904441928003/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (349022)
      previous := (174511)
      next := (174511)
      square := (1555894568162370143887818238220000000000000)
      linear := (-221941971032493090231259986784843000000000000)
      constant := (8165244135397926716169770955911325561094793135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree152.table
  base := (113385593323111489295872402958773879965619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (349022)
      previous := (174511)
      next := (174511)
      square := (1555894568162370143887818238220000000000000)
      linear := (-222604053827455800930786717950043000000000000)
      constant := (8212536265700636797165087733473967500844052371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 152 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38329060943245321153/6250000000000000000)
  centralHi := (613264975091925138449/100000000000000000000)
  directionLo := (153823075713319428759/25000000000000000000)
  directionHi := (615292302853277715037/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree153.table
  base := (115592588428414573275177248843335197135913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-80648450145127426848960361107247513000000000000)
      constant := (2987152524216051966968792193717550191120836685937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree153.table
  base := (115592588427811898269599735586304341801387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-80889034480747001849400887044402063000000000000)
      constant := (3004450421155492128379625284085647877565174261763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 153 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153823075713319428759/25000000000000000000)
  centralHi := (615292302853277715037/100000000000000000000)
  directionLo := (61731297266984409867/10000000000000000000)
  directionHi := (617312972669844098671/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree154.table
  base := (29454890121876004427648924787778470314639/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-81175848747524848124435866985166703000000000000)
      constant := (3026915451826662636566430638578641947995754223644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree154.table
  base := (117819560486982968282808926111392992637689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-81418005529782459562787768908838603000000000000)
      constant := (3044440265347177505129348922967261357585932455361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 154 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61731297266984409867/10000000000000000000)
  centralHi := (617312972669844098671/100000000000000000000)
  directionLo := (7741588121374767281/1250000000000000000)
  directionHi := (619327049709981382481/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree155.table
  base := (120066509501424421542968881092693318588907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-81703247349922269399911372863085893000000000000)
      constant := (3066941915710760699534382688334234959215405298243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree155.table
  base := (120066509500973961408669801898678393364323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-81946976578817917276174650773275143000000000000)
      constant := (3084695124493264532716754794091046363609986012027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 155 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7741588121374767281/1250000000000000000)
  centralHi := (619327049709981382481/100000000000000000000)
  directionLo := (77666824760726729413/12500000000000000000)
  directionHi := (124266919617162767061/20000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree156.table
  base := (15291679433814790527285313132257113194281/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-82230645952319690675386878741005083000000000000)
      constant := (3107231915868619313611310201749111094277329513352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree156.table
  base := (122333435470128906478147986446056876777241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-82475947627853374989561532637711683000000000000)
      constant := (3125214998594027556589067602949776828329134058209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 156 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77666824760726729413/12500000000000000000)
  centralHi := (124266919617162767061/20000000000000000000)
  directionLo := (623335680877045475943/100000000000000000000)
  directionHi := (77916960109630684493/12500000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree157.table
  base := (62310169197561494946564841327084849269163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-82758044554717111950862384618924273000000000000)
      constant := (3147785452300507429761624199081133030429689530374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree157.table
  base := (31155084598696589111391431264110278231977/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-83004918676888832702948414502148223000000000000)
      constant := (3165999887649736555461158669738015157563247306692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 157 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623335680877045475943/100000000000000000000)
  centralHi := (77916960109630684493/12500000000000000000)
  directionLo := (62533036015408682567/10000000000000000000)
  directionHi := (625330360154086825671/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree158.table
  base := (63463609137785099972804642461222279696697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-83285443157114533226337890496843463000000000000)
      constant := (3188602525006689626713508246943404412943702651906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree158.table
  base := (126927218275279207853659379222617051254783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-83533889725924290416335296366584763000000000000)
      constant := (3207049791660656997348136563191822013906075448567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 158 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62533036015408682567/10000000000000000000)
  centralHi := (625330360154086825671/100000000000000000000)
  directionLo := (78414837125064978403/12500000000000000000)
  directionHi := (25092747880020793089/4000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree159.table
  base := (25850815022437220294462053158455050226029/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-83812841759511954501813396374762653000000000000)
      constant := (3229683133987425990142990110057966368738483000105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree159.table
  base := (129254075111934572671664212246375809802339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-84062860774959748129722178231021303000000000000)
      constant := (3248364710627049737362755974795947422651065433211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 159 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78414837125064978403/12500000000000000000)
  centralHi := (25092747880020793089/4000000000000000000)
  directionLo := (629300751534923933137/100000000000000000000)
  directionHi := (314650375767461966569/50000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree160.table
  base := (26320181781058220594843195595046608520183/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-84340240361909375777288902252681843000000000000)
      constant := (3271027279242972029488770462061308694589057065835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree160.table
  base := (131600908905073694192247722848363177609309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-84591831823995205843109060095457843000000000000)
      constant := (3289944644549170950647511308737671647621365852741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 160 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (629300751534923933137/100000000000000000000)
  centralHi := (314650375767461966569/50000000000000000000)
  directionLo := (315638291466042713681/50000000000000000000)
  directionHi := (631276582932085427363/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree161.table
  base := (133967719655199809709757298592739389371573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-84867638964306797052764408130601033000000000000)
      constant := (3312634960773578626399579747483031808814971517277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree161.table
  base := (1674596495687648748551739736865298930389/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-85120802873030663556495941959894383000000000000)
      constant := (3331789593427272094777013250991044931839182212880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 161 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315638291466042713681/50000000000000000000)
  centralHi := (631276582932085427363/100000000000000000000)
  directionLo := (79155781180451393643/12500000000000000000)
  directionHi := (126649249888722229829/20000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree162.table
  base := (27270901472444198457469450862943309544097/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-85395037566704218328239914008520223000000000000)
      constant := (3354506178579492009688326326028038544763153042765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree162.table
  base := (17044313420257323141948463223686810213649/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-85649773922066121269882823824330923000000000000)
      constant := (3373899557261599896794225678230007835944513451208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 162 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79155781180451393643/12500000000000000000)
  centralHi := (126649249888722229829/20000000000000000000)
  directionLo := (317604904208983467379/50000000000000000000)
  directionHi := (635209808417966934759/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree163.table
  base := (138761272026657583008161645627940069640243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-85922436169101639603715419886439413000000000000)
      constant := (3396640932660953752415650538618707579594542140107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree163.table
  base := (138761272026517222713812028658158684194977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-86178744971101578983269705688767463000000000000)
      constant := (3416274536052396360753894395717535206052600213673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 163 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (317604904208983467379/50000000000000000000)
  centralHi := (635209808417966934759/100000000000000000000)
  directionLo := (637167316319960278803/100000000000000000000)
  directionHi := (159291829079990069701/25000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree164.table
  base := (70594006824403347637347970917959639990973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-86449834771499060879190925764358603000000000000)
      constant := (3439039223018200787367258994755653120902322855754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree164.table
  base := (5647520545947415741136226727605416232513/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-86707716020137036696656587553204003000000000000)
      constant := (3458914529799898792254793846890422471230031483425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 164 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (637167316319960278803/100000000000000000000)
  centralHi := (159291829079990069701/25000000000000000000)
  directionLo := (639118828749685940247/100000000000000000000)
  directionHi := (79889853593710742531/12500000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree165.table
  base := (2244292691077494719853596818226604282113/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-86977233373896482154666431642277793000000000000)
      constant := (3481701049651465437739654369364859523422670703168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree165.table
  base := (143634732228854834940281132936633327669761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-87236687069172494410043469417640543000000000000)
      constant := (3501819538504339836963646350780322443016923239689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 165 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (639118828749685940247/100000000000000000000)
  centralHi := (79889853593710742531/12500000000000000000)
  directionLo := (320532200230476238683/50000000000000000000)
  directionHi := (641064400460952477367/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree166.table
  base := (146101427767402090109006400428167704613333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-87504631976293903430141937520196983000000000000)
      constant := (3524626412560975460320545285293535923376197787517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree166.table
  base := (73050713883655751708835387192065133645953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-87765658118207952123430351282077083000000000000)
      constant := (3544989562165947530580087327847775370521663147794) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 166 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320532200230476238683/50000000000000000000)
  centralHi := (641064400460952477367/100000000000000000000)
  directionLo := (643004085379206988277/100000000000000000000)
  directionHi := (321502042689603494139/50000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree167.table
  base := (7429405013220696337630559475839941098503/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-88032030578691324705617443398116173000000000000)
      constant := (3567815311746954098854438582231239879781202376940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree167.table
  base := (18573512533041956102531582389309145914293/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-88294629167243409836817233146513623000000000000)
      constant := (3588424600784945358074467192610408516301656308456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 167 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (643004085379206988277/100000000000000000000)
  centralHi := (321502042689603494139/50000000000000000000)
  directionLo := (6449379366189746583/1000000000000000000)
  directionHi := (644937936618974658301/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree168.table
  base := (151094749720269537244738036153144871997343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-88559429181088745981092949276035363000000000000)
      constant := (3611267747209620145630233396546170039029409178007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree168.table
  base := (6043789988808075920122256027149395011463/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-88823600216278867550204115010950163000000000000)
      constant := (3632124654361552320357702455364911371562403947175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 168 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell031.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6449379366189746583/1000000000000000000)
  centralHi := (644937936618974658301/100000000000000000000)
  directionLo := (646866006500829070129/100000000000000000000)
  directionHi := (64686600650082907013/10000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree169.table
  base := (153621376135237790160463576257579340951763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-89086827783486167256568455153954553000000000000)
      constant := (3654983718949188009624256016476392317362642452587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree169.table
  base := (153621376135179345783229102375779532102311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (125996942)
      previous := (62998471)
      next := (62998471)
      square := (561677939106615621943502383997420000000000000)
      linear := (-89352571265314325263590996875386703000000000000)
      constant := (3676089722895983006822632256489859846595455804639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 169 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell031.Kernel169
