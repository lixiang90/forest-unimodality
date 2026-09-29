import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell160.Parameters
import ForestUnimodality.BinomialMassData.Q97_177.Batch000_049
import ForestUnimodality.BinomialMassData.Q97_177.Batch050_099
import ForestUnimodality.BinomialMassData.Q97_177.Batch100_149
import ForestUnimodality.BinomialMassData.Q49_89.Batch000_049
import ForestUnimodality.BinomialMassData.Q49_89.Batch050_099
import ForestUnimodality.BinomialMassData.Q49_89.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree000.table
  base := (779297127195672771376777621/25000000000000000000000000)
  polynomial :=
    { denominator := 177000000000000000000000000000000000000000
      center := (679)
      previous := (0)
      next := (560)
      square := (16278613648374260627904597174000000000000)
      linear := (-66299495805943536697046880720000000000000)
      constant := (5517423660545363221347585556680000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree000.table
  base := (779297127195672771376777621/25000000000000000000000000)
  polynomial :=
    { denominator := 89000000000000000000000000000000000000000
      center := (343)
      previous := (0)
      next := (280)
      square := (8185291608504571728155418918000000000000)
      linear := (-33337034614287993028458601040000000000000)
      constant := (2774297772816595066101328330760000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree001.table
  base := (44325780527527424466248258078109415877913/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-24821769675727687595317982898660000000000000)
      constant := (937948906705374680055540894583723260026090918) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree001.table
  base := (8834262482919383040989248262952550350089/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7921000000000000000000000000000000000000000
      center := (30527)
      previous := (0)
      next := (24920)
      square := (728490953156906883805832283702000000000000)
      linear := (-3769154658305079408892046546524000000000000)
      constant := (141806719884801331464749526262116302646109938) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49743693530738551289/100000000000000000000)
  directionHi := (4974369353073855129/10000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree002.table
  base := (26886157229918202747792890083500704496523/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-30085188088702031865007135984920000000000000)
      constant := (588750061356564076338942916308515714114379378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree002.table
  base := (53454577089303861521908482444756164652597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-22856566179692637191256388002440000000000000)
      constant := (444165230771224077119049480543753580213220837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49743693530738551289/100000000000000000000)
  centralHi := (4974369353073855129/10000000000000000000)
  directionLo := (562785648269609991/800000000000000000)
  directionHi := (17587051508425312219/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree003.table
  base := (34952505093294717226605512081129305250923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-35348606501676376134696289071180000000000000)
      constant := (410144391224443535282623875643803334735388889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree003.table
  base := (6939772856285638221779615490401266529159/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7921000000000000000000000000000000000000000
      center := (30527)
      previous := (0)
      next := (24920)
      square := (728490953156906883805832283702000000000000)
      linear := (-5373471813571975467610508654452000000000000)
      constant := (61857855291570058368930203117506432177468439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562785648269609991/800000000000000000)
  centralHi := (17587051508425312219/25000000000000000000)
  directionLo := (86158604551374444813/100000000000000000000)
  directionHi := (43079302275687222407/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree004.table
  base := (24223020740313250150612513978050701179303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-40612024914650720404385442157440000000000000)
      constant := (318910457446551092586251956705263472415461229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree004.table
  base := (48068228322708506780836342296434058526397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-61756303912054234969697397084160000000000000)
      constant := (481420053874955135907324938082374177587590637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86158604551374444813/100000000000000000000)
  centralHi := (43079302275687222407/50000000000000000000)
  directionLo := (99487387061477102579/100000000000000000000)
  directionHi := (4974369353073855129/5000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree005.table
  base := (17660840644353029356233962209951392072251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-45875443327625064674074595243700000000000000)
      constant := (274080154262350233250360762138772387410517193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree005.table
  base := (17520466603091787689496392488721810878387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-34888944844194357631644853811900000000000000)
      constant := (207219850152137050623785689859915463967703427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99487387061477102579/100000000000000000000)
  centralHi := (4974369353073855129/5000000000000000000)
  directionLo := (55615140093323962593/50000000000000000000)
  directionHi := (111230280186647925187/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree006.table
  base := (1065604289834668928889727401727416048407/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20886000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1920876410508162754092742466532000000000000)
      linear := (-20455544696239763577505499331984000000000000)
      constant := (102132932477278031139814947330749028967571505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree006.table
  base := (13212546725736609491650060445801864275109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-38899737732361597778441009081720000000000000)
      constant := (193409431670186694315803361623156566923138389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55615140093323962593/50000000000000000000)
  centralHi := (111230280186647925187/100000000000000000000)
  directionLo := (24369333414338802873/20000000000000000000)
  directionHi := (60923333535847007183/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree007.table
  base := (5111204990920532054304913465186237254061/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-56402280153573753213452901416220000000000000)
      constant := (252451126682417358333773144397249751288318046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree007.table
  base := (10136498704937220776884800295646670723499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-42910530620528837925237164351540000000000000)
      constant := (191564859506938283213340042143607278800835579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24369333414338802873/20000000000000000000)
  centralHi := (60923333535847007183/50000000000000000000)
  directionLo := (32902360594036678853/25000000000000000000)
  directionHi := (131609442376146715413/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree008.table
  base := (7865974010872458914652715355016432459361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-61665698566548097483142054502480000000000000)
      constant := (260194826108360066037826233651156604173106923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree008.table
  base := (7794460104966746795292662213958313080699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-46921323508696078072033319621360000000000000)
      constant := (197742565308999242422374860863003797912216779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32902360594036678853/25000000000000000000)
  centralHi := (131609442376146715413/100000000000000000000)
  directionLo := (140696412067402497751/100000000000000000000)
  directionHi := (17587051508425312219/12500000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree009.table
  base := (11970156329375226445779568240445007412477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-133858233959044883505662415177480000000000000)
      constant := (551578126590076565329748418994827212408497311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree009.table
  base := (2369454253507159713503744677976010878627/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15842000000000000000000000000000000000000000
      center := (61054)
      previous := (0)
      next := (49840)
      square := (1456981906313813767611664567404000000000000)
      linear := (-20372846558745327287531789956472000000000000)
      constant := (83944379027193516644311828084371982169604467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140696412067402497751/100000000000000000000)
  centralHi := (17587051508425312219/12500000000000000000)
  directionLo := (149231080592215653869/100000000000000000000)
  directionHi := (14923108059221565387/10000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree010.table
  base := (2216353044885158595913073976492325957371/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-72192535392496786022520360675000000000000000)
      constant := (297698546462682228840185985030018719945650706) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree010.table
  base := (8757609218699207431247788869954524332931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-109885818570061116731251260322000000000000000)
      constant := (453539426523681258905744710196909787241146451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149231080592215653869/100000000000000000000)
  centralHi := (14923108059221565387/10000000000000000000)
  directionLo := (39325842696629213483/25000000000000000000)
  directionHi := (157303370786516853933/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree011.table
  base := (3122596276545459312899876038230868016467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-77455953805471130292209513761260000000000000)
      constant := (325022446666799015079849316747174954695964881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree011.table
  base := (19217183894415034163645809212599826721/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7921000000000000000000000000000000000000000
      center := (30527)
      previous := (0)
      next := (24920)
      square := (728490953156906883805832283702000000000000)
      linear := (-11790740434639559702484357086164000000000000)
      constant := (49558770742561189973276259878198103278625312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39325842696629213483/25000000000000000000)
  centralHi := (157303370786516853933/100000000000000000000)
  directionLo := (164981167127889007391/100000000000000000000)
  directionHi := (5155661472746531481/3125000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree012.table
  base := (2000532942202782708981887198847875080173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-82719372218445474561898666847520000000000000)
      constant := (357194588487501128816005209916288359462246639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree012.table
  base := (3915659880626492235560622893744218012847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-125928990122730077318435881401280000000000000)
      constant := (545016970827445130250084982481827950879761087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (164981167127889007391/100000000000000000000)
  centralHi := (5155661472746531481/3125000000000000000)
  directionLo := (86158604551374444813/50000000000000000000)
  directionHi := (172317209102748889627/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree013.table
  base := (205988474798083864026139198198445666343/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10443000000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (960438205254081377046371233266000000000000)
      linear := (-17596558126283963766317563986756000000000000)
      constant := (78766606528504162379736946409460368093619949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree013.table
  base := (495888318287951074598959391815508223193/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-66975287949532278806014095970460000000000000)
      constant := (300626317461863830717296694892931281271823506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86158604551374444813/50000000000000000000)
  centralHi := (172317209102748889627/100000000000000000000)
  directionLo := (179353437656044176493/100000000000000000000)
  directionHi := (89676718828022088247/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree014.table
  base := (18453178801786205047352234762187719867/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10443000000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (960438205254081377046371233266000000000000)
      linear := (-18649241808878832620255394604008000000000000)
      constant := (86932640717937899745137688180019052717142162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree014.table
  base := (300904385119851511566420333620591363571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-141972161675399037905620502480560000000000000)
      constant := (663880632301563171164975924342528704190845891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179353437656044176493/100000000000000000000)
  centralHi := (89676718828022088247/50000000000000000000)
  directionLo := (186123858344707021563/100000000000000000000)
  directionHi := (46530964586176755391/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree015.table
  base := (-111116109771445416764683634610485311207/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10443000000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (960438205254081377046371233266000000000000)
      linear := (-19701925491473701474193225221260000000000000)
      constant := (95895495277960350746368025109812701895065299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree015.table
  base := (-58594679404440046042774012355871611613/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7921000000000000000000000000000000000000000
      center := (30527)
      previous := (0)
      next := (24920)
      square := (728490953156906883805832283702000000000000)
      linear := (-14999374745173351819921281302020000000000000)
      constant := (73258723746156111642268807489608281928826854) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186123858344707021563/100000000000000000000)
  centralHi := (46530964586176755391/25000000000000000000)
  directionLo := (38531299324679206039/20000000000000000000)
  directionHi := (48164124155849007549/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree016.table
  base := (-2411970226532828775417468578132753308959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-207546091740685703281310558385120000000000000)
      constant := (1056226079390788259989122930303519657194541163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree016.table
  base := (-2465939921534519874917062281243036152027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-158015333228067998492805123559840000000000000)
      constant := (807126113045968331182559985246593910639794133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38531299324679206039/20000000000000000000)
  centralHi := (48164124155849007549/25000000000000000000)
  directionLo := (198974774122954205159/100000000000000000000)
  directionHi := (4974369353073855129/2500000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree017.table
  base := (-444802034462628271469429774904317716501/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-109036464283317195910344432278820000000000000)
      constant := (580439082058998615008359513873266840346320228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree017.table
  base := (-1803119306783891911401940933520690649919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-83018459502201239393198717049740000000000000)
      constant := (443649601191925337733204932769772609361991601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198974774122954205159/100000000000000000000)
  centralHi := (4974369353073855129/2500000000000000000)
  directionLo := (205098502635588948323/100000000000000000000)
  directionHi := (51274625658897237081/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree018.table
  base := (-4570941510178120476876554588669437269833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-228599765392583080360067170730160000000000000)
      constant := (1272697728388262806509054846079565066591133981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree018.table
  base := (-230659796188135845324910771828129505801/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7921000000000000000000000000000000000000000
      center := (30527)
      previous := (0)
      next := (24920)
      square := (728490953156906883805832283702000000000000)
      linear := (-17405850478073695907998974463912000000000000)
      constant := (97294486749312151194559610415666772369100558) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205098502635588948323/100000000000000000000)
  centralHi := (51274625658897237081/25000000000000000000)
  directionLo := (211044618101103746627/100000000000000000000)
  directionHi := (52761154525275936657/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree019.table
  base := (-5466386207012307777714608260641973165851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-239126602218531768899445476902680000000000000)
      constant := (1391508909188370677730280810962775874229018007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree019.table
  base := (-550361913297330503592718041851219027829/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7921000000000000000000000000000000000000000
      center := (30527)
      previous := (0)
      next := (24920)
      square := (728490953156906883805832283702000000000000)
      linear := (-18208009055707143937358205517876000000000000)
      constant := (106392997790213641822758600394518494080566491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211044618101103746627/100000000000000000000)
  centralHi := (52761154525275936657/25000000000000000000)
  directionLo := (216827733178947308709/100000000000000000000)
  directionHi := (21682773317894730871/10000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree020.table
  base := (-3129351785119584660271934781695712171837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-124826719522240228719411891537600000000000000)
      constant := (758582996604288634362777358574751677789506209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree020.table
  base := (-3145713901479394612299216788887924529091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-95050838166702959833587182859200000000000000)
      constant := (580072138381100223122192707835218749805070189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216827733178947308709/100000000000000000000)
  centralHi := (21682773317894730871/10000000000000000000)
  directionLo := (222460560373295850373/100000000000000000000)
  directionHi := (111230280186647925187/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree021.table
  base := (-3479747305021534461512863247915042360953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-130090137935214572989101044623860000000000000)
      constant := (824773915549763634073519344883553212624567821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree021.table
  base := (-1747046948822006315688357306124657500343/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-99061631054870199980383338129020000000000000)
      constant := (630748075441913344640745889870883175879566194) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222460560373295850373/100000000000000000000)
  centralHi := (111230280186647925187/50000000000000000000)
  directionLo := (227954240951294539361/100000000000000000000)
  directionHi := (113977120475647269681/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree022.table
  base := (-3789212217701425459788445855514199511211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-135353556348188917258790197710120000000000000)
      constant := (894276745064077302305209499289785214504423527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree022.table
  base := (-1520705583625377778129037940817440439809/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15842000000000000000000000000000000000000000
      center := (61054)
      previous := (0)
      next := (49840)
      square := (1456981906313813767611664567404000000000000)
      linear := (-41228969577214976050871797359536000000000000)
      constant := (273581866095506649120072181232241054276272911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227954240951294539361/100000000000000000000)
  centralHi := (113977120475647269681/50000000000000000000)
  directionLo := (46663720817680575857/20000000000000000000)
  directionHi := (116659302044201439643/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree023.table
  base := (-8123555064576246405898403400605404691193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-281233949522326523056958701592760000000000000)
      constant := (1934098778637793792283289701751817758809871501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree023.table
  base := (-8145473508715804961704823989053727834113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-214166433662409360547951297337320000000000000)
      constant := (1479320246847038709936964980757485421825990927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46663720817680575857/20000000000000000000)
  centralHi := (116659302044201439643/50000000000000000000)
  directionLo := (47712474704144587757/20000000000000000000)
  directionHi := (119281186760361469393/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree024.table
  base := (-86016161326022338987639697005780023459/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10443000000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (960438205254081377046371233266000000000000)
      linear := (-29176078634827521159633700776528000000000000)
      constant := (208611341904973277851498296521942392150176630) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree024.table
  base := (-4310358977150278413530074399255761798279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-111094009719371920420771803938480000000000000)
      constant := (797837940835984616183510283649255110795832041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47712474704144587757/20000000000000000000)
  centralHi := (119281186760361469393/50000000000000000000)
  directionLo := (24369333414338802873/10000000000000000000)
  directionHi := (243693334143388028731/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree025.table
  base := (-281819608197980546165543904503275601367/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-151143811587111950067857656968900000000000000)
      constant := (1122269361776950675313604397950606686318790704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree025.table
  base := (-9034845959656018511798005803074111244151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-230209605215078321135135918416600000000000000)
      constant := (1716931998505803035737814792911349964835079929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24369333414338802873/10000000000000000000)
  centralHi := (243693334143388028731/100000000000000000000)
  directionLo := (248718467653692756449/100000000000000000000)
  directionHi := (4974369353073855129/2000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree026.table
  base := (-4689041628906091337927609020573689412539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-156407230000086294337546810055160000000000000)
      constant := (1204662835288773140662341085625228961464855223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree026.table
  base := (-469625913507902897437973982476887321963/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7921000000000000000000000000000000000000000
      center := (30527)
      previous := (0)
      next := (24920)
      square := (728490953156906883805832283702000000000000)
      linear := (-23823119099141280142872822895624000000000000)
      constant := (184305167958441787015331342610873151045462154) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248718467653692756449/100000000000000000000)
  centralHi := (4974369353073855129/2000000000000000000)
  directionLo := (126822031995707522621/50000000000000000000)
  directionHi := (253644063991415045243/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree027.table
  base := (-4842552568104148073401744282841275645957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-161670648413060638607235963141420000000000000)
      constant := (1290216653336251146308372061138058558429271049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree027.table
  base := (-1939525013488750018774370382753578089777/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15842000000000000000000000000000000000000000
      center := (61054)
      previous := (0)
      next := (49840)
      square := (1456981906313813767611664567404000000000000)
      linear := (-49250555353549456344464107899176000000000000)
      constant := (394800822155813292977523293905644907950876383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126822031995707522621/50000000000000000000)
  centralHi := (253644063991415045243/100000000000000000000)
  directionLo := (6461895341353083361/2500000000000000000)
  directionHi := (258475813654123334441/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree028.table
  base := (-9942569567492805203163090732885004027677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-333868133652069965753850232455360000000000000)
      constant := (2757827415662882205693517659549121902938969089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree028.table
  base := (-4976706814215441154510652482822647230319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-127137181272040881007956425017760000000000000)
      constant := (1054881785204641513123611736309001811288643201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6461895341353083361/2500000000000000000)
  centralHi := (258475813654123334441/100000000000000000000)
  directionLo := (32902360594036678853/12500000000000000000)
  directionHi := (10528755390091737233/4000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree029.table
  base := (-10153214148827385053095527035990667716571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-344394970478018654293228538627880000000000000)
      constant := (2941479408821526646356172212532609457035849047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree029.table
  base := (-10162594702612059364625887307945062544581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-262295948320416242309505160575160000000000000)
      constant := (2250308586628336631845653073187587159584373899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32902360594036678853/12500000000000000000)
  centralHi := (10528755390091737233/4000000000000000000)
  directionLo := (267877987778617546433/100000000000000000000)
  directionHi := (133938993889308773217/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree030.table
  base := (-5159663150767121239256639931764521563061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-177460903651983671416303422400200000000000000)
      constant := (1565682699303783904590597863821583101316953977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree030.table
  base := (-10327431222722772838608183747836793034127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-270317534096750722603097471114800000000000000)
      constant := (2395621234746029452894180476979384762376680033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267877987778617546433/100000000000000000000)
  centralHi := (133938993889308773217/50000000000000000000)
  directionLo := (2128573675031977011/781250000000000000)
  directionHi := (272457430404093057409/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree031.table
  base := (-10442817333767255976775560092133177984263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-365448644129916031371985150972920000000000000)
      constant := (3327465425229954741020665965696113222310341491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree031.table
  base := (-2089962463165306647435201243894246342869/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15842000000000000000000000000000000000000000
      center := (61054)
      previous := (0)
      next := (49840)
      square := (1456981906313813767611664567404000000000000)
      linear := (-55667823974617040579337956330888000000000000)
      constant := (509137310197378284534626721132597674718134651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2128573675031977011/781250000000000000)
  centralHi := (272457430404093057409/100000000000000000000)
  directionLo := (34620145514498051691/12500000000000000000)
  directionHi := (276961164115984413529/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree032.table
  base := (-10525284301143409146471274536799716650367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-375975480955864719911363457145440000000000000)
      constant := (3529762810636879282154518972822440559020217419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree032.table
  base := (-10531315066815005772606760815427230354279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-286360705649419683190282092194080000000000000)
      constant := (2700492043261495661036063125579080908363756041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34620145514498051691/12500000000000000000)
  centralHi := (276961164115984413529/100000000000000000000)
  directionLo := (281392824134804995503/100000000000000000000)
  directionHi := (17587051508425312219/6250000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree033.table
  base := (-5284030842200322429450202827310292425629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-193251158890906704225370881658980000000000000)
      constant := (1869121809422997547588884516111368616199156353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree033.table
  base := (-10573256069070875779416882656163637546897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-294382291425754163483874402733720000000000000)
      constant := (2860027282833657917448264354138507826991028863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281392824134804995503/100000000000000000000)
  centralHi := (17587051508425312219/6250000000000000000)
  directionLo := (142877881878758033649/50000000000000000000)
  directionHi := (285755763757516067299/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree034.table
  base := (-10572264564634639859466575304820446728159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-397029154607762096990120069490480000000000000)
      constant := (3952896205065420027838166120821120074817835563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree034.table
  base := (-423069378197890527783499728567416416411/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15842000000000000000000000000000000000000000
      center := (61054)
      previous := (0)
      next := (49840)
      square := (1456981906313813767611664567404000000000000)
      linear := (-60480775440417728755493342654672000000000000)
      constant := (604856712695201825777781965631511472828042345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (142877881878758033649/50000000000000000000)
  centralHi := (285755763757516067299/100000000000000000000)
  directionLo := (290053084049663870427/100000000000000000000)
  directionHi := (72513271012415967607/25000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree035.table
  base := (-10538824697132662368560157921713474152633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-407555991433710785529498375663000000000000000)
      constant := (4173710838974689138110173558400046189424053581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree035.table
  base := (-10542667816188375108299791510191217454601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-310425462978423124071059023813000000000000000)
      constant := (3193253616944343430996674270193275366542105479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290053084049663870427/100000000000000000000)
  centralHi := (72513271012415967607/25000000000000000000)
  directionLo := (73571914908476375559/25000000000000000000)
  directionHi := (294287659633905502237/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree036.table
  base := (-5234260326442985847036714424812107930789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-209041414129829737034438340917760000000000000)
      constant := (2200339694978470352520736156769367156878770473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree036.table
  base := (-81811110859805639575045242873332738671/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-159223524377378802182325667176320000000000000)
      constant := (1683465687728758576464200340483381208127168576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73571914908476375559/25000000000000000000)
  centralHi := (294287659633905502237/100000000000000000000)
  directionLo := (298462161184431307739/100000000000000000000)
  directionHi := (14923108059221565387/5000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree037.table
  base := (-518100150193354080877959558519039345227/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10443000000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (960438205254081377046371233266000000000000)
      linear := (-42860966508560816260825498800804000000000000)
      constant := (463379506408906576721130646365365344235588878) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree037.table
  base := (-10364837092006048956412332679121501672123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-326468634531092084658243644892280000000000000)
      constant := (3545311773413583155858536975038658585255113717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298462161184431307739/100000000000000000000)
  centralHi := (14923108059221565387/5000000000000000000)
  directionLo := (151289537563707205913/50000000000000000000)
  directionHi := (302579075127414411827/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree038.table
  base := (-2554953841823147103386700979758744936009/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-219568250955778425573816647090280000000000000)
      constant := (2436526092188235704862382956170878853266516026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree038.table
  base := (-10222246413427143956827708485297831519739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-334490220307426564951835955431920000000000000)
      constant := (3728390581858873032196729369884035876532147381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151289537563707205913/50000000000000000000)
  centralHi := (302579075127414411827/100000000000000000000)
  directionLo := (38330090120035251319/12500000000000000000)
  directionHi := (306640720960282010553/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree039.table
  base := (-10042411989871562975339780544468312564231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-449663338737505539687011600353080000000000000)
      constant := (5118446007120774805243082068656377411891735667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree039.table
  base := (-10044495867542030899034067753910054717263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-342511806083761045245428265971560000000000000)
      constant := (3916164270298942455984063061312698456584559777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38330090120035251319/12500000000000000000)
  centralHi := (306640720960282010553/100000000000000000000)
  directionLo := (310649266532405602521/100000000000000000000)
  directionHi := (155324633266202801261/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree040.table
  base := (-614385777561450388713375400458706370349/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-230095087781727114113194953262800000000000000)
      constant := (2684986284239474479297748630888077834995563144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree040.table
  base := (-983195755371736699572008633363665096791/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7921000000000000000000000000000000000000000
      center := (30527)
      previous := (0)
      next := (24920)
      square := (728490953156906883805832283702000000000000)
      linear := (-35053339186009552553902057651120000000000000)
      constant := (410862989133470813543883104792726408768318489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310649266532405602521/100000000000000000000)
  centralHi := (155324633266202801261/50000000000000000000)
  directionLo := (62921348314606741573/20000000000000000000)
  directionHi := (157303370786516853933/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree041.table
  base := (-9583413890142217120831010174011177058717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-470717012389402916765768212698120000000000000)
      constant := (5627628556249751868385443947838261277975818369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree041.table
  base := (-2396235529038755882542849776155746494759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-179277488818215002916306443525420000000000000)
      constant := (2152892492176723524063063907921050664030027922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62921348314606741573/20000000000000000000)
  centralHi := (157303370786516853933/50000000000000000000)
  directionLo := (7962876242652590367/2500000000000000000)
  directionHi := (318515049706103614681/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree042.table
  base := (-9302401365934951183916712472049157270779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-481243849215351605305146518870640000000000000)
      constant := (5891411202739656224081246537729030650621254903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree042.table
  base := (-4651854447161669079297157148013896695363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-183288281706382243063102598795240000000000000)
      constant := (2253813747563615245735571598787021924276029677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7962876242652590367/2500000000000000000)
  centralHi := (318515049706103614681/100000000000000000000)
  directionLo := (161187989576892558837/50000000000000000000)
  directionHi := (12895039166151404707/4000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree043.table
  base := (-8987356328298399196559311892743058347477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-491770686041300293844524825043160000000000000)
      constant := (6161318195242540030884988573559624241677297689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree043.table
  base := (-8988474396839591370178920194681929911043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-374598149189098966419797508130120000000000000)
      constant := (4714155708691300986719002503803104433174628397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161187989576892558837/50000000000000000000)
  centralHi := (12895039166151404707/4000000000000000000)
  directionLo := (40773901537442147787/12500000000000000000)
  directionHi := (326191212299537182297/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree044.table
  base := (-345538553257853817840962527904865983247/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20886000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1920876410508162754092742466532000000000000)
      linear := (-100459504573449796476780626243136000000000000)
      constant := (1287469520247449747896951799971079422684757895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree044.table
  base := (-1727883875144503937097738239621752376117/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15842000000000000000000000000000000000000000
      center := (61054)
      previous := (0)
      next := (49840)
      square := (1456981906313813767611664567404000000000000)
      linear := (-76523946993086689342677963733952000000000000)
      constant := (985073638661783624378064490765300099428777243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40773901537442147787/12500000000000000000)
  centralHi := (326191212299537182297/100000000000000000000)
  directionLo := (329962334255778014783/100000000000000000000)
  directionHi := (5155661472746531481/1562500000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree045.table
  base := (-4127939254576770462638438388901934065683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-256412179846598835461640718694100000000000000)
      constant := (3359748902941636312630507407200947102552072431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree045.table
  base := (-1651338946438594356213962632344535341093/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15842000000000000000000000000000000000000000
      center := (61054)
      previous := (0)
      next := (49840)
      square := (1456981906313813767611664567404000000000000)
      linear := (-78128264148353585401396425841880000000000000)
      constant := (1028252750738302310923636141896698935563202347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (329962334255778014783/100000000000000000000)
  centralHi := (5155661472746531481/1562500000000000000)
  directionLo := (333690840559943775559/100000000000000000000)
  directionHi := (8342271013998594389/2500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree046.table
  base := (-783972957601248641996890484605662352789/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10443000000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (960438205254081377046371233266000000000000)
      linear := (-52335119651914635946265974356072000000000000)
      constant := (700776745979262220250920103464119068049824473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree046.table
  base := (-7840426447016249530767710633748965959261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-398662906518102407300574439749040000000000000)
      constant := (5361841391945439328759847662927594440636693619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (333690840559943775559/100000000000000000000)
  centralHi := (8342271013998594389/2500000000000000000)
  directionLo := (168689072052461254233/50000000000000000000)
  directionHi := (337378144104922508467/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree047.table
  base := (-3695062503222571635223321799826447158039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-266939016672547524001019024866620000000000000)
      constant := (3651077717694204464476039600392582412328598723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree047.table
  base := (-923839962062823763585033223163559605881/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-203342246147218443797083375144340000000000000)
      constant := (2793550137484574027829646994740675777447266396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168689072052461254233/50000000000000000000)
  centralHi := (337378144104922508467/100000000000000000000)
  directionLo := (34102558139494740659/10000000000000000000)
  directionHi := (341025581394947406591/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree048.table
  base := (-6907155026653387247749391722015011662333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-544404870171043736541416355905760000000000000)
      constant := (7602660790438406615912685916682837233210256481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree048.table
  base := (-3453831144335267758391977495586636157489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-207353039035385683943879530414160000000000000)
      constant := (2908519853617661432059432009890098254996529631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34102558139494740659/10000000000000000000)
  centralHi := (341025581394947406591/100000000000000000000)
  directionLo := (344634418205497779253/100000000000000000000)
  directionHi := (172317209102748889627/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree049.table
  base := (-3195447516233327171254589551596082950781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-277465853498496212540397331039140000000000000)
      constant := (3954641368791984231670425447096212105744994017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree049.table
  base := (-1597831882965445017078578143114833305797/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-211363831923552924090675685683980000000000000)
      constant := (3025829554034294596741709543233284810769563926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (344634418205497779253/100000000000000000000)
  centralHi := (172317209102748889627/50000000000000000000)
  directionLo := (348205854715169859029/100000000000000000000)
  directionHi := (34820585471516985903/10000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree050.table
  base := (-73017600343424256869644542224575643459/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10443000000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (960438205254081377046371233266000000000000)
      linear := (-56545854382294111362017296825080000000000000)
      constant := (822202061887861458606240197493390052442861304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree050.table
  base := (-5841776629549406610670426628599667998833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-430749249623440328474943681907600000000000000)
      constant := (6290957992676236754518711012704862029781243807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (348205854715169859029/100000000000000000000)
  centralHi := (34820585471516985903/10000000000000000000)
  directionLo := (175870515084253122189/50000000000000000000)
  directionHi := (351741030168506244379/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree051.table
  base := (-5258746660309315984754930300473003423199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-575985380648889802159551274423320000000000000)
      constant := (8540873884512659389857847756476820425251532843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree051.table
  base := (-5259060679598103332295769559669892045781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-438770835399774808768535992447240000000000000)
      constant := (6534935956312079352084079053614074785105368699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (175870515084253122189/50000000000000000000)
  centralHi := (351741030168506244379/100000000000000000000)
  directionLo := (7104820542422786919/2000000000000000000)
  directionHi := (355241027121139345951/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree052.table
  base := (-145092341468543676287993809272341060437/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-293256108737419245349464790297920000000000000)
      constant := (4432921037517829785733827339651823076893702544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree052.table
  base := (-4643222343309008715070386904234346125363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-446792421176109289062128302986880000000000000)
      constant := (6783592661055950668264551368483239744340999677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7104820542422786919/2000000000000000000)
  centralHi := (355241027121139345951/100000000000000000000)
  directionLo := (179353437656044176493/50000000000000000000)
  directionHi := (358706875312088352987/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree053.table
  base := (-199703479669916881288165418122474023089/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10443000000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (960438205254081377046371233266000000000000)
      linear := (-59703905430078717923830788676836000000000000)
      constant := (919692480650161224644041499678008007553763146) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree053.table
  base := (-1997148619395428945519018010172517549943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-227407003476221884677860306763260000000000000)
      constant := (3518463912388405706039604677639613488486901497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179353437656044176493/50000000000000000000)
  centralHi := (358706875312088352987/100000000000000000000)
  directionLo := (181069777601234533813/50000000000000000000)
  directionHi := (362139555202469067627/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree054.table
  base := (-1656060691925166972591189796723927587467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-303782945563367933888843096470440000000000000)
      constant := (4767060879028189464495636843002292024204082119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree054.table
  base := (-414039388023808316099163867871132476621/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-231417796364389124824656462033080000000000000)
      constant := (3647470605959400328308557617325531038610740236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181069777601234533813/50000000000000000000)
  centralHi := (362139555202469067627/100000000000000000000)
  directionLo := (73108000243016408619/20000000000000000000)
  directionHi := (45692500151885255387/12500000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree055.table
  base := (-2597135974318593170254774125844630515371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-618092727952684556317064499113400000000000000)
      constant := (9877432661565813194901556842584304523527980647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree055.table
  base := (-2597300768794901161329764554919008921753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-470857178505112729942905234605800000000000000)
      constant := (7557632625809135547870427074213986530330794487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73108000243016408619/20000000000000000000)
  centralHi := (45692500151885255387/12500000000000000000)
  directionLo := (368909104705213560471/100000000000000000000)
  directionHi := (46113638088151695059/12500000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree056.table
  base := (-924567411159176463855738562428551407401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-314309782389316622428221402642960000000000000)
      constant := (5113428646474541708817656394219438637652511357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree056.table
  base := (-1849274963739184530740072826010574423681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-478878764281447210236497545145440000000000000)
      constant := (7825001902236495570699028787611090239990022799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (368909104705213560471/100000000000000000000)
  centralHi := (46113638088151695059/12500000000000000000)
  directionLo := (372247716689414043127/100000000000000000000)
  directionHi := (46530964586176755391/12500000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree057.table
  base := (-534067930186762376832545965397400895731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-319573200802290966697910555729220000000000000)
      constant := (5291197732468421194510458803442724942445881167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree057.table
  base := (-667659374257437863317964980008871101/6250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7921000000000000000000000000000000000000000
      center := (30527)
      previous := (0)
      next := (24920)
      square := (728490953156906883805832283702000000000000)
      linear := (-48690035005778169053008985568508000000000000)
      constant := (809704890409004535168024278529693957121436640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (372247716689414043127/100000000000000000000)
  centralHi := (46530964586176755391/12500000000000000000)
  directionLo := (375556650355924735473/100000000000000000000)
  directionHi := (187778325177962367737/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree058.table
  base := (-63538518867720094078315478894865235093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-324836619215265310967599708815480000000000000)
      constant := (5472023510509993625950401654095521844699847602) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree058.table
  base := (-25425532747531344921082521305452280477/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7921000000000000000000000000000000000000000
      center := (30527)
      previous := (0)
      next := (24920)
      square := (728490953156906883805832283702000000000000)
      linear := (-49492193583411617082368216622472000000000000)
      constant := (837377351688391029659142651814587512486341683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (375556650355924735473/100000000000000000000)
  centralHi := (187778325177962367737/50000000000000000000)
  directionLo := (3788366833777351387/1000000000000000000)
  directionHi := (378836683377735138701/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree059.table
  base := (592798006750295822319962261063195533883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1770000000000000000000000000000000000000000
      center := (6790)
      previous := (0)
      next := (5600)
      square := (162786136483742606279045971740000000000000)
      linear := (-11189831784008123906348774979720000000000000)
      constant := (191725624243953677279211741208748185609497291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree059.table
  base := (296355990718197032426152452992027439891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-251471760805225325558637238382180000000000000)
      constant := (4327587822510427421734112183399459849351376611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3788366833777351387/1000000000000000000)
  centralHi := (378836683377735138701/100000000000000000000)
  directionLo := (191044280023455807951/50000000000000000000)
  directionHi := (382088560046911615903/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree060.table
  base := (1472709917410828596237417918819678291243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-670726912082427999013956029976000000000000000)
      constant := (11685689783730176284645037506390233900395450649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree060.table
  base := (294527369985359790915581376066724034157/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15842000000000000000000000000000000000000000
      center := (61054)
      previous := (0)
      next := (49840)
      square := (1456981906313813767611664567404000000000000)
      linear := (-102193021477357026282173357460800000000000000)
      constant := (1788251041734613865135542466321424521074557597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191044280023455807951/50000000000000000000)
  centralHi := (382088560046911615903/100000000000000000000)
  directionLo := (38531299324679206039/10000000000000000000)
  directionHi := (385312993246792060391/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree061.table
  base := (2385572906319300654202998087384324726779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-681253748908376687553334336148520000000000000)
      constant := (12065680789652466256643058968322414503121753097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree061.table
  base := (1192755431043401170898561676079929826813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-259493346581559805852229548921820000000000000)
      constant := (4616006070589068885502957446719539124158185773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38531299324679206039/10000000000000000000)
  centralHi := (385312993246792060391/100000000000000000000)
  directionLo := (388510666276850711041/100000000000000000000)
  directionHi := (194255333138425355521/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree062.table
  base := (3331379659479140012001315990174022190373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-691780585734325376092712642321040000000000000)
      constant := (12451784771780070674236395833004827313734065239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree062.table
  base := (3331326989641469096009490115621151631231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-527008278939454091998051408383280000000000000)
      constant := (9527446386865094418284137875320315142070980751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (388510666276850711041/100000000000000000000)
  centralHi := (194255333138425355521/50000000000000000000)
  directionLo := (78336446908693147527/20000000000000000000)
  directionHi := (97920558635866434409/25000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree063.table
  base := (1077531015759366270456622738894274166083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-351153711280137032316045474246780000000000000)
      constant := (6422000833133011947501795644291915810232809538) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree063.table
  base := (2155039681412948148495577300926934456761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-267514932357894286145821859461460000000000000)
      constant := (4913778949619765735740644070526432247832003881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78336446908693147527/20000000000000000000)
  centralHi := (97920558635866434409/25000000000000000000)
  directionLo := (98707081782110036559/25000000000000000000)
  directionHi := (394828327128440146237/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree064.table
  base := (532180100604032281901427639407698121349/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10443000000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (960438205254081377046371233266000000000000)
      linear := (-71283425938622275317146925466608000000000000)
      constant := (1324233141973663378729921660792510591481247607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree064.table
  base := (1330440769775788938620787474020703774361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-271525725246061526292618014731280000000000000)
      constant := (5066173319734226961201162206852395989193426962) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98707081782110036559/25000000000000000000)
  centralHi := (394828327128440146237/100000000000000000000)
  directionLo := (198974774122954205159/50000000000000000000)
  directionHi := (397949548245908410319/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree065.table
  base := (6366406215614277404412146300040661521541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-723361096212171441710847560838600000000000000)
      constant := (13646773987570283060863861961951824628269452663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree065.table
  base := (1273274808694796335984961970345757746093/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15842000000000000000000000000000000000000000
      center := (61054)
      previous := (0)
      next := (49840)
      square := (1456981906313813767611664567404000000000000)
      linear := (-110214607253691506575765668000440000000000000)
      constant := (2088362515023074517347211531345808747106802653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198974774122954205159/50000000000000000000)
  centralHi := (397949548245908410319/100000000000000000000)
  directionLo := (40104647859718532371/10000000000000000000)
  directionHi := (401046478597185323711/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree066.table
  base := (7443936119243242964620545410438054101623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-733887933038120130250225867011120000000000000)
      constant := (14057329332459186230921615795052164598983248989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree066.table
  base := (930488604395030767325773477140512628271/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-279547311022396006586210325270920000000000000)
      constant := (5377977839542151956555825191348880002114138364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40104647859718532371/10000000000000000000)
  centralHi := (401046478597185323711/100000000000000000000)
  directionLo := (40411967663216136243/10000000000000000000)
  directionHi := (404119676632161362431/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree067.table
  base := (4277193864842967660388611599701506719983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-372207384932034409394802086591820000000000000)
      constant := (7236998711603791283396309812492252834676782469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree067.table
  base := (8554364596306118804961535240771025582767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-567116207821126493466012961081480000000000000)
      constant := (11074775928738171869520296297334527293641097407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40411967663216136243/10000000000000000000)
  centralHi := (404119676632161362431/100000000000000000000)
  directionLo := (407169679725004458403/100000000000000000000)
  directionHi := (101792419931251114601/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree068.table
  base := (1212219818601462212162480186415792570023/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-377470803345008753664491239678080000000000000)
      constant := (7448389116863746809884733547090480487235000756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree068.table
  base := (9697738939060308239395772779307752313029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-575137793597460973759605271621120000000000000)
      constant := (11398273305162806376468962777160576706071502709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (407169679725004458403/100000000000000000000)
  centralHi := (101792419931251114601/25000000000000000000)
  directionLo := (410197005271177896647/100000000000000000000)
  directionHi := (51274625658897237081/12500000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree069.table
  base := (434961859489777010115371489625163743929/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20886000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1920876410508162754092742466532000000000000)
      linear := (-153093688703193239173672157105736000000000000)
      constant := (3065134348439912945398883870021309924889252735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree069.table
  base := (10874029868003441936949880049649764860441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-583159379373795454053197582160760000000000000)
      constant := (11726447792552490584345869421721495787459553161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (410197005271177896647/100000000000000000000)
  centralHi := (51274625658897237081/12500000000000000000)
  directionLo := (103300537928029078683/25000000000000000000)
  directionHi := (413202151712116314733/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree070.table
  base := (1510406224651958709907777486894726338691/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-387997640170957442203869545850600000000000000)
      constant := (7880338965185924991392115056187566508619800452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree070.table
  base := (96665885723088725955033365122589148551/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15842000000000000000000000000000000000000000
      center := (61054)
      previous := (0)
      next := (49840)
      square := (1456981906313813767611664567404000000000000)
      linear := (-118236193030025986869357978540080000000000000)
      constant := (2411859875539396252965633013990400716141811775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103300537928029078683/25000000000000000000)
  centralHi := (413202151712116314733/100000000000000000000)
  directionLo := (208092799746653192511/50000000000000000000)
  directionHi := (416185599493306385023/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree071.table
  base := (13325367016455289713096811290583674608353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-786522117167863572947117397873720000000000000)
      constant := (16201796782973862301925872884466625313935030379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree071.table
  base := (6662677543530783383205651805792305773957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-299601275463232207320191101620020000000000000)
      constant := (6198414024776621251548698754634190854035513397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208092799746653192511/50000000000000000000)
  centralHi := (416185599493306385023/100000000000000000000)
  directionLo := (419147811960986942147/100000000000000000000)
  directionHi := (104786952990246735537/25000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree072.table
  base := (14600396921305048385269546420836260828443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-797048953993812261486495704046240000000000000)
      constant := (16649028287226938715750843014172633071831430249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree072.table
  base := (14600386817347102829776488840395145724779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-607224136702798894933974513779680000000000000)
      constant := (12739033798887901100374096732106049949285974459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (419147811960986942147/100000000000000000000)
  centralHi := (104786952990246735537/25000000000000000000)
  directionLo := (211044618101103746627/50000000000000000000)
  directionHi := (84417847240441498651/20000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree073.table
  base := (1590833848753889287263609256215246262227/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10443000000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (960438205254081377046371233266000000000000)
      linear := (-80757579081976095002587401021876000000000000)
      constant := (1710237243243508655462704423485889816716436561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree073.table
  base := (15908329931338776622591423366278211791901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-615245722479133375227566824319320000000000000)
      constant := (13085916617978743088025835095715069715603647821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211044618101103746627/50000000000000000000)
  centralHi := (84417847240441498651/20000000000000000000)
  directionLo := (425010303832557627937/100000000000000000000)
  directionHi := (212505151916278813969/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree074.table
  base := (17249190857622938736511933299804688860537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-818102627645709638565252316391280000000000000)
      constant := (17561829209643079463361294141606420365770587891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree074.table
  base := (8624591806724554048761338121041269916199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-311633654127733927760579567429480000000000000)
      constant := (6718738250182750018298842246781527899006212279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (425010303832557627937/100000000000000000000)
  centralHi := (212505151916278813969/50000000000000000000)
  directionLo := (213955715867748547/50000000000000000)
  directionHi := (427911431735497094001/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree075.table
  base := (18622953313356481267893192855210417692821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-828629464471658327104630622563800000000000000)
      constant := (18027398611350747482677465259659462391966129703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree075.table
  base := (18622947181139594152280459029533330106739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-631288894031802335814751445398600000000000000)
      constant := (13793713440641784463016407511430433507775479619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213955715867748547/50000000000000000)
  centralHi := (427911431735497094001/100000000000000000000)
  directionLo := (430793022756872224067/100000000000000000000)
  directionHi := (107698255689218056017/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree076.table
  base := (20029625253009410934197511647960529609439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-839156301297607015644008928736320000000000000)
      constant := (18499080631274223078726800007919811810711371477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree076.table
  base := (5007405015747548707955399565099314167741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-319655239904068408054171877969120000000000000)
      constant := (7077313717140689115399053586137663335045352922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430793022756872224067/100000000000000000000)
  centralHi := (107698255689218056017/25000000000000000000)
  directionLo := (216827733178947308709/50000000000000000000)
  directionHi := (433655466357894617419/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree077.table
  base := (10734603086108424008839075272028008332787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-424841569061777852091693617454420000000000000)
      constant := (9488437632073211906308434594805558491019294641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree077.table
  base := (1073460089019474882461105766326655902923/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7921000000000000000000000000000000000000000
      center := (30527)
      previous := (0)
      next := (24920)
      square := (728490953156906883805832283702000000000000)
      linear := (-64733206558447129640193606647788000000000000)
      constant := (1452021847749320034163385864154264882814106166) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216827733178947308709/50000000000000000000)
  centralHi := (433655466357894617419/100000000000000000000)
  directionLo := (27281196201848667311/6250000000000000000)
  directionHi := (436499139229578676977/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree078.table
  base := (22941695648013338230471158698643348333941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-860209974949504392722765541081360000000000000)
      constant := (19460782505550321445219509566060572486651345863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree078.table
  base := (11470845966123796078572681708006538371871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-327676825680402888347764188508760000000000000)
      constant := (7445243283550108807435154169917559790443590191) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27281196201848667311/6250000000000000000)
  centralHi := (436499139229578676977/100000000000000000000)
  directionLo := (439324405871382418827/100000000000000000000)
  directionHi := (109831101467845604707/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree079.table
  base := (1222354666274524882746140363730236781139/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10443000000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (960438205254081377046371233266000000000000)
      linear := (-87073681177545308126214384725388000000000000)
      constant := (1995080235177960772328266324702215725410869154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree079.table
  base := (1222354509111622588122075151662670075659/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7921000000000000000000000000000000000000000
      center := (30527)
      previous := (0)
      next := (24920)
      square := (728490953156906883805832283702000000000000)
      linear := (-66337523713714025698912068755716000000000000)
      constant := (1526543170043834406786311638850822019338589878) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (439324405871382418827/100000000000000000000)
  centralHi := (109831101467845604707/25000000000000000000)
  directionLo := (442131619136567964501/100000000000000000000)
  directionHi := (221065809568283982251/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree080.table
  base := (12992699453323423361033689507582033549941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-440631824300700884900761076713200000000000000)
      constant := (10223467399861126597833810623591679176362033863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree080.table
  base := (25985396248113071530260300400567807820489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-671396822913474737282712998096800000000000000)
      constant := (15645053875272027910523334085808897605746093369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (442131619136567964501/100000000000000000000)
  centralHi := (221065809568283982251/50000000000000000000)
  directionLo := (222460560373295850373/50000000000000000000)
  directionHi := (444921120746591700747/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree081.table
  base := (13778306070534736981652406021849856666661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-445895242713675229170450229799460000000000000)
      constant := (10474589923381597913953896560183308053169940823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree081.table
  base := (27556609892861443836906683241657652912487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-679418408689809217576305308636440000000000000)
      constant := (16029353089723770294463672764236590268719809527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222460560373295850373/50000000000000000000)
  centralHi := (444921120746591700747/100000000000000000000)
  directionLo := (55961655222080870201/12500000000000000000)
  directionHi := (447693241776646961609/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree082.table
  base := (2916073281814641452670644058279908036463/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10443000000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (960438205254081377046371233266000000000000)
      linear := (-90231732225329914688027876577144000000000000)
      constant := (2145753749070301487105448780985841079624783109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree082.table
  base := (29160730917222917619288583882408556386999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-687439994466143697869897619176080000000000000)
      constant := (16418329342215275128613380155744638175141419079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55961655222080870201/12500000000000000000)
  centralHi := (447693241776646961609/100000000000000000000)
  directionLo := (56306037889289029259/12500000000000000000)
  directionHi := (450448303114312234073/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree083.table
  base := (15398880380279066214849944940199865623969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-456422079539623917709828535971980000000000000)
      constant := (10986003864844981205420851003061477196711108267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree083.table
  base := (3849719894189057438757479533920165860049/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-347730790121239089081744964857860000000000000)
      constant := (8405991315709154631834853639519716535109792516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56306037889289029259/12500000000000000000)
  centralHi := (450448303114312234073/100000000000000000000)
  directionLo := (453186615893103525701/100000000000000000000)
  directionHi := (226593307946551762851/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree084.table
  base := (1623384790941893031196317673263276894941/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10443000000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (960438205254081377046371233266000000000000)
      linear := (-92337099590519652395903537811648000000000000)
      constant := (2249259056216315699898342469318112801227737726) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree084.table
  base := (4058461807554298005756261736696042074347/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-351741583009406329228541120127680000000000000)
      constant := (8605156478106834787539440909688037397083610348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (453186615893103525701/100000000000000000000)
  centralHi := (226593307946551762851/50000000000000000000)
  directionLo := (455908481902589078723/100000000000000000000)
  directionHi := (113977120475647269681/25000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree085.table
  base := (34170537866825117289360720381910008996471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-933897832731145212498413684289000000000000000)
      constant := (23019285986805104723833133637324786223950146653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree085.table
  base := (34170536718756554157143712731150331193259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-711504751795147138750674550795000000000000000)
      constant := (17613320315656918305108517760488941773381804539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455908481902589078723/100000000000000000000)
  centralHi := (113977120475647269681/25000000000000000000)
  directionLo := (57326774247074583281/12500000000000000000)
  directionHi := (458614193976596666249/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree086.table
  base := (561035731216649976053094865358741343253/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-472212334778546950518895995230760000000000000)
      constant := (11776047001251007344575558833426802747122914528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree086.table
  base := (17953142913848982438047416678757979048373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-359763168785740809522133430667320000000000000)
      constant := (9010502354474884556706530324930001952042162533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57326774247074583281/12500000000000000000)
  centralHi := (458614193976596666249/100000000000000000000)
  directionLo := (230652018180463507899/50000000000000000000)
  directionHi := (461304036360927015799/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree087.table
  base := (37674942521634780471178311146985939251383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-954951506383042589577170296634040000000000000)
      constant := (24091014608310627894075496806325914163602192669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree087.table
  base := (9418735425477981195918856676942370429987/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-363773961673908049668929585937140000000000000)
      constant := (9216683067708095428630402634633111032351854054) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230652018180463507899/50000000000000000000)
  centralHi := (461304036360927015799/100000000000000000000)
  directionLo := (463978285061880363327/100000000000000000000)
  directionHi := (7249660704091880677/1562500000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree088.table
  base := (616820390023167674289179320555412423363/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-482739171604495639058274301403280000000000000)
      constant := (12318023901715244548601783749239045501989753888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree088.table
  base := (1579060170758660103474110119535725563011/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15842000000000000000000000000000000000000000
      center := (61054)
      previous := (0)
      next := (49840)
      square := (1456981906313813767611664567404000000000000)
      linear := (-147113901824830115926290296482784000000000000)
      constant := (3770080918896490041775927857360628410923050655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463978285061880363327/100000000000000000000)
  centralHi := (7249660704091880677/1562500000000000000)
  directionLo := (46663720817680575857/10000000000000000000)
  directionHi := (466637208176805758571/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree089.table
  base := (2065548702610723970260243232979870494961/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10443000000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (960438205254081377046371233266000000000000)
      linear := (-97600518003493996665592690897908000000000000)
      constant := (2518719358718076721521082666366643575157755446) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree089.table
  base := (41310973467240146115629459680968146127117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 890000000000000000000000000000000000000000
      center := (3430)
      previous := (0)
      next := (2800)
      square := (81852916085045717281554189180000000000000)
      linear := (-8354956122477360223876896550040000000000000)
      constant := (216540675119780256781247344642386165005313413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46663720817680575857/10000000000000000000)
  centralHi := (466637208176805758571/100000000000000000000)
  directionLo := (14665033318993551173/3125000000000000000)
  directionHi := (469281066207793637537/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree090.table
  base := (8635669947646874446407439397890566049961/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20886000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1920876410508162754092742466532000000000000)
      linear := (-197306403372177731039061043030320000000000000)
      constant := (5148890391796175368781965034715771181259742723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree090.table
  base := (10794587311040984653174594827531107410487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-375806340338409770109318051746600000000000000)
      constant := (9849256304266885200790149177400747803596935054) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14665033318993551173/3125000000000000000)
  centralHi := (469281066207793637537/100000000000000000000)
  directionLo := (471910112359550561797/100000000000000000000)
  directionHi := (235955056179775280899/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree091.table
  base := (22539315985997306998788833125624213473667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-498529426843418671867341760662060000000000000)
      constant := (13153911459167138176729457440031623661305504481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree091.table
  base := (140870723608603985996115997372722166209/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7921000000000000000000000000000000000000000
      center := (30527)
      previous := (0)
      next := (24920)
      square := (728490953156906883805832283702000000000000)
      linear := (-75963426645315402051222841403284000000000000)
      constant := (2012958216274610980031325907898240632913327648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471910112359550561797/100000000000000000000)
  centralHi := (235955056179775280899/50000000000000000000)
  directionLo := (474524592822420191477/100000000000000000000)
  directionHi := (237262296411210095739/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree092.table
  base := (9402364142539602658143344638257622108101/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20886000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1920876410508162754092742466532000000000000)
      linear := (-201517138102557206454812365499328000000000000)
      constant := (5375461292962984134790375752052652347674898743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree092.table
  base := (47011820360381193886827054361116862907821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-767655852229488500805820724572480000000000000)
      constant := (20565328747991496876226878158141286671092850141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474524592822420191477/100000000000000000000)
  centralHi := (237262296411210095739/50000000000000000000)
  directionLo := (477124747041445877571/100000000000000000000)
  directionHi := (119281186760361469393/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree093.table
  base := (12244478981303294409848054084791249872787/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-509056263669367360406720066834580000000000000)
      constant := (13726451299027966336901485883186720044843029282) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree093.table
  base := (12244478906938368715468747028856838654101/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-387838719002911490549706517556060000000000000)
      constant := (10502876182003104060885218820211740037958268042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (477124747041445877571/100000000000000000000)
  centralHi := (119281186760361469393/25000000000000000000)
  directionLo := (239855403986153581253/50000000000000000000)
  directionHi := (479710807972307162507/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree094.table
  base := (127442293947918151149651011873229585083/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10443000000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (960438205254081377046371233266000000000000)
      linear := (-102863936416468340935281843984168000000000000)
      constant := (2803461131774012871613815801169901462280870760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree094.table
  base := (50976917328052225107649245422910988677857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-783699023782157461393005345651760000000000000)
      constant := (21450853010561977003827488008159597941317305297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239855403986153581253/50000000000000000000)
  centralHi := (479710807972307162507/100000000000000000000)
  directionLo := (48228300232490445661/10000000000000000000)
  directionHi := (482283002324904456611/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree095.table
  base := (10601765129637420071839182207363730184959/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20886000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1920876410508162754092742466532000000000000)
      linear := (-207833240198126419578439349202840000000000000)
      constant := (5724486524718418775306223556041999434321526837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree095.table
  base := (26504412718110070422278670514702280843491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-395860304779245970843298828095700000000000000)
      constant := (10950315343730162309579938592825706766561292211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48228300232490445661/10000000000000000000)
  centralHi := (482283002324904456611/100000000000000000000)
  directionLo := (242420775397656377257/50000000000000000000)
  directionHi := (96968310159062550903/20000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree096.table
  base := (3442102506829024105209849176100405407737/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-524846518908290393215787526093360000000000000)
      constant := (14608183257685776178189349679665412269383979928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree096.table
  base := (55073639930362247930185848393585214677279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-799742195334826421980189966731040000000000000)
      constant := (22355085394527820877585548421265108485458726959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242420775397656377257/50000000000000000000)
  centralHi := (96968310159062550903/20000000000000000000)
  directionLo := (24369333414338802873/5000000000000000000)
  directionHi := (487386668286776057461/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree097.table
  base := (1429284023555612051539055941003648085029/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10443000000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (960438205254081377046371233266000000000000)
      linear := (-106021987464252947497095335835924000000000000)
      constant := (2981641299286782044894681384940438387807831388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree097.table
  base := (28585680395622871572045197008775051042677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-403881890555580451136891138635340000000000000)
      constant := (11407108565806061372397680916261897179309044517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24369333414338802873/5000000000000000000)
  centralHi := (487386668286776057461/100000000000000000000)
  directionLo := (489918564120368803459/100000000000000000000)
  directionHi := (24495928206018440173/5000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree098.table
  base := (29650994064640953589095611890207532509469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-535373355734239081755165832265880000000000000)
      constant := (15211286027947582181206727897896357261996384767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree098.table
  base := (3706374250117610045949106516007553673157/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-407892683443747691283687293905160000000000000)
      constant := (11639012949289330707587485483442006661160612776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489918564120368803459/100000000000000000000)
  centralHi := (24495928206018440173/5000000000000000000)
  directionLo := (49243744223590874213/10000000000000000000)
  directionHi := (492437442235908742131/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree099.table
  base := (61465521654668233347733021415239516079591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-1081273548294426852049709970704280000000000000)
      constant := (31034843704288914406458828355210406266419168813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree099.table
  base := (61465521547175558877561925341236931385163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-823806952663829862860966898349960000000000000)
      constant := (23746511695307871438721343872648957733501876123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49243744223590874213/10000000000000000000)
  centralHi := (492437442235908742131/100000000000000000000)
  directionLo := (19797740055346680887/4000000000000000000)
  directionHi := (15466984418239594443/3125000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree100.table
  base := (15915490376080133780501724817958886130409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-545900192560187770294544138438400000000000000)
      constant := (15826613968951105725313790075487889295719722374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree100.table
  base := (63661961413633850218484910290426642216371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-831828538440164343154559208889600000000000000)
      constant := (24219674521692872486313473371570469432995874691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19797740055346680887/4000000000000000000)
  centralHi := (15466984418239594443/3125000000000000000)
  directionLo := (248718467653692756449/50000000000000000000)
  directionHi := (497436935307385512899/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree101.table
  base := (2635652306624818067903980608686723413033/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20886000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1920876410508162754092742466532000000000000)
      linear := (-220465444389264845825693316609864000000000000)
      constant := (6455544951320656390609933130238709263011518095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree101.table
  base := (32945653794559931018742554128913099137017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-419925062108249411724075759714620000000000000)
      constant := (12348757188818764590616260075699230658264311657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248718467653692756449/50000000000000000000)
  centralHi := (497436935307385512899/100000000000000000000)
  directionLo := (99983586583815661857/20000000000000000000)
  directionHi := (249958966459539154643/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree102.table
  base := (34076780063587782732605986202528544992271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-556427029386136458833922444610920000000000000)
      constant := (16454167080136577448315588238049525595354286053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree102.table
  base := (13630712012529653096471246174623918371309/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15842000000000000000000000000000000000000000
      center := (61054)
      previous := (0)
      next := (49840)
      square := (1456981906313813767611664567404000000000000)
      linear := (-169574341998566660748348765993776000000000000)
      constant := (5036006252610965346728031640390332057419138589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99983586583815661857/20000000000000000000)
  centralHi := (249958966459539154643/50000000000000000000)
  directionLo := (100477335693212749657/20000000000000000000)
  directionHi := (251193339233031874143/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree103.table
  base := (880608985982952017738699667396930086509/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10443000000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (960438205254081377046371233266000000000000)
      linear := (-112338089559822160620722319539436000000000000)
      constant := (3354505614880374820756708315548723127147307896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree103.table
  base := (35224359412106705338140789997604590887497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-427946647884583892017668070254260000000000000)
      constant := (12833612588932755195431061228627215964419863737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100477335693212749657/20000000000000000000)
  centralHi := (251193339233031874143/50000000000000000000)
  directionLo := (63105418961330611049/12500000000000000000)
  directionHi := (504843351690644888393/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree104.table
  base := (72776783910541571416101620984303130808751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-1133907732424170294746601501566880000000000000)
      constant := (34187890722096264128438471312972037595035786693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree104.table
  base := (36388391932322693792099428130277983392541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-431957440772751132164464225524080000000000000)
      constant := (13079548060998472647755342222024091906452317261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63105418961330611049/12500000000000000000)
  centralHi := (504843351690644888393/100000000000000000000)
  directionLo := (101457625596566018097/20000000000000000000)
  directionHi := (253644063991415045243/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree105.table
  base := (75137755214191259283068314301512064598879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-1144434569250118983285979807739400000000000000)
      constant := (34836837880059842959989024793551190490606093397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree105.table
  base := (9392219396936167096164099761163811616929/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-435968233660918372311260380793900000000000000)
      constant := (13327822047691080252993494447679464207270778436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101457625596566018097/20000000000000000000)
  centralHi := (253644063991415045243/50000000000000000000)
  directionLo := (254860589263230458521/50000000000000000000)
  directionHi := (509721178526460917043/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree106.table
  base := (77531632781536598304060687995790404425173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-1154961406076067671825358113911920000000000000)
      constant := (35491897622610432893424230576899799193412081639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree106.table
  base := (77531632748904189101483345251880827532329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-879958053098171224916113072127440000000000000)
      constant := (27156869097959046913711196394108068034883578009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254860589263230458521/50000000000000000000)
  centralHi := (509721178526460917043/100000000000000000000)
  directionLo := (512142670439091886343/100000000000000000000)
  directionHi := (64017833804886485793/12500000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree107.table
  base := (19989604151272489349890323617410290339259/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-582744121451008180182368210042220000000000000)
      constant := (18076534974834920298690343978878601324025763474) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree107.table
  base := (39979208288788821879096436054683679888873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-443989819437252852604852691333540000000000000)
      constant := (13831385564834841891934072413804939428399763033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512142670439091886343/100000000000000000000)
  centralHi := (64017833804886485793/12500000000000000000)
  directionLo := (51455276690594553899/10000000000000000000)
  directionHi := (514552766905945538991/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree108.table
  base := (659344853422786142665595758106056040711/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20886000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1920876410508162754092742466532000000000000)
      linear := (-235203015945593009780822945251392000000000000)
      constant := (7364070972232986605008895618478226580828624325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree108.table
  base := (16483621330930944014594561665719652780359/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15842000000000000000000000000000000000000000
      center := (61054)
      previous := (0)
      next := (49840)
      square := (1456981906313813767611664567404000000000000)
      linear := (-179200244930168037100659538641344000000000000)
      constant := (5634670038091954562919747330051061369673223639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51455276690594553899/10000000000000000000)
  centralHi := (514552766905945538991/100000000000000000000)
  directionLo := (6461895341353083361/1250000000000000000)
  directionHi := (516951627308246668881/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree109.table
  base := (42455351496614353254499837923820313847247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-593270958276956868721746516214740000000000000)
      constant := (18746876178513482877412164218582385537506800421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree109.table
  base := (42455351486838829061121812720382231394181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-452011405213587332898445001873180000000000000)
      constant := (14344303140139081044774149208521457654873307701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6461895341353083361/1250000000000000000)
  centralHi := (516951627308246668881/100000000000000000000)
  directionLo := (129834851836555331041/25000000000000000000)
  directionHi := (103867881469244264833/20000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree110.table
  base := (87436205545014519861655960196808302227767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-1197068753379862425982871338602000000000000000)
      constant := (38173262437191017229237748929849269100164570781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree110.table
  base := (43718102764267654873757006762817294276953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-456022198101754573045241157143000000000000000)
      constant := (14604269699538222602076710231047275787967744713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129834851836555331041/25000000000000000000)
  centralHi := (103867881469244264833/20000000000000000000)
  directionLo := (130429064789257297437/25000000000000000000)
  directionHi := (521716259157029189749/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree111.table
  base := (5624663395456833533420156639385927156447/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-603797795102905557261124822387260000000000000)
      constant := (19429442550797755821104687953946787898358208168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree111.table
  base := (44997307156710233981988835865834904310297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-460032990989921813192037312412820000000000000)
      constant := (14866574773404311635943726038182588277041862537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130429064789257297437/25000000000000000000)
  centralHi := (521716259157029189749/100000000000000000000)
  directionLo := (131020582856970531291/25000000000000000000)
  directionHi := (104816466285576425033/20000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree112.table
  base := (46292964667249293982929360331512061770683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-609061213515879901530813975473520000000000000)
      constant := (19775310175090908027121343277812700461071242569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree112.table
  base := (46292964661396919204274777196571628075407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-464043783878089053338833467682640000000000000)
      constant := (15131218361715409771050198306568283865985298847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131020582856970531291/25000000000000000000)
  centralHi := (104816466285576425033/20000000000000000000)
  directionLo := (526437769504586861649/100000000000000000000)
  directionHi := (10528755390091737233/2000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree113.table
  base := (95210150561216882410590892545327808446093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-1228649263857708491601006257119560000000000000)
      constant := (40248468182893899679350141909593598303602549199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree113.table
  base := (19042030110270713995695439994498654736151/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15842000000000000000000000000000000000000000
      center := (61054)
      previous := (0)
      next := (49840)
      square := (1456981906313813767611664567404000000000000)
      linear := (-187221830706502517394251849180984000000000000)
      constant := (6159280185780207610441470364913939844165052071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526437769504586861649/100000000000000000000)
  centralHi := (10528755390091737233/2000000000000000000)
  directionLo := (105756543099147215853/20000000000000000000)
  directionHi := (264391357747868039633/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree114.table
  base := (6263505792148503497800500567133410347/640000000000000000000000000000000000)
  polynomial :=
    { denominator := 20886000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1920876410508162754092742466532000000000000)
      linear := (-247835220136731436028076912658416000000000000)
      constant := (8190485719935609052724157335562696388292878125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree114.table
  base := (24466819498502360018805289701512763935617/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-472065369654423533632425778222280000000000000)
      constant := (15667521081589479574502643364939325206268044514) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105756543099147215853/20000000000000000000)
  centralHi := (264391357747868039633/50000000000000000000)
  directionLo := (531117308372759214749/100000000000000000000)
  directionHi := (2124469233491036859/400000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree115.table
  base := (502786558264316358942276282845460336751/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10443000000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (960438205254081377046371233266000000000000)
      linear := (-124970293750960586867976286946460000000000000)
      constant := (4166250160048260412671490039687152845933813860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree115.table
  base := (100557311645860938715614612466798640566007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-952152325085181547558443866984200000000000000)
      constant := (31878360426225765892917536960303012031923341447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531117308372759214749/100000000000000000000)
  centralHi := (2124469233491036859/400000000000000000)
  directionLo := (66680210508254040693/12500000000000000000)
  directionHi := (106688336813206465109/20000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree116.table
  base := (51640125754038978811357657447296494643283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-630114887167777278609570587818560000000000000)
      constant := (21189343592628893908876340918370597293559804369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree116.table
  base := (103280251502178620060728115341170621039473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-960173910861516027852036177523840000000000000)
      constant := (32426355718003996343453942377137732489253665633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66680210508254040693/12500000000000000000)
  centralHi := (106688336813206465109/20000000000000000000)
  directionLo := (535755975557235092867/100000000000000000000)
  directionHi := (133938993889308773217/25000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree117.table
  base := (26509024390839477174551518948172815602279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-635378305580751622879259740904820000000000000)
      constant := (21550492676977745245293898813084107426669199194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree117.table
  base := (106036097558388193697495740385601343676067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-968195496637850508145628488063480000000000000)
      constant := (32979028038477417546252607772270728243258126707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535755975557235092867/100000000000000000000)
  centralHi := (133938993889308773217/25000000000000000000)
  directionLo := (538060312968132529479/100000000000000000000)
  directionHi := (13451507824203313237/2500000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree118.table
  base := (54412424907121596135618423232507357861179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 885000000000000000000000000000000000000000
      center := (3395)
      previous := (0)
      next := (2800)
      square := (81393068241871303139522985870000000000000)
      linear := (-10858334304978406222863540576120000000000000)
      constant := (371435560224823195487948185256433802341428683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree118.table
  base := (10882484981005691467438917099414099387351/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7921000000000000000000000000000000000000000
      center := (30527)
      previous := (0)
      next := (24920)
      square := (728490953156906883805832283702000000000000)
      linear := (-97621708241418498843922079860312000000000000)
      constant := (3353637738761091772855247734986627081247207271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538060312968132529479/100000000000000000000)
  centralHi := (13451507824203313237/2500000000000000000)
  directionLo := (270177411822974556691/50000000000000000000)
  directionHi := (540354823645949113383/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree119.table
  base := (111646508256407993737477214480684007538163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-1291810284813400622837276094154680000000000000)
      constant := (44563919442933553066809924041998443090721036209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree119.table
  base := (27911627063220475916632789188043527933217/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-492119334095259734366406554571380000000000000)
      constant := (17049201882685206891610599204695095569518023714) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270177411822974556691/50000000000000000000)
  centralHi := (540354823645949113383/100000000000000000000)
  directionLo := (542639632245493848681/100000000000000000000)
  directionHi := (271319816122746924341/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree120.table
  base := (11450107288564989549997627264805453350431/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10443000000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (960438205254081377046371233266000000000000)
      linear := (-130233712163934931137665440032720000000000000)
      constant := (4530455536312485264131895384758363349338550933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree120.table
  base := (1789079263791876391986515139045355615361/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-496130126983426974513202709841200000000000000)
      constant := (17332553585861385800109924557164104378536783392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542639632245493848681/100000000000000000000)
  centralHi := (271319816122746924341/50000000000000000000)
  directionLo := (544914860808186114817/100000000000000000000)
  directionHi := (272457430404093057409/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree121.table
  base := (117388543697880623191548280768267234144703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-1312863958465297999916032706499720000000000000)
      constant := (46051303867060341941888454592118074726173133429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree121.table
  base := (29347135923844878360227387802695478865027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-500140919871594214659998865111020000000000000)
      constant := (17618243803317868602114090741166811776179757734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544914860808186114817/100000000000000000000)
  centralHi := (272457430404093057409/50000000000000000000)
  directionLo := (136795157209531016047/25000000000000000000)
  directionHi := (547180628838124064189/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree122.table
  base := (60154460344559013867308066877880164945337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-661695397645623344227705506336120000000000000)
      constant := (23402082477349217692850644283596622562524154291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree122.table
  base := (60154460343505894187762617325373854977333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-504151712759761454806795020380840000000000000)
      constant := (17906272535038938495553719865481926305275454693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136795157209531016047/25000000000000000000)
  centralHi := (547180628838124064189/100000000000000000000)
  directionLo := (274718526687664864099/50000000000000000000)
  directionHi := (549437053375329728199/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree123.table
  base := (123262203855479109401176654985543312321047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-1333917632117195376994789318844760000000000000)
      constant := (47563138625998582806597918599314368810568693821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree123.table
  base := (123262203853705518102597764787879144153093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-1016325011295857389907182351301320000000000000)
      constant := (36393279562018525634817816338871570700836649653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274718526687664864099/50000000000000000000)
  centralHi := (549437053375329728199/100000000000000000000)
  directionLo := (551684249066297858057/100000000000000000000)
  directionHi := (275842124533148929029/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree124.table
  base := (126248393193173921537661644719003157026443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-1344444468943144065534167625017280000000000000)
      constant := (48328224880921205791675131978611109968827144249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree124.table
  base := (63124196595840270137865434341303015574243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-512173298536095935100387330920480000000000000)
      constant := (18489345541213870234706753214051221186363578803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551684249066297858057/100000000000000000000)
  centralHi := (275842124533148929029/50000000000000000000)
  directionLo := (553922328231968827057/100000000000000000000)
  directionHi := (276961164115984413529/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree125.table
  base := (129267488698500217958878924939184452408977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-1354971305769092754073545931189800000000000000)
      constant := (49099423719427641784020966790052403236506946811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree125.table
  base := (64633744348621428993711208811192694822217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-516184091424263175247183486190300000000000000)
      constant := (18784389815638130672695092818562207335686780857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553922328231968827057/100000000000000000000)
  centralHi := (276961164115984413529/50000000000000000000)
  directionLo := (556151400933239625933/100000000000000000000)
  directionHi := (278075700466619812967/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree126.table
  base := (66159745183919365019950920804243322991261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-682749071297520721306462118681160000000000000)
      constant := (24938367570740047380692656992761793021997738623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree126.table
  base := (26463898073356031415522025340740978367427/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15842000000000000000000000000000000000000000
      center := (61054)
      previous := (0)
      next := (49840)
      square := (1456981906313813767611664567404000000000000)
      linear := (-208077953724972166157591856584048000000000000)
      constant := (7632709041707095024457200121443353289648389267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556151400933239625933/100000000000000000000)
  centralHi := (278075700466619812967/50000000000000000000)
  directionLo := (558371575034121064691/100000000000000000000)
  directionHi := (139592893758530266173/25000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree127.table
  base := (27080879639529795590665606103829610077471/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20886000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1920876410508162754092742466532000000000000)
      linear := (-275204995884198026230460508706968000000000000)
      constant := (10132031829408318298586122135120600618039029653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree127.table
  base := (264461715228042617385871966305750367931/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (152635)
      previous := (0)
      next := (124600)
      square := (3642454765784534419029161418510000000000000)
      linear := (-524205677200597655540775796729940000000000000)
      constant := (19381493907088692047660632210670199258081651456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558371575034121064691/100000000000000000000)
  centralHi := (139592893758530266173/25000000000000000000)
  directionLo := (560582956262643727787/100000000000000000000)
  directionHi := (140145739065660931947/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree128.table
  base := (69261106092232767951948647587724903127253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (200305)
      previous := (0)
      next := (165200)
      square := (4802191026270406885231856166330000000000000)
      linear := (-693275908123469409845840424853680000000000000)
      constant := (25724847868037971268538477314142931163357903079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree128.table
  base := (1731527652296442033006970267234523745603/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7921000000000000000000000000000000000000000
      center := (30527)
      previous := (0)
      next := (24920)
      square := (728490953156906883805832283702000000000000)
      linear := (-105643294017752979137514390399952000000000000)
      constant := (3936710744817457776741518699522405300711370904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell160.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560582956262643727787/100000000000000000000)
  centralHi := (140145739065660931947/25000000000000000000)
  directionLo := (281392824134804995503/50000000000000000000)
  directionHi := (562785648269609991007/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree129.table
  base := (141672932324894684097859322307421060080651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (400610)
      previous := (0)
      next := (330400)
      square := (9604382052540813770463712332660000000000000)
      linear := (-1397078653072887508231059155879880000000000000)
      constant := (52245344908547707278018211322093858130422238393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree129.table
  base := (141672932324263229620115378105481607878233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (305270)
      previous := (0)
      next := (249200)
      square := (7284909531569068838058322837020000000000000)
      linear := (-1064454525953864271668736214539160000000000000)
      constant := (39975904110500207472822905142483339816003483593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell160.Kernel129
