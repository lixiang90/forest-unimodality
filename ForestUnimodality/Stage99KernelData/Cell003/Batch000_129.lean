import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell003.Parameters
import ForestUnimodality.BinomialMassData.Q19_70.Batch000_049
import ForestUnimodality.BinomialMassData.Q19_70.Batch050_099
import ForestUnimodality.BinomialMassData.Q19_70.Batch100_149
import ForestUnimodality.BinomialMassData.Q39_140.Batch000_049
import ForestUnimodality.BinomialMassData.Q39_140.Batch050_099
import ForestUnimodality.BinomialMassData.Q39_140.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree000.table
  base := (62074109397817529717888973/12500000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (9903687354770056294750446500000000000000)
      constant := (1738075063138890832100891244000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree000.table
  base := (62074109397817529717888973/12500000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (19807374709540112589500893000000000000000)
      constant := (3476150126277781664201782488000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree001.table
  base := (2282061723031786561477899786116191007653/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (6090251915719534607507323910000000000000)
      constant := (1275783958853948315662317468526566964285680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree001.table
  base := (18086119754339154043143589103036670918367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (11979796703067989126212378210000000000000)
      constant := (2527629266732154009015413840220883928571380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (28310267402542700833/100000000000000000000)
  directionHi := (14155133701271350417/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree002.table
  base := (13383057769803807220189779222141151147959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (2276816476669012920264201320000000000000)
      constant := (933507907132018758054923426855880580357130) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree002.table
  base := (26266011169136938300293783374789195153061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (4152218696595865662923863420000000000000)
      constant := (1831946323676447801364532225518243660714270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28310267402542700833/100000000000000000000)
  centralHi := (14155133701271350417/50000000000000000000)
  directionLo := (40036764115084821401/100000000000000000000)
  directionHi := (20018382057542410701/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree003.table
  base := (9756750660170630442531736955105595120353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-1536618962381508766978921270000000000000)
      constant := (679565954080757365198057465870891658424710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree003.table
  base := (9481018212821624487804345458591062270681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-3675359309876257800364651370000000000000)
      constant := (1320601671931596460398576434664498717895340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40036764115084821401/100000000000000000000)
  centralHi := (20018382057542410701/50000000000000000000)
  directionLo := (4903482151706494713/10000000000000000000)
  directionHi := (49034821517064947131/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree004.table
  base := (14092165079107333859282389993223009757281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-5350054401432030454222043860000000000000)
      constant := (490753805594087471047168231186805341504835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree004.table
  base := (13550484874191513531840728296784688640379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-11502937316348381263653166160000000000000)
      constant := (943907183217199125490164390106928204826530) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4903482151706494713/10000000000000000000)
  centralHi := (49034821517064947131/100000000000000000000)
  directionLo := (56620534805085401667/100000000000000000000)
  directionHi := (14155133701271350417/25000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree005.table
  base := (5008190858079254761613010783562988804843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-9163489840482552141465166450000000000000)
      constant := (350071083180852741208895743386909216339010) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree005.table
  base := (9516304780432468526294560127923697867409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-19330515322820504726941680950000000000000)
      constant := (665809236128807355650622614848408850718630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56620534805085401667/100000000000000000000)
  centralHi := (14155133701271350417/25000000000000000000)
  directionLo := (63303682373281881659/100000000000000000000)
  directionHi := (3165184118664094083/5000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree006.table
  base := (6950573425288208818402802524855016696023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-12976925279533073828708289040000000000000)
      constant := (245772563623822908636035188723925584360805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree006.table
  base := (650604033810462350208933306564711037299/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-27158093329292628190230195740000000000000)
      constant := (461565924228116818898291374742297726109300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63303682373281881659/100000000000000000000)
  centralHi := (3165184118664094083/5000000000000000000)
  directionLo := (69345709617977311793/100000000000000000000)
  directionHi := (34672854808988655897/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree007.table
  base := (924796150550457226081991571253237318817/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-16790360718583595515951411630000000000000)
      constant := (168381666041952876824489441842816530792975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree007.table
  base := (2119218887130559234269658038468105917583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-34985671335764751653518710530000000000000)
      constant := (311489483408847315885169497477284828461620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69345709617977311793/100000000000000000000)
  centralHi := (34672854808988655897/50000000000000000000)
  directionLo := (74901927096866492353/100000000000000000000)
  directionHi := (37450963548433246177/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree008.table
  base := (2838600876038829368626943942736818084963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-20603796157634117203194534220000000000000)
      constant := (110968291647325722602539476091788632973705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree008.table
  base := (313710557539307536144469474152651595561/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-42813249342236875116807225320000000000000)
      constant := (201313029669874327057044247253484893514160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74901927096866492353/100000000000000000000)
  centralHi := (37450963548433246177/50000000000000000000)
  directionLo := (40036764115084821401/50000000000000000000)
  directionHi := (80073528230169642803/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree009.table
  base := (90882193315070330355420112368789636677/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-24417231596684638890437656810000000000000)
      constant := (68621285866206482312338926948022196539120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree009.table
  base := (73535028775912477404057883632179117797/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-50640827348708998580095740110000000000000)
      constant := (121011167501694399630754798723790611932640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40036764115084821401/50000000000000000000)
  centralHi := (80073528230169642803/100000000000000000000)
  directionLo := (84930802207628102501/100000000000000000000)
  directionHi := (42465401103814051251/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree010.table
  base := (367398232263594309782992171370140505207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-28230667035735160577680779400000000000000)
      constant := (37731267696249870940667320647954917682245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree010.table
  base := (134792445932698662722579646434244838437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-58468405355181122043384254900000000000000)
      constant := (63284763900288883844203829325397138690590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84930802207628102501/100000000000000000000)
  centralHi := (42465401103814051251/50000000000000000000)
  directionLo := (22381231540113468489/25000000000000000000)
  directionHi := (89524926160453873957/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree011.table
  base := (-1942952150441198325013274525211731301/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-32044102474785682264923901990000000000000)
      constant := (15643625589784476063354290235602887543040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree011.table
  base := (-345801038724442922031195662458744115699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-66295983361653245506672769690000000000000)
      constant := (22815044263422755278013804041525823802140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22381231540113468489/25000000000000000000)
  centralHi := (89524926160453873957/100000000000000000000)
  directionLo := (46947267344431747691/50000000000000000000)
  directionHi := (93894534688863495383/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree012.table
  base := (-598053517814113594208151902364325299711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-35857537913836203952167024580000000000000)
      constant := (403953234919774590364936850497229020230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree012.table
  base := (-169756902551413400092306354727366927559/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-74123561368125368969961284480000000000000)
      constant := (-4278239156584718387207761459325479433040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46947267344431747691/50000000000000000000)
  centralHi := (93894534688863495383/100000000000000000000)
  directionLo := (4903482151706494713/5000000000000000000)
  directionHi := (98069643034129894261/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree013.table
  base := (-884950244776595043930412319354500949261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-39670973352886725639410147170000000000000)
      constant := (-9428519694827243588479247601315066448270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree013.table
  base := (-952533343561947813441104748190530339421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-81951139374597492433249799270000000000000)
      constant := (-20830065651586652521823609464924247518940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4903482151706494713/5000000000000000000)
  centralHi := (98069643034129894261/100000000000000000000)
  directionLo := (102074120741964434193/100000000000000000000)
  directionHi := (51037060370982217097/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree014.table
  base := (-1124585564441971226220939224238871720733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-43484408791937247326653269760000000000000)
      constant := (-14917618780320322874850381502721020451310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree014.table
  base := (-2362280223954568876572520184157507124809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-89778717381069615896538314060000000000000)
      constant := (-28915497467337289911353441824025498736630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102074120741964434193/100000000000000000000)
  centralHi := (51037060370982217097/50000000000000000000)
  directionLo := (52963660574134709667/50000000000000000000)
  directionHi := (21185464229653883867/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree015.table
  base := (-664101345045123786439113424184876761381/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-47297844230987769013896392350000000000000)
      constant := (-16850368951159843494643061048382746593340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree015.table
  base := (-550288315082219165085225301924281901519/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-97606295387541739359826828850000000000000)
      constant := (-30056736719380451848969311129748665531650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52963660574134709667/50000000000000000000)
  centralHi := (21185464229653883867/20000000000000000000)
  directionLo := (54822597088363292933/50000000000000000000)
  directionHi := (109645194176726585867/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree016.table
  base := (-752069398698714585673187372266513494009/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-51111279670038290701139514940000000000000)
      constant := (-15810372504666161568944254933311889161260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree016.table
  base := (-123541809159228310432229608426985109357/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-105433873394013862823115343640000000000000)
      constant := (-25373397531822328450061039035223941374750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54822597088363292933/50000000000000000000)
  centralHi := (109645194176726585867/100000000000000000000)
  directionLo := (22648213922034160667/20000000000000000000)
  directionHi := (14155133701271350417/12500000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree017.table
  base := (-3317186598728923242951704910516864952599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-54924715109088812388382637530000000000000)
      constant := (-12231588350905469087286831134590273340965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree017.table
  base := (-846348225179817956493194930872968285597/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-113261451400485986286403858430000000000000)
      constant := (-15691600028573619742927916072681119967160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22648213922034160667/20000000000000000000)
  centralHi := (14155133701271350417/12500000000000000000)
  directionLo := (116726222790164084439/100000000000000000000)
  directionHi := (2918155569754102111/2500000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree018.table
  base := (-3592382241032562540650811611520549808251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-58738150548139334075625760120000000000000)
      constant := (-6437761206623310343782997417219243288785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree018.table
  base := (-3650725440097880316092211927029593228201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-121089029406958109749692373220000000000000)
      constant := (-1623203672610786389117623769071525974070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116726222790164084439/100000000000000000000)
  centralHi := (2918155569754102111/2500000000000000000)
  directionLo := (30027573086313616051/25000000000000000000)
  directionHi := (24022058469050892841/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree019.table
  base := (-3840791726760763310656152286535765933283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-62551585987189855762868882710000000000000)
      constant := (1328656751255767041254351912748192335095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree019.table
  base := (-778209073638880671239579968154085391301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-128916607413430233212980888010000000000000)
      constant := (16376615060615262858999426511820113044650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30027573086313616051/25000000000000000000)
  centralHi := (24022058469050892841/20000000000000000000)
  directionLo := (123401594672297347017/100000000000000000000)
  directionHi := (61700797336148673509/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree020.table
  base := (-813525218985276026741609758804184729413/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-66365021426240377450112005300000000000000)
      constant := (10885279157281852741913951809267672352725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree020.table
  base := (-4111215017577333116276725466675242736789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-136744185419902356676269402800000000000000)
      constant := (37967492891310076102341494632733008424770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123401594672297347017/100000000000000000000)
  centralHi := (61700797336148673509/50000000000000000000)
  directionLo := (126607364746563763319/100000000000000000000)
  directionHi := (3165184118664094083/2500000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree021.table
  base := (-855365131952031888190758415416009347381/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-70178456865290899137355127890000000000000)
      constant := (22094195013378821668040619263698364208325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree021.table
  base := (-4314891865658133405218856408483737629037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-144571763426374480139557917590000000000000)
      constant := (62893406400671186718596848331888365967410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126607364746563763319/100000000000000000000)
  centralHi := (3165184118664094083/2500000000000000000)
  directionLo := (64866971658296390409/50000000000000000000)
  directionHi := (129733943316592780819/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree022.table
  base := (-4471387466493466045606783631553271537353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-73991892304341420824598250480000000000000)
      constant := (34850507736448905357165301921635496192645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree022.table
  base := (-2252422854824589644905720658335508867923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-152399341432846603602846432380000000000000)
      constant := (90960469783832340032665082076028758490780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64866971658296390409/50000000000000000000)
  centralHi := (129733943316592780819/100000000000000000000)
  directionLo := (132786924389701791537/100000000000000000000)
  directionHi := (66393462194850895769/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree023.table
  base := (-37228850192977992964028968304730734013/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-77805327743391942511841373070000000000000)
      constant := (49073900761633882760007084460303038693125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree023.table
  base := (-187327602060532453315775915560113038039/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-160226919439318727066134947170000000000000)
      constant := (122020737903394696645751957021552183431750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132786924389701791537/100000000000000000000)
  centralHi := (66393462194850895769/50000000000000000000)
  directionLo := (16971409105315848607/12500000000000000000)
  directionHi := (135771272842526788857/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree024.table
  base := (-2412626066905220945280686701284731005023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-81618763182442464199084495660000000000000)
      constant := (64702422298196091004468548174068829648390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree024.table
  base := (-606443895252091714362080707136431443093/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-168054497445790850529423461960000000000000)
      constant := (155960371805723963927833105955598391867920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16971409105315848607/12500000000000000000)
  centralHi := (135771272842526788857/100000000000000000000)
  directionLo := (69345709617977311793/50000000000000000000)
  directionHi := (138691419235954623587/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree025.table
  base := (-155865670398259534061662637322984073851/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-85432198621492985886327618250000000000000)
      constant := (81687898094616404393788964635757837286880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree025.table
  base := (-5011191843589450486919082949739699790681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-175882075452262973992711976750000000000000)
      constant := (192690975320719858301845645861971014652330) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69345709617977311793/50000000000000000000)
  centralHi := (138691419235954623587/100000000000000000000)
  directionLo := (17693917126589188021/12500000000000000000)
  directionHi := (141551337012713504169/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree026.table
  base := (-321377119484629249188245219872907559769/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-89245634060543507573570740840000000000000)
      constant := (99992539321836798538420001185171766529360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree026.table
  base := (-5163102237576047264005782551235726683929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-183709653458735097456000491540000000000000)
      constant := (232143238554261386714704481840499132124970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17693917126589188021/12500000000000000000)
  centralHi := (141551337012713504169/100000000000000000000)
  directionLo := (144354605920594954417/100000000000000000000)
  directionHi := (72177302960297477209/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree027.table
  base := (-211564171847475338486936277716665605303/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-93059069499594029260813863430000000000000)
      constant := (119586428492706922621005991891417595359875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree027.table
  base := (-2654033316864924031161428008546210260563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-191537231465207220919289006330000000000000)
      constant := (274262261223615868034781805005280563521180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144354605920594954417/100000000000000000000)
  centralHi := (72177302960297477209/50000000000000000000)
  directionLo := (14710446455119484139/10000000000000000000)
  directionHi := (147104464551194841391/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree028.table
  base := (-1357398969484844316153026093585464279537/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-96872504938644550948056986020000000000000)
      constant := (140445651090844875421141197074035000864820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree028.table
  base := (-272335639209449836454806336867089444853/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-199364809471679344382577521120000000000000)
      constant := (319004100679113232956269978054074777205800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14710446455119484139/10000000000000000000)
  centralHi := (147104464551194841391/100000000000000000000)
  directionLo := (74901927096866492353/50000000000000000000)
  directionHi := (149803854193732984707/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree029.table
  base := (-5564060214143644946752911101390215210313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-100685940377695072635300108610000000000000)
      constant := (162550902616627312603954281612842467639045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree029.table
  base := (-5579548443969142671400365826343825392909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-207192387478151467845866035910000000000000)
      constant := (366333214069658022983935022981682222496370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74901927096866492353/50000000000000000000)
  centralHi := (149803854193732984707/100000000000000000000)
  directionLo := (4764232990523128123/3125000000000000000)
  directionHi := (152455455696740099937/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree030.table
  base := (-5692946930548442200810757657665655413053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-104499375816745594322543231200000000000000)
      constant := (185886446168847784941922676831702060543145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree030.table
  base := (-285349428460919027284018093392690237173/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-215019965484623591309154550700000000000000)
      constant := (416220554464883612166641738925233667957800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4764232990523128123/3125000000000000000)
  centralHi := (152455455696740099937/100000000000000000000)
  directionLo := (15506172065375824157/10000000000000000000)
  directionHi := (155061720653758241571/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree031.table
  base := (-1163325221540633479627444800157803699883/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-108312811255796116009786353790000000000000)
      constant := (210439328928277349437741084213884352520475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree031.table
  base := (-2914687834173231715848208433018687094223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-222847543491095714772443065490000000000000)
      constant := (468642146276107284921168985593133806808780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15506172065375824157/10000000000000000000)
  centralHi := (155061720653758241571/100000000000000000000)
  directionLo := (3152497958921314009/2000000000000000000)
  directionHi := (157624897946065700451/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree032.table
  base := (-2967702596200034822809312855048831051747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-112126246694846637697029476380000000000000)
      constant := (236198790257187287350388458482581826377710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree032.table
  base := (-2973497561013092969679934774410876802287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-230675121497567838235731580280000000000000)
      constant := (523578012856233418553723052030477247679820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3152497958921314009/2000000000000000000)
  centralHi := (157624897946065700451/100000000000000000000)
  directionLo := (32029411292067857121/20000000000000000000)
  directionHi := (80073528230169642803/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree033.table
  base := (-120990836945021213290118295876788650117/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-115939682133897159384272598970000000000000)
      constant := (263155811964160688436081479349119862295250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree033.table
  base := (-6060086795230980473505220817108217491997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-238502699504039961699020095070000000000000)
      constant := (581011363657121744725888875174174775560210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32029411292067857121/20000000000000000000)
  centralHi := (80073528230169642803/50000000000000000000)
  directionLo := (8131505231707498993/5000000000000000000)
  directionHi := (162630104634149979861/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree034.table
  base := (-769906722233725665574823221711295355679/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-119753117572947681071515721560000000000000)
      constant := (291302774352719282251837838554837300409880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree034.table
  base := (-308442695333317260671536244223933080041/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-246330277510512085162308609860000000000000)
      constant := (640927973369387390886788660073493687942600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8131505231707498993/5000000000000000000)
  centralHi := (162630104634149979861/100000000000000000000)
  directionLo := (10317237959652094013/6250000000000000000)
  directionHi := (165075807354433504209/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree035.table
  base := (-6264726303391595059996898848608354740079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-123566553011998202758758844150000000000000)
      constant := (320633191253127868604148429136207584097235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree035.table
  base := (-3136734930519141067102595710733816118267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-254157855516984208625597124650000000000000)
      constant := (703315703663610218781605729791015743442620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10317237959652094013/6250000000000000000)
  centralHi := (165075807354433504209/100000000000000000000)
  directionLo := (167485800634326951999/100000000000000000000)
  directionHi := (20935725079290869/12500000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree036.table
  base := (-3183059117642541132125095213069309294649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-127379988451048724446001966740000000000000)
      constant := (351141504263983613718786476829148349374570) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree036.table
  base := (-1274816712134317501172091711991289849521/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-261985433523456332088885639440000000000000)
      constant := (768164131377054489508111415095048552667650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167485800634326951999/100000000000000000000)
  centralHi := (20935725079290869/12500000000000000)
  directionLo := (84930802207628102501/50000000000000000000)
  directionHi := (169861604415256205003/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree037.table
  base := (-3231783241025451361068986456576651967613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-131193423890099246133245089330000000000000)
      constant := (382822921587764265128469047393134362267090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree037.table
  base := (-3235411787773109139334770606793844122759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-269813011529928455552174154230000000000000)
      constant := (835464256611123216547194672030611822813740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84930802207628102501/50000000000000000000)
  centralHi := (169861604415256205003/100000000000000000000)
  directionLo := (5381394805590932703/3125000000000000000)
  directionHi := (172204633778909846497/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree038.table
  base := (-1311437937833044597319856223687024154379/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-135006859329149767820488211920000000000000)
      constant := (415673290632803993480329922520770772983675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree038.table
  base := (-328190072536530409872633077621195313141/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-277640589536400579015462669020000000000000)
      constant := (905208271211026037761439948693326561602600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5381394805590932703/3125000000000000000)
  centralHi := (172204633778909846497/100000000000000000000)
  directionLo := (34903241760806075567/20000000000000000000)
  directionHi := (43629052201007594459/25000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree039.table
  base := (-6647091144049380662823022385605056258909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-138820294768200289507731334510000000000000)
      constant := (449688996339355982592757345185323030938185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree039.table
  base := (-6653114357215247508329910567353325841903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-285468167542872702478751183810000000000000)
      constant := (977389373207428635922440875721017191066790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34903241760806075567/20000000000000000000)
  centralHi := (43629052201007594459/25000000000000000000)
  directionLo := (44199390815750646639/25000000000000000000)
  directionHi := (176797563263002586557/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree040.table
  base := (-841670139659221544414888593615387941307/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-142633730207250811194974457100000000000000)
      constant := (484866879237456351307904394187691376434040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree040.table
  base := (-421177952429009524248593552340901611017/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-293295745549344825942039698600000000000000)
      constant := (1052001616529849878662862852578190195660960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44199390815750646639/25000000000000000000)
  centralHi := (176797563263002586557/100000000000000000000)
  directionLo := (179049852320907747913/100000000000000000000)
  directionHi := (89524926160453873957/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree041.table
  base := (-1363215753606239128354792262922823131423/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-146447165646301332882217579690000000000000)
      constant := (521204168755357184406746330810005952000975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree041.table
  base := (-1705268642305883184393490919057111338977/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-301123323555816949405328213390000000000000)
      constant := (1129039788030055072900207847319758825086440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179049852320907747913/100000000000000000000)
  centralHi := (89524926160453873957/50000000000000000000)
  directionLo := (36254831874685253039/20000000000000000000)
  directionHi := (45318539843356566299/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree042.table
  base := (-1379062742007942142274686705606185745833/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-150260601085351854569460702280000000000000)
      constant := (558698428412926375267778284464917494479225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree042.table
  base := (-862482725419084589559934999543749633159/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-308950901562289072868616728180000000000000)
      constant := (1208499305853894047479264036058500205430960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36254831874685253039/20000000000000000000)
  centralHi := (45318539843356566299/25000000000000000000)
  directionLo := (183471502138467862177/100000000000000000000)
  directionHi := (91735751069233931089/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree043.table
  base := (-871390913806754668155835255488316282063/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-154074036524402376256703824870000000000000)
      constant := (597347510359748731551479772236771441022360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree043.table
  base := (-697526658884031076867234494495423113563/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-316778479568761196331905242970000000000000)
      constant := (1290376134670155951321550478494953820505900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183471502138467862177/100000000000000000000)
  centralHi := (91735751069233931089/50000000000000000000)
  directionLo := (7425713523948985649/4000000000000000000)
  directionHi := (92821419049362320613/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree044.table
  base := (-1760893444219397645213108355523036497829/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-157887471963452897943946947460000000000000)
      constant := (637149517329704726946795364530774890303940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree044.table
  base := (-880917473085717851637060292880463297451/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-324606057575233319795193757760000000000000)
      constant := (1374666714348889230100992507158940553427440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7425713523948985649/4000000000000000000)
  centralHi := (92821419049362320613/50000000000000000000)
  directionLo := (46947267344431747691/25000000000000000000)
  directionHi := (37557813875545398153/20000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree045.table
  base := (-7112701074562672425925861835082945281913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-161700907402503419631190070050000000000000)
      constant := (678102770538963791182993965309596915133045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree045.table
  base := (-1423225265053247948004879011156573458311/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-332433635581705443258482272550000000000000)
      constant := (1461367899483685201498514921488949289591150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46947267344431747691/25000000000000000000)
  centralHi := (37557813875545398153/20000000000000000000)
  directionLo := (189911047119845644979/100000000000000000000)
  directionHi := (9495552355992282249/5000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree046.table
  base := (-89731896327283529658523952466557163511/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-165514342841553941318433192640000000000000)
      constant := (720205782393956942032552362567639942169200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree046.table
  base := (-3590832979048376285406680567939611219991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-340261213588177566721770787340000000000000)
      constant := (1550476907748497294019108257795454429201260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (189911047119845644979/100000000000000000000)
  centralHi := (9495552355992282249/5000000000000000000)
  directionLo := (12000598464659954051/6250000000000000000)
  directionHi := (192009575434559264817/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree047.table
  base := (-452572711205695543327401377505644001761/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-169327778280604463005676315230000000000000)
      constant := (763457233130311389971346662710339359013840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree047.table
  base := (-1810998469431909892009664278731003593911/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-348088791594649690185059302130000000000000)
      constant := (1641991275524800429282503158867068993704920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12000598464659954051/6250000000000000000)
  centralHi := (192009575434559264817/100000000000000000000)
  directionLo := (48521353739206396271/25000000000000000000)
  directionHi := (38817082991365117017/20000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree048.table
  base := (-7300569581111990195339479061284224284129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-173141213719654984692919437820000000000000)
      constant := (807855950695187876728333376311052150055485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree048.table
  base := (-1825785318336858868858631885023880035897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-355916369601121813648347816920000000000000)
      constant := (1735908819569397175227302506401313589948840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48521353739206396271/25000000000000000000)
  centralHi := (38817082991365117017/20000000000000000000)
  directionLo := (4903482151706494713/2500000000000000000)
  directionHi := (196139286068259788521/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree049.table
  base := (-7356800076167750432751276484688576566973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-176954649158705506380162560410000000000000)
      constant := (853400893330299477921695880537399820155945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree049.table
  base := (-3679567902021838168629008514733897638239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-363743947607593937111636331710000000000000)
      constant := (1832227603746160008755513177133004330646540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4903482151706494713/2500000000000000000)
  centralHi := (196139286068259788521/100000000000000000000)
  directionLo := (49542967954449726459/25000000000000000000)
  directionHi := (198171871817798905837/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree050.table
  base := (-1852470334775515184782710832800393531309/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-180768084597756028067405683000000000000000)
      constant := (900091134423118396873438159657944905616740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree050.table
  base := (-7412002012921036153479547561374195367937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-371571525614066060574924846500000000000000)
      constant := (1930945910037761749869205632578806324244410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49542967954449726459/25000000000000000000)
  centralHi := (198171871817798905837/100000000000000000000)
  directionLo := (100091910287712053503/50000000000000000000)
  directionHi := (200183820575424107007/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree051.table
  base := (-7459836932640983690749998652547480333213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-184581520036806549754648805590000000000000)
      constant := (947925849278232443414046546862338188337545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree051.table
  base := (-7461761689160358117084391993415068195593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-379399103620538184038213361290000000000000)
      constant := (2032062213201543375059410772706695226308490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100091910287712053503/50000000000000000000)
  centralHi := (200183820575424107007/100000000000000000000)
  directionLo := (10108787422408419591/5000000000000000000)
  directionHi := (202175748448168391821/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree052.table
  base := (-3753343919387035251293245024492718109563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-188394955475857071441891928180000000000000)
      constant := (996904303526007325019299876141509732330590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree052.table
  base := (-3754217092730999634070895512167679827363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-387226681627010307501501876080000000000000)
      constant := (2135575158548479891521281748604524824169180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10108787422408419591/5000000000000000000)
  centralHi := (202175748448168391821/100000000000000000000)
  directionLo := (102074120741964434193/50000000000000000000)
  directionHi := (204148241483928868387/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree053.table
  base := (-7550452749786817957797545998744372262809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-192208390914907593129135050770000000000000)
      constant := (1047025842936450654278695150757446970801685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree053.table
  base := (-3776018348516524634687254311431967827177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-395054259633482430964790390870000000000000)
      constant := (2241483542414075022864225082461274504195220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102074120741964434193/50000000000000000000)
  centralHi := (204148241483928868387/100000000000000000000)
  directionLo := (4122037153708540147/2000000000000000000)
  directionHi := (206101857685427007351/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree054.table
  base := (-948893540579723603449434601803824855047/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-196021826353958114816378173360000000000000)
      constant := (1098289884446012734199801509768929040586840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree054.table
  base := (-3796292253631396419936862867047440795587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-402881837639954554428078905660000000000000)
      constant := (2349786294961078838751858108120358288617820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4122037153708540147/2000000000000000000)
  centralHi := (206101857685427007351/100000000000000000000)
  directionLo := (208037128853931935379/100000000000000000000)
  directionHi := (10401856442696596769/5000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree055.table
  base := (-7628789415271598434052337206964454702099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-199835261793008636503621295950000000000000)
      constant := (1150695908236632028510097038293744085426535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree055.table
  base := (-3815045602209811988863874613084859146679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-410709415646426677891367420450000000000000)
      constant := (2460482465010703759317999344811869719464940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208037128853931935379/100000000000000000000)
  centralHi := (10401856442696596769/5000000000000000000)
  directionLo := (104977281140005420767/50000000000000000000)
  directionHi := (41990912456002168307/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree056.table
  base := (-478961829171070371614535937823949953631/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-203648697232059158190864418540000000000000)
      constant := (1204243450731597766306326062322588025966640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree056.table
  base := (-7664568873047636153852552923292587390763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-418536993652898801354655935240000000000000)
      constant := (2573571206644863241598530624841518882646590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104977281140005420767/50000000000000000000)
  centralHi := (41990912456002168307/20000000000000000000)
  directionLo := (211854642296538838669/100000000000000000000)
  directionHi := (21185464229653883867/10000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree057.table
  base := (-1538991938879396970147905939602769246267/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-207462132671109679878107541130000000000000)
      constant := (1258932098393218475515371699743015381903275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree057.table
  base := (-7696028263206723050482394164685300300513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-426364571659370924817944450030000000000000)
      constant := (2689051767359364727837053934463778978964090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211854642296538838669/100000000000000000000)
  centralHi := (21185464229653883867/10000000000000000000)
  directionLo := (5343445792685997141/2500000000000000000)
  directionHi := (213737831707439885641/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree058.table
  base := (-7723511241038254079861332108781183323429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-211275568110160201565350663720000000000000)
      constant := (1314761482223946393549149371738658583679985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree058.table
  base := (-1931119735064908198671547362223285770071/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-434192149665843048281232964820000000000000)
      constant := (2806923477578815849138745118780479984380120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5343445792685997141/2500000000000000000)
  centralHi := (213737831707439885641/100000000000000000000)
  directionLo := (107802286552050192101/50000000000000000000)
  directionHi := (215604573104100384203/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree059.table
  base := (-1937263329075561883329004312579220310763/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-215089003549210723252593786310000000000000)
      constant := (1371731272886335533903527852860409156493180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree059.table
  base := (-3874964708771513696275532732407616042949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-442019727672315171744521479610000000000000)
      constant := (2927185741369650265077505309568683753987140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107802286552050192101/50000000000000000000)
  centralHi := (215604573104100384203/100000000000000000000)
  directionLo := (217455290080064133219/100000000000000000000)
  directionHi := (10872764504003206661/5000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree060.table
  base := (-1942898580131234291656575632994453198801/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-218902438988261244939836908900000000000000)
      constant := (1429841176368626878135212033780776552167860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree060.table
  base := (-971548409244008773786055647826952062149/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-449847305678787295207809994400000000000000)
      constant := (3049838028209206541418534898916906845196560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217455290080064133219/100000000000000000000)
  centralHi := (10872764504003206661/5000000000000000000)
  directionLo := (54822597088363292933/25000000000000000000)
  directionHi := (219290388353453171733/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree061.table
  base := (-7791141754806049812093169608232752099241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-222715874427311766627080031490000000000000)
      constant := (1489090930132329987113667556593353676526565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree061.table
  base := (-7791859258207851030558842097377834246497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-457674883685259418671098509190000000000000)
      constant := (3174879865687008389175597942169301602745210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54822597088363292933/25000000000000000000)
  centralHi := (219290388353453171733/100000000000000000000)
  directionLo := (221110256805539851699/100000000000000000000)
  directionHi := (2211102568055398517/1000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree062.table
  base := (-1561540463778700677587537479483462073823/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-226529309866362288314323154080000000000000)
      constant := (1549480299686267733701157009156394137080975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree062.table
  base := (-1561670276271035960278312322976039176499/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-465502461691731542134387023980000000000000)
      constant := (3302310833029919116186643060921386288225350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221110256805539851699/100000000000000000000)
  centralHi := (2211102568055398517/1000000000000000000)
  directionLo := (222915268443001127111/100000000000000000000)
  directionHi := (27864408555375140889/12500000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree063.table
  base := (-1564256399654554348916993041624443816521/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-230342745305412810001566276670000000000000)
      constant := (1611009075538448533132801565669222332108825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree063.table
  base := (-3910934499424020041302194161036617587803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-473330039698203665597675538770000000000000)
      constant := (3432130555356159871864425334086623537707580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222915268443001127111/100000000000000000000)
  centralHi := (27864408555375140889/12500000000000000000)
  directionLo := (224705781290599477059/100000000000000000000)
  directionHi := (11235289064529973853/5000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree064.table
  base := (-489492883855111260519371518681938566363/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-234156180744463331688809399260000000000000)
      constant := (1673677070483045000388978282082114402836720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree064.table
  base := (-3916208441707945802007845199663867809341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-481157617704675789060964053560000000000000)
      constant := (3564338698574668475121658989039058506692260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224705781290599477059/100000000000000000000)
  centralHi := (11235289064529973853/5000000000000000000)
  directionLo := (22648213922034160667/10000000000000000000)
  directionHi := (226482139220341606671/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree065.table
  base := (-3919759765063091404440813758974153818939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-237969616183513853376052521850000000000000)
      constant := (1737484117184859240227772058709309232674270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree065.table
  base := (-122499988902527561314395011734848531459/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-488985195711147912524252568350000000000000)
      constant := (3698934964856232856863637122471628579063680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22648213922034160667/10000000000000000000)
  centralHi := (226482139220341606671/100000000000000000000)
  directionLo := (228244672722553745189/100000000000000000000)
  directionHi := (22824467272255374519/10000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree066.table
  base := (-7844186438343518689891975503588976366047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-241783051622564375063295644440000000000000)
      constant := (1802430066028077386823464273208385827188355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree066.table
  base := (-3922310006009634867392076488366318976771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-496812773717620035987541083140000000000000)
      constant := (3835919088611500128659950182415715343252060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228244672722553745189/100000000000000000000)
  centralHi := (22824467272255374519/10000000000000000000)
  directionLo := (45998739924754087337/20000000000000000000)
  directionHi := (114996849811885218343/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree067.table
  base := (-980736336194339491907612945069282794199/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-245596487061614896750538767030000000000000)
      constant := (1868514783199966955838857889914100817624280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree067.table
  base := (-7846282434787515271536660341697010739969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-504640351724092159450829597930000000000000)
      constant := (3975290832918532854023333440302959248202170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45998739924754087337/20000000000000000000)
  centralHi := (114996849811885218343/50000000000000000000)
  directionLo := (11586476287792658033/5000000000000000000)
  directionHi := (231729525755853160661/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree068.table
  base := (-1961158926061309574190815389618711050759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-249409922500665418437781889620000000000000)
      constant := (1935738148983536715961833163389380452893740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree068.table
  base := (-7844989578468134752558847016418225588071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-512467929730564282914118112720000000000000)
      constant := (4117049986349216637681183804198724208835030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11586476287792658033/5000000000000000000)
  centralHi := (231729525755853160661/100000000000000000000)
  directionLo := (233452445580328168879/100000000000000000000)
  directionHi := (2918155569754102111/1250000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree069.table
  base := (-7840424543633826209700423809164183116327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-253223357939715940125025012210000000000000)
      constant := (2004100056236130751956841992720753590928555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree069.table
  base := (-980093017443182276956813880794305866657/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-520295507737036406377406627510000000000000)
      constant := (4261196360149648376987235410920938714672080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233452445580328168879/100000000000000000000)
  centralHi := (2918155569754102111/1250000000000000000)
  directionLo := (235162742771552902791/100000000000000000000)
  directionHi := (29395342846444112849/12500000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree070.table
  base := (-3916629974206308094804708374022200533609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-257036793378766461812268134800000000000000)
      constant := (2073600409033524285780088452668445962647370) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree070.table
  base := (-7833548526377581885815826459600268776273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-528123085743508529840695142300000000000000)
      constant := (4407729785734761336192036078502981185660890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235162742771552902791/100000000000000000000)
  centralHi := (29395342846444112849/12500000000000000000)
  directionLo := (236860690761981501221/100000000000000000000)
  directionHi := (118430345380990750611/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree071.table
  base := (-7823144373277048596254550983215490183521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-260850228817816983499511257390000000000000)
      constant := (2144239121461376904839821671948957843576765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree071.table
  base := (-7823404891001539891209288872337957159993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-535950663749980653303983657090000000000000)
      constant := (4556650112461963126323931113812092998800490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236860690761981501221/100000000000000000000)
  centralHi := (118430345380990750611/50000000000000000000)
  directionLo := (47709310650499447649/20000000000000000000)
  directionHi := (119273276626248619123/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree072.table
  base := (-3905040008853119721106446235989753999927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-264663664256867505186754379980000000000000)
      constant := (2216016116537919548695844342056717220005110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree072.table
  base := (-7810315157398768245228823595507054586641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-543778241756452776767272171880000000000000)
      constant := (4707957205652553226445345745082506178935130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47709310650499447649/20000000000000000000)
  centralHi := (119273276626248619123/50000000000000000000)
  directionLo := (30027573086313616051/12500000000000000000)
  directionHi := (240220584690508928409/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree073.table
  base := (-779406885340342125545554811759224571723/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-268477099695918026873997502570000000000000)
      constant := (2288931325253539078869167721377771399896950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree073.table
  base := (-974285130827082703897974249671849143009/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-551605819762924900230560686670000000000000)
      constant := (4861650944833214008724624536535514479914960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30027573086313616051/12500000000000000000)
  centralHi := (240220584690508928409/100000000000000000000)
  directionLo := (241883030718265650717/100000000000000000000)
  directionHi := (120941515359132825359/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree074.table
  base := (-1555022529752164132383937165767695738073/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-272290535134968548561240625160000000000000)
      constant := (2362984685714507563451990933104653245837225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree074.table
  base := (-155506081981948788152576179313855061139/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-559433397769397023693849201460000000000000)
      constant := (5017731222172990118062944866028507286013500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241883030718265650717/100000000000000000000)
  centralHi := (120941515359132825359/50000000000000000000)
  directionLo := (121767064296813155367/50000000000000000000)
  directionHi := (48706825718725262147/20000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree075.table
  base := (-1550642598134644991880366011917142784613/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-276103970574019070248483747750000000000000)
      constant := (2438176142379507447021435621352000012692725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree075.table
  base := (-242293302953939344881039280036073862787/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-567260975775869147157137716250000000000000)
      constant := (5176197941093934532146249541312944547357120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121767064296813155367/50000000000000000000)
  centralHi := (48706825718725262147/20000000000000000000)
  directionLo := (4903482151706494713/2000000000000000000)
  directionHi := (245174107585324735651/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree076.table
  base := (-3864185651994441713104123114129857219279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-279917406013069591935726870340000000000000)
      constant := (2514505645378850004836782496474909994650470) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree076.table
  base := (-3864263534736967660380080100128132182489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-575088553782341270620426231040000000000000)
      constant := (5337051015036048214702727007234061494451540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4903482151706494713/2000000000000000000)
  centralHi := (245174107585324735651/100000000000000000000)
  directionLo := (49360637868918938807/20000000000000000000)
  directionHi := (61700797336148673509/25000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree077.table
  base := (-7700588868854760309938227217269515872893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-283730841452120113622969992930000000000000)
      constant := (2591973149907391488232056307589066944448745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree077.table
  base := (-3850364666542106671836011013726068339531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-582916131788813394083714745830000000000000)
      constant := (5500290366359311009968402029680100432465660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49360637868918938807/20000000000000000000)
  centralHi := (61700797336148673509/25000000000000000000)
  directionLo := (248421588254860273447/100000000000000000000)
  directionHi := (31052698531857534181/12500000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree078.table
  base := (-3834933418092521568804199852930294621329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-287544276891170635310213115520000000000000)
      constant := (2670578615683135333761675120920879376506970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree078.table
  base := (-7669993481016839397199001485687664129423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-590743709795285517547003260620000000000000)
      constant := (5665915925367526677484363475644863510940390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248421588254860273447/100000000000000000000)
  centralHi := (31052698531857534181/12500000000000000000)
  directionLo := (125014755880526763121/50000000000000000000)
  directionHi := (250029511761053526243/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree079.table
  base := (-7636206241456808332644945047574825077833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-291357712330221156997456238110000000000000)
      constant := (2750322006464383866605722589096381122275845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree079.table
  base := (-7636320407847272261980629274829495606911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-598571287801757641010291775410000000000000)
      constant := (5833927629440413102605844196137685307516230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125014755880526763121/50000000000000000000)
  centralHi := (250029511761053526243/100000000000000000000)
  directionLo := (25162716067999152989/10000000000000000000)
  directionHi := (251627160679991529891/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree080.table
  base := (-7599608017014502108952240773077449971881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-295171147769271678684699360700000000000000)
      constant := (2831203289619081469277545498542289250984165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree080.table
  base := (-7599710918091020805081898482107680473471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-606398865808229764473580290200000000000000)
      constant := (6004325422261884664638294675052462366857030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25162716067999152989/10000000000000000000)
  centralHi := (251627160679991529891/100000000000000000000)
  directionLo := (253214729493127526639/100000000000000000000)
  directionHi := (3165184118664094083/1250000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree081.table
  base := (-7560073003045097039338787333770842524877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-298984583208322200371942483290000000000000)
      constant := (2913222435740684101728846333459520511629305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree081.table
  base := (-1890041434001742395523416814432827158247/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-614226443814701887936868804990000000000000)
      constant := (6177109253133819444690354841874558395690840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253214729493127526639/100000000000000000000)
  centralHi := (3165184118664094083/1250000000000000000)
  directionLo := (254792406622884307503/100000000000000000000)
  directionHi := (15924525413930269219/6250000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree082.table
  base := (-751760195736815934769875838488955756143/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-302798018647372722059185605880000000000000)
      constant := (2996379418305506946123329015914865485349950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree082.table
  base := (-7517685514315385492052893647807606499651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-622054021821174011400157319780000000000000)
      constant := (6352279076365798759829437633376467545024430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254792406622884307503/100000000000000000000)
  centralHi := (15924525413930269219/6250000000000000000)
  directionLo := (2002815427294385453/781250000000000000)
  directionHi := (51272074938736267597/20000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree083.table
  base := (-373609778208468336898483188206980927273/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-306611454086423243746428728470000000000000)
      constant := (3080674213367051282823180701588613350908900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree083.table
  base := (-3736135420975670719010042906938767966237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-629881599827646134863445834570000000000000)
      constant := (6529834850732367506841307478250322484726820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2002815427294385453/781250000000000000)
  centralHi := (51272074938736267597/20000000000000000000)
  directionLo := (25791881077867927159/10000000000000000000)
  directionHi := (257918810778679271591/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree084.table
  base := (-7423854441792037322199122868096831952683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-310424889525473765433671851060000000000000)
      constant := (3166106799283300977906734711600610881656095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree084.table
  base := (-7423922250960831576198559400132135959971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-637709177834118258326734349360000000000000)
      constant := (6709776538990306094791732281402750482802030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25791881077867927159/10000000000000000000)
  centralHi := (257918810778679271591/100000000000000000000)
  directionLo := (64866971658296390409/25000000000000000000)
  directionHi := (259467886633185561637/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree085.table
  base := (-460786196855548581810419252469292809837/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-314238324964524287120914973650000000000000)
      constant := (3252677156473414814073706013954696026491280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree085.table
  base := (-7372640222634896119065972227193924717517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-645536755840590381790022864150000000000000)
      constant := (6892104107449241708807275995390175269773810) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64866971658296390409/25000000000000000000)
  centralHi := (259467886633185561637/100000000000000000000)
  directionLo := (130503884457796031621/50000000000000000000)
  directionHi := (261007768915592063243/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree086.table
  base := (-457398137164016276283711738207889961111/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-318051760403574808808158096240000000000000)
      constant := (3340385267200629211044750709997581621777840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree086.table
  base := (-14636850385932905341284010489837763793/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-653364333847062505253311378940000000000000)
      constant := (7076817525589670116606560953722678267245000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130503884457796031621/50000000000000000000)
  centralHi := (261007768915592063243/100000000000000000000)
  directionLo := (52507723879329821253/20000000000000000000)
  directionHi := (131269309698324553133/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree087.table
  base := (-90765350452628328712048236595343165051/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-321865195842625330495401218830000000000000)
      constant := (3429231115378531881418234413686539137857200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree087.table
  base := (-1452255511501019169760903491863635470287/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-661191911853534628716599893730000000000000)
      constant := (7263916765723119694938137025979477585399550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52507723879329821253/20000000000000000000)
  centralHi := (131269309698324553133/50000000000000000000)
  directionLo := (264060595157819884383/100000000000000000000)
  directionHi := (8251893598681871387/3125000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree088.table
  base := (-1800288272961323968955418579022580517793/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-325678631281675852182644341420000000000000)
      constant := (3519214686398175292378802772552838727508980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree088.table
  base := (-1800299418919186155123631363287031912631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-669019489860006752179888408520000000000000)
      constant := (7453401802689776116116133051367631064463320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264060595157819884383/100000000000000000000)
  centralHi := (8251893598681871387/3125000000000000000)
  directionLo := (10622953951176143323/4000000000000000000)
  directionHi := (66393462194850895769/25000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree089.table
  base := (-3569072870561615553364579003760212246851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-329492066720726373869887464010000000000000)
      constant := (3610335966973773575689884445518285142720430) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree089.table
  base := (-7138185874627569489237346070365662263137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-676847067866478875643176923310000000000000)
      constant := (7645272613589407444893776850810153641580410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10622953951176143323/4000000000000000000)
  centralHi := (66393462194850895769/25000000000000000000)
  directionLo := (66769632129766239381/25000000000000000000)
  directionHi := (10683141140762598301/4000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree090.table
  base := (-1768051582442127403701207525260225609163/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-333305502159776895557130586600000000000000)
      constant := (3702594945004971414472331229113568414717180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree090.table
  base := (-7072242452645014864674340095085439063387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-684674645872950999106465438100000000000000)
      constant := (7839529177541892572596173169419019265562910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66769632129766239381/25000000000000000000)
  centralHi := (10683141140762598301/4000000000000000000)
  directionLo := (268574778481361621869/100000000000000000000)
  directionHi := (26857477848136162187/10000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree091.table
  base := (-7003335173149048871799087459900585594437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-337118937598827417244373709190000000000000)
      constant := (3795991609453891697214879233124979504194705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree091.table
  base := (-1400673536440570561271286784637476228751/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-692502223879423122569753952890000000000000)
      constant := (8036171475474067455054757159482633319937150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268574778481361621869/100000000000000000000)
  centralHi := (26857477848136162187/10000000000000000000)
  directionLo := (54012547755763544443/20000000000000000000)
  directionHi := (33757842347352215277/12500000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree092.table
  base := (-6931532559412596126013825782796478837469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-340932373037877938931616831780000000000000)
      constant := (3890525950235363270226962108098123240688585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree092.table
  base := (-6931561812671980484600703263953689386029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-700329801885895246033042467680000000000000)
      constant := (8235199489929969290347333521351241742977970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54012547755763544443/20000000000000000000)
  centralHi := (33757842347352215277/12500000000000000000)
  directionLo := (271542545685053577713/100000000000000000000)
  directionHi := (135771272842526788857/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree093.table
  base := (-6856798752287225944851970723737638856607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-344745808476928460618859954370000000000000)
      constant := (3986197958118903523649477456142682640018755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree093.table
  base := (-6856825072734031991903240490659853539657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-708157379892367369496330982470000000000000)
      constant := (8436613204901883691999175788895560252224010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271542545685053577713/100000000000000000000)
  centralHi := (135771272842526788857/50000000000000000000)
  directionLo := (68253582945111241069/25000000000000000000)
  directionHi := (273014331780444964277/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree094.table
  base := (-3389566996791145493750748422205622638481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-348559243915978982306103076960000000000000)
      constant := (4083007624641185114410846167599606415306330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree094.table
  base := (-6779157672530750612499793382935525871413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-715984957898839492959619497260000000000000)
      constant := (8640412605679888630113781617541513189001090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68253582945111241069/25000000000000000000)
  centralHi := (273014331780444964277/100000000000000000000)
  directionLo := (13723911304537634713/5000000000000000000)
  directionHi := (274478226090752694261/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree095.table
  base := (-837317313177774373906372686436024236829/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-352372679355029503993346199550000000000000)
      constant := (4180954942027853911705968035335413213687880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree095.table
  base := (-6698559805578402625371895191979645399983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-723812535905311616422908012050000000000000)
      constant := (8846597678717845465162443679705174822001190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13723911304537634713/5000000000000000000)
  centralHi := (274478226090752694261/100000000000000000000)
  directionLo := (137967177109566376113/50000000000000000000)
  directionHi := (275934354219132752227/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree096.table
  base := (-3307506246120923880063240522302641665627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-356186114794080025680589322140000000000000)
      constant := (4280039903123688072393931086062815083406110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree096.table
  base := (-3307515825236628468086816703328707109761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-731640113911783739886196526840000000000000)
      constant := (9055168411514015373749375851165981004633460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137967177109566376113/50000000000000000000)
  centralHi := (275934354219132752227/100000000000000000000)
  directionLo := (69345709617977311793/25000000000000000000)
  directionHi := (277382838471909247173/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree097.table
  base := (-3264278071284766858327269926336139585787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-359999550233130547367832444730000000000000)
      constant := (4380262501330197641686306267569970228994910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree097.table
  base := (-6528573372411260789318219565321278085963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-739467691918255863349485041630000000000000)
      constant := (9266124792504682048765653324239260533982590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69345709617977311793/25000000000000000000)
  centralHi := (277382838471909247173/100000000000000000000)
  directionLo := (55764759595693324779/20000000000000000000)
  directionHi := (34852974747308327987/12500000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree098.table
  base := (-6439169630620136909777378232838985027827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-363812985672181069055075567320000000000000)
      constant := (4481622730549861677870115868756635524026055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree098.table
  base := (-402449070283904379256715881589802162881/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-747295269924727986812773556420000000000000)
      constant := (9479466810969341578380150068302421577573280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55764759595693324779/20000000000000000000)
  centralHi := (34852974747308327987/12500000000000000000)
  directionLo := (280257348805593749809/100000000000000000000)
  directionHi := (28025734880559374981/10000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree099.table
  base := (-6346853117719179367209684344004302315129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-367626421111231590742318689910000000000000)
      constant := (4584120585136286909975345804061349418970485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree099.table
  base := (-1586716762294626831546273767557403055269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-755122847931200110276062071210000000000000)
      constant := (9695194456946180383837803020329677144524680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280257348805593749809/100000000000000000000)
  centralHi := (28025734880559374981/10000000000000000000)
  directionLo := (140841802033295243073/50000000000000000000)
  directionHi := (281683604066590486147/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree100.table
  base := (-312580337678795672913207425690064061753/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-371439856550282112429561812500000000000000)
      constant := (4687756059849649505076051912016955156772900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree100.table
  base := (-6251619278869289793564182774350726637563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-762950425937672233739350586000000000000000)
      constant := (9913307721156704259037699358295449135370590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140841802033295243073/50000000000000000000)
  centralHi := (281683604066590486147/100000000000000000000)
  directionLo := (283102674025427008337/100000000000000000000)
  directionHi := (141551337012713504169/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree101.table
  base := (-1538357669355433297477732606667724542771/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-375253291989332634116804935090000000000000)
      constant := (4792529149816850672928278603668018564012060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree101.table
  base := (-6153441937363464810205913945730540353113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-770778003944144357202639100790000000000000)
      constant := (10133806594938507890182555311244612175282090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283102674025427008337/100000000000000000000)
  centralHi := (141551337012713504169/50000000000000000000)
  directionLo := (71128666549056829599/25000000000000000000)
  directionHi := (284514666196227318397/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree102.table
  base := (-3026162509514203989035688905863228384377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-379066727428383155804048057680000000000000)
      constant := (4898439850495878483974778708495574013093610) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree102.table
  base := (-1210467028093077253361391876537664626709/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-778605581950616480665927615580000000000000)
      constant := (10356691070185286504923603923294817380651850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71128666549056829599/25000000000000000000)
  centralHi := (284514666196227318397/100000000000000000000)
  directionLo := (142959842719165482253/50000000000000000000)
  directionHi := (285919685438330964507/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree103.table
  base := (-1189657979923814428122239253928467568521/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-382880162867433677491291180270000000000000)
      constant := (5005488157643923237090252530476018175508825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree103.table
  base := (-2974149498400020145985679360913680170851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-786433159957088604129216130370000000000000)
      constant := (10581961139293291074258562419883834776080860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (142959842719165482253/50000000000000000000)
  centralHi := (285919685438330964507/100000000000000000000)
  directionLo := (287317834047170833861/100000000000000000000)
  directionHi := (143658917023585416931/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree104.table
  base := (-5841325432683503400800111487201288413199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-386693598306484199178534302860000000000000)
      constant := (5113674067288842711960259670571954905538035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree104.table
  base := (-5841333608496061728370914253072449097277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-794260737963560727592504645160000000000000)
      constant := (10809616795113517159200404640716928563190610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287317834047170833861/100000000000000000000)
  centralHi := (143658917023585416931/50000000000000000000)
  directionLo := (144354605920594954417/50000000000000000000)
  directionHi := (57741842368237981767/20000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree105.table
  base := (-5731431724707975577278227493465059316451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-390507033745534720865777425450000000000000)
      constant := (5222997575703617324932396487766222923924215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree105.table
  base := (-5731439071795857215787673664616485890743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-802088315970032851055793159950000000000000)
      constant := (11039658030908996294964387247620595987647990) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144354605920594954417/50000000000000000000)
  centralHi := (57741842368237981767/20000000000000000000)
  directionLo := (290093916245005978081/100000000000000000000)
  directionHi := (145046958122502989041/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree106.table
  base := (-175581527369651808905676587121654639201/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-394320469184585242553020548040000000000000)
      constant := (5333458679383474153483899254577746804094880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree106.table
  base := (-5618615477600850243489941773857883135991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-809915893976504974519081674740000000000000)
      constant := (11272084840316628837301728903376948180480630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290093916245005978081/100000000000000000000)
  centralHi := (145046958122502989041/50000000000000000000)
  directionLo := (291472042369020386207/100000000000000000000)
  directionHi := (9108501324031887069/3125000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree107.table
  base := (-1100571396083628237557334584983971622237/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-398133904623635764240263670630000000000000)
      constant := (5445057375025393517379097766601304966108525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree107.table
  base := (-5502862911958974395532866552342121358587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-817743471982977097982370189530000000000000)
      constant := (11506897217313059435328569249977801504898910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291472042369020386207/100000000000000000000)
  centralHi := (9108501324031887069/3125000000000000000)
  directionLo := (29284368308565490891/10000000000000000000)
  directionHi := (292843683085654908911/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree108.table
  base := (-107683522552163740607860911754075328719/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-401947340062686285927506793220000000000000)
      constant := (5557793659509742762553500714926368174741750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree108.table
  base := (-2692090728250375396161954622769026794877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-825571049989449221445658704320000000000000)
      constant := (11744095156184151610616386000240336248717220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29284368308565490891/10000000000000000000)
  centralHi := (292843683085654908911/100000000000000000000)
  directionLo := (14710446455119484139/5000000000000000000)
  directionHi := (294208929102389682781/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree109.table
  base := (-1315641600440551664801640409324163455069/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-405760775501736807614749915810000000000000)
      constant := (5671667529883809495382905349416117116290340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree109.table
  base := (-210502847553183336548062279425045380131/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-833398627995921344908947219110000000000000)
      constant := (11983678651497667084576485054911920584770750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14710446455119484139/5000000000000000000)
  centralHi := (294208929102389682781/100000000000000000000)
  directionLo := (147783934515882367167/50000000000000000000)
  directionHi := (59113573806352946867/20000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree110.table
  base := (-5138027882896274112416330157485723701681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-409574210940787329301993038400000000000000)
      constant := (5786678983347031124530692852137999670441165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree110.table
  base := (-5138032182871281783737323094363118438679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-841226206002393468372235733900000000000000)
      constant := (12225647698078799190523860481469581709292470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147783934515882367167/50000000000000000000)
  centralHi := (59113573806352946867/20000000000000000000)
  directionLo := (59384117891699596253/20000000000000000000)
  directionHi := (148460294729248990633/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree111.table
  base := (-1252640161764512635221723740306129830351/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-413387646379837850989236160990000000000000)
      constant := (5902828017237739509716604189638641823750860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree111.table
  base := (-2505282254593632853528710674581010788931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-849053784008865591835524248690000000000000)
      constant := (12470002290988248542134677315494408489549660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59384117891699596253/20000000000000000000)
  centralHi := (148460294729248990633/50000000000000000000)
  directionLo := (149133587501931782601/50000000000000000000)
  directionHi := (298267175003863565203/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree112.table
  base := (-2440082383333418972021755219158731042483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-417201081818888372676479283580000000000000)
      constant := (6020114629021259080960755458274888827026190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree112.table
  base := (-1220042058813853410357042417520167951901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-856881362015337715298812763480000000000000)
      constant := (12716742425502563647365293302582352973467720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149133587501931782601/50000000000000000000)
  centralHi := (298267175003863565203/100000000000000000000)
  directionLo := (74901927096866492353/25000000000000000000)
  directionHi := (299607708387465969413/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree113.table
  base := (-4746840310819082096424474449905802865553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-421014517257938894363722406170000000000000)
      constant := (6138538816279214236154306232906796899705645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree113.table
  base := (-4746843425722078003289650307589134612627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-864708940021809838762101278270000000000000)
      constant := (12965868097096499837064902685200510577116110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74901927096866492353/25000000000000000000)
  centralHi := (299607708387465969413/100000000000000000000)
  directionLo := (150471135243268765303/50000000000000000000)
  directionHi := (300942270486537530607/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree114.table
  base := (-576323418195375003677507865977219585691/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-424827952696989416050965528760000000000000)
      constant := (6258100576699917379198596855920378516006520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree114.table
  base := (-4610590142628401128893362942721715751637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-872536518028281962225389793060000000000000)
      constant := (13217379301427177147695900485676479897385410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150471135243268765303/50000000000000000000)
  centralHi := (300942270486537530607/100000000000000000000)
  directionLo := (75567735098219907331/25000000000000000000)
  directionHi := (12090837615715185173/4000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree115.table
  base := (-4471405934145611160494571911124470515009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-428641388136039937738208651350000000000000)
      constant := (6378799908069722830482376965948143531974685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree115.table
  base := (-89428168912274386607323453926110356387/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-880364096034754085688678307850000000000000)
      constant := (13471276034319842037409406145552363752645500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75567735098219907331/25000000000000000000)
  centralHi := (12090837615715185173/4000000000000000000)
  directionLo := (151796897733780499781/50000000000000000000)
  directionHi := (303593795467560999563/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree116.table
  base := (-2164648068617548903284574801160018460847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-432454823575090459425451773940000000000000)
      constant := (6500636808265244208913406375902798707740710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree116.table
  base := (-2164649196049267337158534978064789359833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-888191674041226209151966822640000000000000)
      constant := (13727558291755059361542790337682929489623380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151796897733780499781/50000000000000000000)
  centralHi := (303593795467560999563/100000000000000000000)
  directionLo := (4764232990523128123/1562500000000000000)
  directionHi := (304910911393480199873/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree117.table
  base := (-4184258013121105723772232288013242515571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-436268259014140981112694896530000000000000)
      constant := (6623611275246343913027189815753036511955015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree117.table
  base := (-2092130018724630244123980874859086076697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-896019252047698332615255337430000000000000)
      constant := (13986226069857180187170919570141477949262420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4764232990523128123/1562500000000000000)
  centralHi := (304910911393480199873/100000000000000000000)
  directionLo := (306222362225893302579/100000000000000000000)
  directionHi := (15311118111294665129/5000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree118.table
  base := (-4036291617895314332275144571248909386503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-440081694453191502799938019120000000000000)
      constant := (6747723307049813163117730924392288171472395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree118.table
  base := (-2018146717563351680850434911689303574613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-903846830054170456078543852220000000000000)
      constant := (14247279364883948053025852320686497499554180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306222362225893302579/100000000000000000000)
  centralHi := (15311118111294665129/5000000000000000000)
  directionLo := (76882055110250563773/25000000000000000000)
  directionHi := (307528220441002255093/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree119.table
  base := (-3885397005614355712744149798253614706327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-443895129892242024487181141710000000000000)
      constant := (6872972901783669836361710484702623485278555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree119.table
  base := (-1942699318410014086660532279485623568681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-911674408060642579541832367010000000000000)
      constant := (14510718173217121417602419662587762700384660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76882055110250563773/25000000000000000000)
  centralHi := (307528220441002255093/100000000000000000000)
  directionLo := (9650892405709191249/3125000000000000000)
  directionHi := (308828556982694119969/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree120.table
  base := (-1865787114223469000986240044984089885691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-447708565331292546174424264300000000000000)
      constant := (6999360057622009147971365372451113708001630) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree120.table
  base := (-1865787846283880218527030469138995156227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-919501986067114703005120881800000000000000)
      constant := (14776542491354003494924435547120540678128220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9650892405709191249/3125000000000000000)
  centralHi := (308828556982694119969/100000000000000000000)
  directionLo := (15506172065375824157/5000000000000000000)
  directionHi := (310123441307516483141/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree121.table
  base := (-1787411668403414764654412747383762947159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-451522000770343067861667386890000000000000)
      constant := (7126884772800349206419491435944636593698870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree121.table
  base := (-893706162716802337583400928775662865561/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-927329564073586826468409396590000000000000)
      constant := (15044752315899782641171537841518564397642920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15506172065375824157/5000000000000000000)
  centralHi := (310123441307516483141/100000000000000000000)
  directionLo := (311412941427969709171/100000000000000000000)
  directionHi := (77853235356992427293/25000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree122.table
  base := (-683028875894636460307856627190285494781/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-455335436209393589548910509480000000000000)
      constant := (7255547045611419691468575275867700038413325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree122.table
  base := (-1707572779386771485808492395250429942819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-935157142080058949931697911380000000000000)
      constant := (15315347643560597092251716112707939808005340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311412941427969709171/100000000000000000000)
  centralHi := (77853235356992427293/25000000000000000000)
  directionLo := (312697123954192397059/100000000000000000000)
  directionHi := (15634856197709619853/5000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree123.table
  base := (-3252537403699514925286786551430488505159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-459148871648444111236153632070000000000000)
      constant := (7385346874401347451886814218393432902319435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree123.table
  base := (-1626269230994805922725628264273895373219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-942984720086531073394986426170000000000000)
      constant := (15588328471137247310046676695203404647749340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312697123954192397059/100000000000000000000)
  centralHi := (15634856197709619853/5000000000000000000)
  directionLo := (313976054134112330157/100000000000000000000)
  directionHi := (156988027067056165079/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree124.table
  base := (-3087002455312533669730968748043606583883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-462962307087494632923396754660000000000000)
      constant := (7516284257566197768252921108282473769564095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree124.table
  base := (-771750851236874314175484491890208410289/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-950812298093003196858274940960000000000000)
      constant := (15863694795519487604615833256322741645119080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313976054134112330157/100000000000000000000)
  centralHi := (156988027067056165079/50000000000000000000)
  directionLo := (315249795892131400901/100000000000000000000)
  directionHi := (157624897946065700451/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree125.table
  base := (-2918539578801844261515674283787033101687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-466775742526545154610639877250000000000000)
      constant := (7648359193548834440134361386004953841440955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree125.table
  base := (-583708086176530693314495465336770912171/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-958639876099475320321563455750000000000000)
      constant := (16141446613680836177674944420725880180740150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315249795892131400901/100000000000000000000)
  centralHi := (157624897946065700451/50000000000000000000)
  directionLo := (316518411866409408299/100000000000000000000)
  directionHi := (3165184118664094083/1000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree126.table
  base := (-686787204350373628162969846617910532903/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-470589177965595676297882999840000000000000)
      constant := (7781571680836065794110750883587492525393580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree126.table
  base := (-54942991638028365639496449566333128103/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-966467454105947443784851970540000000000000)
      constant := (16421583922673849382740173837344834051639500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316518411866409408299/100000000000000000000)
  centralHi := (3165184118664094083/1000000000000000000)
  directionLo := (79445490861202064501/25000000000000000000)
  directionHi := (63556392688961651601/20000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree127.table
  base := (-1286415106582093767553534654395132628109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-474402613404646197985126122430000000000000)
      constant := (7915921717956047221263227617185840716032370) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree127.table
  base := (-1286415449521290910851324807448040433299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-974295032112419567248140485330000000000000)
      constant := (16704106719625811911495964172709024339338140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79445490861202064501/25000000000000000000)
  centralHi := (63556392688961651601/20000000000000000000)
  directionLo := (159520255399777463349/50000000000000000000)
  directionHi := (319040510799554926699/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree128.table
  base := (-2395583807028915776963421464120814824121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-478216048843696719672369245020000000000000)
      constant := (8051409303475913985908915377331771481155765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree128.table
  base := (-1197792211166814099649618552546795057779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-982122610118891690711429000120000000000000)
      constant := (16989015001734799875994285941011448691910940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell003.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159520255399777463349/50000000000000000000)
  centralHi := (319040510799554926699/100000000000000000000)
  directionLo := (32029411292067857121/10000000000000000000)
  directionHi := (320294112920678571211/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 19
  qDenominator := 70
  table := BinomialMassData.Q19_70.Degree129.table
  base := (-1107704819441343125725983844963197314611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (459)
      previous := (171)
      next := (0)
      square := (7024749492987803108079436350000000000000)
      linear := (-482029484282747241359612367610000000000000)
      constant := (8188034435999620842584728049714076187977230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_70.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 39
  qDenominator := 140
  table := BinomialMassData.Q39_140.Degree129.table
  base := (-110770509542109900249684572440701038597/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 700000000000000000000000000000000000000000
      center := (909)
      previous := (351)
      next := (0)
      square := (14049498985975606216158872700000000000000)
      linear := (-989950188125363814174717514910000000000000)
      constant := (17276308766266078434919101687258768545964200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q39_140.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell003.Kernel129
