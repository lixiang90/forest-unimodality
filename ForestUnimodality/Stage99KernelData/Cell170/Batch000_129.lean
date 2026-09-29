import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell170.Parameters
import ForestUnimodality.BinomialMassData.Q653_1128.Batch000_049
import ForestUnimodality.BinomialMassData.Q653_1128.Batch050_099
import ForestUnimodality.BinomialMassData.Q653_1128.Batch100_149
import ForestUnimodality.BinomialMassData.Q7_12.Batch000_049
import ForestUnimodality.BinomialMassData.Q7_12.Batch050_099
import ForestUnimodality.BinomialMassData.Q7_12.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree000.table
  base := (33987783341290920138249021/2000000000000000000000000)
  polynomial :=
    { denominator := 11280000000000000000000000000000000000000000
      center := (26773)
      previous := (0)
      next := (19475)
      square := (722011991002850915810640228000000000000000)
      linear := (-2337002764116377282466174811200000000000000)
      constant := (191691098044880789579724478440000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree000.table
  base := (33987783341290920138249021/2000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-24861731533152949813469944800000000000000)
      constant := (2039267000477455208294941260000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree001.table
  base := (6348027259770286175768392686560976039859/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-447385847271624608833817665600200000000000000)
      constant := (16379131551241846573303468641926914374999907712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree001.table
  base := (50519786906074957469359611163476283496177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-101468619796373511199316651400000000000000)
      constant := (3688773686436181376313812228795292411724744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49300664859163467021/100000000000000000000)
  directionHi := (24650332429581733511/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree002.table
  base := (62576001193353319852092391631104695496799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-565254304802840020839904682821200000000000000)
      constant := (10470571806361400073935737753145589609374887352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree002.table
  base := (7746245131433452430362831129155831138143/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-128352044993288172958223468400000000000000)
      constant := (2349298654281936729677031458496879367785184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49300664859163467021/100000000000000000000)
  centralHi := (24650332429581733511/50000000000000000000)
  directionLo := (34860834438919814499/50000000000000000000)
  directionHi := (69721668877839628999/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree003.table
  base := (19921481556776862995126428256661681240213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-227707587444685144281997233347400000000000000)
      constant := (2405423583538370632833704968179488885262264816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree003.table
  base := (19653763274573718423171802032535025796237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-51745156730067611572376761800000000000000)
      constant := (538721345820087233368739117055840619109688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34860834438919814499/50000000000000000000)
  centralHi := (69721668877839628999/100000000000000000000)
  directionLo := (85391256382996653193/100000000000000000000)
  directionHi := (42695628191498326597/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree004.table
  base := (26177845160051260035419232152892493473437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-800991219865270844852078717263200000000000000)
      constant := (5472438388775600655788740155603045301963207976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree004.table
  base := (12870459740872083923532088002690062755471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-182118895387117496476037102400000000000000)
      constant := (1226161206327129112730165095793684518393912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85391256382996653193/100000000000000000000)
  centralHi := (42695628191498326597/50000000000000000000)
  directionLo := (49300664859163467021/50000000000000000000)
  directionHi := (98601329718326934043/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree005.table
  base := (8813284273378268245517399425720335013223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-918859677396486256858165734484200000000000000)
      constant := (4610186398072921761342260351752748186366183408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree005.table
  base := (539851208260935281330936576817505561943/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-209002320584032158234943919400000000000000)
      constant := (1035473718225855163619796494118766407358336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49300664859163467021/50000000000000000000)
  centralHi := (98601329718326934043/100000000000000000000)
  directionLo := (110239637961024607937/100000000000000000000)
  directionHi := (55119818980512303969/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree006.table
  base := (12009859852177038355587640109086773551139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-345576044975900556288084250568400000000000000)
      constant := (1427635233121844457035069399171494386587185224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree006.table
  base := (11722081638646921608987070518090688648369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-78628581926982273331283578800000000000000)
      constant := (321773028218999699811163512517088263780428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110239637961024607937/100000000000000000000)
  centralHi := (55119818980512303969/50000000000000000000)
  directionLo := (60380736442455994057/50000000000000000000)
  directionHi := (24152294576982397623/20000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree007.table
  base := (1014598489782934982553144840893835086259/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-1154596592458917080870339768926200000000000000)
      constant := (4298000113828012682144925413632573962394571456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree007.table
  base := (7872554724949919597005519794540477059417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-262769170977861481752757553400000000000000)
      constant := (972177133151892781678248796028457174139012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60380736442455994057/50000000000000000000)
  centralHi := (24152294576982397623/20000000000000000000)
  directionLo := (13043729868748773229/10000000000000000000)
  directionHi := (130437298687487732291/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree008.table
  base := (5268190424448194769436633689806906649299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-1272465049990132492876426786147200000000000000)
      constant := (4547450232698713514940474043982008888757707352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree008.table
  base := (315771672928755169129539188212619125121/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-289652596174776143511664370400000000000000)
      constant := (1031772662080177960973454383610468616069696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13043729868748773229/10000000000000000000)
  centralHi := (130437298687487732291/100000000000000000000)
  directionLo := (34860834438919814499/25000000000000000000)
  directionHi := (139443337755679257997/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree009.table
  base := (3078074395927326357737839640761626259507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-463444502507115968294171267789400000000000000)
      constant := (1656621548440344021704155938031655877774023112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree009.table
  base := (2880098252825186532313551077055365397857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-105512007123896935090190395800000000000000)
      constant := (376792243008658186259871006999664384774284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34860834438919814499/25000000000000000000)
  centralHi := (139443337755679257997/100000000000000000000)
  directionLo := (18487749322186300133/12500000000000000000)
  directionHi := (29580398915498080213/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree010.table
  base := (1323001409148870270573427770875164632771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-1508201965052563316888600820589200000000000000)
      constant := (5529705917305869144045778006575403184512962008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree010.table
  base := (141993804995286349340784973629352420733/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-343419446568605467029478004400000000000000)
      constant := (1260074419245496724980652268905253497171104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18487749322186300133/12500000000000000000)
  centralHi := (29580398915498080213/20000000000000000000)
  directionLo := (31180478223116178213/20000000000000000000)
  directionHi := (77951195557790445533/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree011.table
  base := (-64798030707353007723937449056812515301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-1626070422583778728894687837810200000000000000)
      constant := (6205889448853121758960069436776836666132813104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree011.table
  base := (-19384778808994648031490497058336696501/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-370302871765520128788384821400000000000000)
      constant := (1416183580326993304551244327719398062815424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31180478223116178213/20000000000000000000)
  centralHi := (77951195557790445533/50000000000000000000)
  directionLo := (163511807252904862237/100000000000000000000)
  directionHi := (81755903626452431119/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree012.table
  base := (-170112303306824008627228182227282181721/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-581312960038331380300258285010400000000000000)
      constant := (2328501219334392530444685174264107262831035712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree012.table
  base := (-24027231061399230040820616804787464353/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-132395432320811596849097212800000000000000)
      constant := (531947160033721304647634817893923227376896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163511807252904862237/100000000000000000000)
  centralHi := (81755903626452431119/50000000000000000000)
  directionLo := (170782512765993306387/100000000000000000000)
  directionHi := (42695628191498326597/25000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree013.table
  base := (-302819821485318586709482162616653205111/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-1861807337646209552906861872252200000000000000)
      constant := (7860333256557542908886396462380584828268045376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree013.table
  base := (-324675225283123839539808503723682356761/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-424069722159349452306198455400000000000000)
      constant := (1797226761162275145001758249752579481252832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (170782512765993306387/100000000000000000000)
  centralHi := (42695628191498326597/25000000000000000000)
  directionLo := (17775607506417951459/10000000000000000000)
  directionHi := (177756075064179514591/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree014.table
  base := (-418611536673183881290668056562816394449/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-1979675795177424964912948889473200000000000000)
      constant := (8824920385843808410065732423606427424765403584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree014.table
  base := (-13760894533749878952717614733084629331/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-450953147356264114065105272400000000000000)
      constant := (2019127825629496549885941148719892056085504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17775607506417951459/10000000000000000000)
  centralHi := (177756075064179514591/100000000000000000000)
  directionLo := (184466196843155461033/100000000000000000000)
  directionHi := (92233098421577730517/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree015.table
  base := (-416374656677730261009193153916078288869/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-699181417569546792306345302231400000000000000)
      constant := (3291824077350906004558823959964289434373210960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree015.table
  base := (-4337345763821350270617298141061787819311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-159278857517726258608004029800000000000000)
      constant := (753566927931740333596541061182258546168268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184466196843155461033/100000000000000000000)
  centralHi := (92233098421577730517/50000000000000000000)
  directionLo := (190940653956493333607/100000000000000000000)
  directionHi := (23867581744561666701/12500000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree016.table
  base := (-610553109459565320355060868883517591239/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-2215412710239855788925122923915200000000000000)
      constant := (11009236710721719841528987243521714353188956224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree016.table
  base := (-2529063801886893586581685953468811255333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-504719997750093437582918906400000000000000)
      constant := (2521331637228721001208319401750245589616024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190940653956493333607/100000000000000000000)
  centralHi := (23867581744561666701/12500000000000000000)
  directionLo := (39440531887330773617/20000000000000000000)
  directionHi := (98601329718326934043/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree017.table
  base := (-5523974619906403528051614444675250994787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-2333281167771071200931209941136200000000000000)
      constant := (12224138659003722030040127448237003179781117224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree017.table
  base := (-2849014645072319335065619246458371952341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-531603422947008099341825723400000000000000)
      constant := (2800556174222691628920526721679997219431448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39440531887330773617/20000000000000000000)
  centralHi := (98601329718326934043/50000000000000000000)
  directionLo := (203271848627507799433/100000000000000000000)
  directionHi := (101635924313753899717/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree018.table
  base := (-1523138635115970697533113801650602481393/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-817049875100762204312432319452400000000000000)
      constant := (4506187449820214565999835167529716635385874848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree018.table
  base := (-7833892042678106524695428758578239249/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-186162282714640920366910846800000000000000)
      constant := (1032670711191207995809923039817648903209600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203271848627507799433/100000000000000000000)
  centralHi := (101635924313753899717/50000000000000000000)
  directionLo := (104582503316759443497/50000000000000000000)
  directionHi := (41833001326703777399/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree019.table
  base := (-6598278751485656468263378908982250567391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-2569018082833502024943383975578200000000000000)
      constant := (14891217248467271601043721970964803511757596232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree019.table
  base := (-1693358047291088213615523358141900588669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-585370273340837422859639357400000000000000)
      constant := (3413409659359225139568803907652566315231664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104582503316759443497/50000000000000000000)
  centralHi := (41833001326703777399/20000000000000000000)
  directionLo := (10744830798523022293/5000000000000000000)
  directionHi := (214896615970460445861/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree020.table
  base := (-1409551546321747434895617529133252216389/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-2686886540364717436949470992799200000000000000)
      constant := (16341051972617346157254040602741072507438811640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree020.table
  base := (-288942099437742859879814395774864847369/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-612253698537752084618546174400000000000000)
      constant := (3746512320473095208118743761802621637367900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10744830798523022293/5000000000000000000)
  centralHi := (214896615970460445861/100000000000000000000)
  directionLo := (1763834207376393727/800000000000000000)
  directionHi := (55119818980512303969/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree021.table
  base := (-7446459712384214461762653770089681524789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-934918332631977616318519336673400000000000000)
      constant := (5955732270206376558469044187416262944281786376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree021.table
  base := (-7622911487031852346839125403627722247507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-213045707911555582125817663800000000000000)
      constant := (1365708128754457529966067097831467333029916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1763834207376393727/800000000000000000)
  centralHi := (55119818980512303969/25000000000000000000)
  directionLo := (28240503566095748121/12500000000000000000)
  directionHi := (225924028528765984969/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree022.table
  base := (-1559792481901131242019901766494256498563/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-2922623455427148260961645027241200000000000000)
      constant := (19468923685946991571327552076288757462082759880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree022.table
  base := (-3988031418298308242593886811489882926127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-666020548931581408136359808400000000000000)
      constant := (4465081925540030125984178690872728429318856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28240503566095748121/12500000000000000000)
  centralHi := (225924028528765984969/100000000000000000000)
  directionLo := (115620307712596732889/50000000000000000000)
  directionHi := (231240615425193465779/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree023.table
  base := (-506820960265950605682918726004651585949/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-3040491912958363672967732044462200000000000000)
      constant := (21145617155799088885787620680076507292927735168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree023.table
  base := (-16573713435730424783794555257097871373/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-692903974128496069895266625400000000000000)
      constant := (4850246331706883271101860923197238315286000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115620307712596732889/50000000000000000000)
  centralHi := (231240615425193465779/100000000000000000000)
  directionLo := (118218841325925895933/50000000000000000000)
  directionHi := (236437682651851791867/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree024.table
  base := (-8380276575586304794129787734086552390043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-1052786790163193028324606353894400000000000000)
      constant := (7632250893345958833886939856719267338489480312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree024.table
  base := (-2139643781664418259692531203052623363531/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-239929133108470243884724480800000000000000)
      constant := (1750833150971470279422119481453474078550512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118218841325925895933/50000000000000000000)
  centralHi := (236437682651851791867/100000000000000000000)
  directionLo := (60380736442455994057/25000000000000000000)
  directionHi := (241522945769823976229/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree025.table
  base := (-8615217737224454285555600269870548005589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-3276228828020794496979906078904200000000000000)
      constant := (24721879883439699064564742592577941580807080728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree025.table
  base := (-2198509091222043543068228670920367818237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-746670824522325393413080259400000000000000)
      constant := (5671739830293702500604873672012467034173872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60380736442455994057/25000000000000000000)
  centralHi := (241522945769823976229/100000000000000000000)
  directionLo := (123251662147908667553/50000000000000000000)
  directionHi := (246503324295817335107/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree026.table
  base := (-1102050878701688306260905588419302742031/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-3394097285552009908985993096125200000000000000)
      constant := (26620609387801323392485301268233143899883628096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree026.table
  base := (-359827096492233994508089810425203162777/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-773554249719240055171987076400000000000000)
      constant := (6107879732573789431586729077517317153500700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123251662147908667553/50000000000000000000)
  centralHi := (246503324295817335107/100000000000000000000)
  directionLo := (251385052149972601437/100000000000000000000)
  directionHi := (125692526074986300719/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree027.table
  base := (-1797195056786242870681931520350883627767/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-1170655247694408440330693371115400000000000000)
      constant := (9530867429561863405277145935963125267951523640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree027.table
  base := (-71606404937215513361079513635538551869/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-266812558305384905643631297800000000000000)
      constant := (2186947594494922583202054152530812784329216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251385052149972601437/100000000000000000000)
  centralHi := (125692526074986300719/50000000000000000000)
  directionLo := (12808688457449497979/5000000000000000000)
  directionHi := (256173769148989959581/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree028.table
  base := (-9125789459217389109399429541030064733957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-3629834200614440732998167130567200000000000000)
      constant := (30637561649991135656563308231712850264193607064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree028.table
  base := (-232643076601422974337625839942642223757/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-827321100113069378689800710400000000000000)
      constant := (7030562043179598113350538239682595197789920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12808688457449497979/5000000000000000000)
  centralHi := (256173769148989959581/100000000000000000000)
  directionLo := (260874597374975464581/100000000000000000000)
  directionHi := (130437298687487732291/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree029.table
  base := (-9237496213855698977803280605228001436981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-3747702658145656145004254147788200000000000000)
      constant := (32755225573995354045304716204412309327451045912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree029.table
  base := (-9417627845642635095301193426364988521473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-854204525309984040448707527400000000000000)
      constant := (7516978445124236246881274721875860413226972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260874597374975464581/100000000000000000000)
  centralHi := (130437298687487732291/50000000000000000000)
  directionLo := (26549220536789985223/10000000000000000000)
  directionHi := (265492205367899852231/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree030.table
  base := (-186451152170248327051340215980751601039/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-1288523705225623852336780388336400000000000000)
      constant := (11648453840957798696781123375613973655965818800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree030.table
  base := (-1900558354612200655038121155779007475899/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-293695983502299567402538114800000000000000)
      constant := (2673346505283477486337783252153259551446060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26549220536789985223/10000000000000000000)
  centralHi := (265492205367899852231/100000000000000000000)
  directionLo := (67507715608415210739/25000000000000000000)
  directionHi := (270030862433660842957/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree031.table
  base := (-9382280480336366372459532270596510140477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-3983439573208086969016428182230200000000000000)
      constant := (37207761646790415451008352059664678755177414104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree031.table
  base := (-47812592694771259157693481055589721203/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-907971375703813363966521161400000000000000)
      constant := (8539698322423066530285608023424754007338400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67507715608415210739/25000000000000000000)
  centralHi := (270030862433660842957/100000000000000000000)
  directionLo := (137247242433338366711/50000000000000000000)
  directionHi := (274494484866676733423/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree032.table
  base := (-9417840681890321685011580134417705696539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-4101308030739302381022515199451200000000000000)
      constant := (39542238928748008263255193644387532744376865128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree032.table
  base := (-4798991017780162895556538240143657911251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-934854800900728025725427978400000000000000)
      constant := (9075912604721572439734415499509656630389928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137247242433338366711/50000000000000000000)
  centralHi := (274494484866676733423/100000000000000000000)
  directionLo := (34860834438919814499/12500000000000000000)
  directionHi := (278886675511358515993/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree033.table
  base := (-9430303127604796264689090457245007400813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-1406392162756839264342867405557400000000000000)
      constant := (13982874665411943380157678893822336187638497992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree033.table
  base := (-9610246267984255695690778078418683549911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-320579408699214229161444931800000000000000)
      constant := (3209548019520723029285266350333975797401068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34860834438919814499/12500000000000000000)
  centralHi := (278886675511358515993/100000000000000000000)
  directionLo := (141605378899720237051/50000000000000000000)
  directionHi := (283210757799440474103/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree034.table
  base := (-9420638402930280136783855469773038884603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-4337044945801733205034689233893200000000000000)
      constant := (44426762479579151545119272200195587711481662056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree034.table
  base := (-2400070458611137179654613475249637932263/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-988621651294557349243241612400000000000000)
      constant := (10197857742408990216409279173664052137754128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141605378899720237051/50000000000000000000)
  centralHi := (283210757799440474103/100000000000000000000)
  directionLo := (287469805177672336503/100000000000000000000)
  directionHi := (35933725647209042063/12500000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree035.table
  base := (-938973654707982207111491050069416349767/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-4454913403332948617040776251114200000000000000)
      constant := (46976512819821215496451722269615407184022581840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree035.table
  base := (-47844897931194452211505220562270706647/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1015505076491472011002148429400000000000000)
      constant := (10783521585615319144428278021576650912141600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287469805177672336503/100000000000000000000)
  centralHi := (35933725647209042063/12500000000000000000)
  directionLo := (145833333333333333333/50000000000000000000)
  directionHi := (291666666666666666667/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree036.table
  base := (-9338418506946056088116280885761935247513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-1524260620288054676348954422778400000000000000)
      constant := (16532581482333547446262798676041845240917850792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree036.table
  base := (-4758580983258400428482720867880196775557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-347462833896128890920351748800000000000000)
      constant := (3795201993409257717421542481970875277386632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145833333333333333333/50000000000000000000)
  centralHi := (291666666666666666667/100000000000000000000)
  directionLo := (18487749322186300133/6250000000000000000)
  directionHi := (295803989154980802129/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree037.table
  base := (-1853489133881613459385370318734252675523/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-4690650318395379441052950285556200000000000000)
      constant := (52290336264057087343690972099224985402317089480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree037.table
  base := (-147587381814237593752978543999237969653/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1069271926885301334519962063400000000000000)
      constant := (12004083441656366902565484165050755717919488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18487749322186300133/6250000000000000000)
  centralHi := (295803989154980802129/100000000000000000000)
  directionLo := (74971059231027423321/25000000000000000000)
  directionHi := (59976847384821938657/20000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree038.table
  base := (-9177527806366630580450501819660228744167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-4808518775926594853059037302777200000000000000)
      constant := (55054175383189276067583354304669529938697726984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree038.table
  base := (-4677491660673634880123801102818765826397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1096155352082215996278868880400000000000000)
      constant := (12638928326153394495353092076297048860499416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74971059231027423321/25000000000000000000)
  centralHi := (59976847384821938657/20000000000000000000)
  directionLo := (303909708813507817343/100000000000000000000)
  directionHi := (2374294600105529823/781250000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree039.table
  base := (-9069329707617132241422073485201083010081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-1642129077819270088355041439999400000000000000)
      constant := (19296385356969943969929390502177616883137545704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree039.table
  base := (-4623001179563282526291213049790610397287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-374346259093043552679258565800000000000000)
      constant := (4430038865063466435223797694880025350465112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303909708813507817343/100000000000000000000)
  centralHi := (2374294600105529823/781250000000000000)
  directionLo := (30788255336518609993/10000000000000000000)
  directionHi := (307882553365186099931/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree040.table
  base := (-1788695345654618381998667365730879762831/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-5044255690989025677071211337219200000000000000)
      constant := (60795178865738659800169044951944175177406275560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree040.table
  base := (-1823855633176019650905820757615951955953/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1149922202476045319796682514400000000000000)
      constant := (13957625618575865103936362999629128647928460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30788255336518609993/10000000000000000000)
  centralHi := (307882553365186099931/100000000000000000000)
  directionLo := (311804782231161782131/100000000000000000000)
  directionHi := (77951195557790445533/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree041.table
  base := (-1100069929720375221906366089345674067503/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-5162124148520241089077298354440200000000000000)
      constant := (63772149838789296913036123220839506347294262848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree041.table
  base := (-1795080963413285576569088224092091230001/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1176805627672959981555589331400000000000000)
      constant := (14641434009593283783544720810688423578599820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311804782231161782131/100000000000000000000)
  centralHi := (77951195557790445533/25000000000000000000)
  directionLo := (39459785260157939407/12500000000000000000)
  directionHi := (315678282081263515257/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree042.table
  base := (-8641137524791779189423943446084386123161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-1759997535350485500361128457220400000000000000)
      constant := (22273326657564201184450691107528940185294496424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree042.table
  base := (-4407472845551829179519310868385907272271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-401229684289958214438165382800000000000000)
      constant := (5113840495539867861774069302258738225465496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39459785260157939407/12500000000000000000)
  centralHi := (315678282081263515257/100000000000000000000)
  directionLo := (79876206302836724879/25000000000000000000)
  directionHi := (319504825211346899517/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree043.table
  base := (-8465743085784804769432131984823409577789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-5397861063582671913089472388882200000000000000)
      constant := (69938584638576315784757042706148218853471815128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree043.table
  base := (-4319218352326507062557192266359071632599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1230572478066789305073402965400000000000000)
      constant := (16057868756655020429356617687647146842452872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79876206302836724879/25000000000000000000)
  centralHi := (319504825211346899517/100000000000000000000)
  directionLo := (323286079021180386007/100000000000000000000)
  directionHi := (40410759877647548251/12500000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree044.table
  base := (-4137441701087982605650730881119368823619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-5515729521113887325095559406103200000000000000)
      constant := (73127883154342936796021493303517253254682090576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree044.table
  base := (-1689277808792611548589260516233783312381/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1257455903263703966832309782400000000000000)
      constant := (16790457416994586063420501522677919003771420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323286079021180386007/100000000000000000000)
  centralHi := (40410759877647548251/12500000000000000000)
  directionLo := (13080944580232388979/4000000000000000000)
  directionHi := (81755903626452431119/25000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree045.table
  base := (-8069043293619344813918008194561093012639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-1877865992881700912367215474441400000000000000)
      constant := (25462599470132041262525397530631086592841930776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree045.table
  base := (-2059822869671041576998406038952135979111/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-428113109486872876197072199800000000000000)
      constant := (5846423290643628970692442158005297473002672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13080944580232388979/4000000000000000000)
  centralHi := (81755903626452431119/25000000000000000000)
  directionLo := (82679728470768455953/25000000000000000000)
  directionHi := (330718913883073823813/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree046.table
  base := (-3924343559555832225859745871841088931427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-5751466436176318149107733440545200000000000000)
      constant := (79718256551366166297783570007253286975268797008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree046.table
  base := (-4008806164738818141843201801607781245701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1311222753657533290350123416400000000000000)
      constant := (18304289261920116302643610585184239750309528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82679728470768455953/25000000000000000000)
  centralHi := (330718913883073823813/100000000000000000000)
  directionLo := (167186688731157328609/50000000000000000000)
  directionHi := (334373377462314657219/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree047.table
  base := (-7614260485548412269154214616043058557783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33840000000000000000000000000000000000000000
      center := (80319)
      previous := (0)
      next := (58425)
      square := (2166035973008552747431920684000000000000000)
      linear := (-124879465823564543853485541654600000000000000)
      constant := (1768493334135479802728625786814197789840462328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree047.table
  base := (-3890900574152147789685254567361400616569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1338106178854447952109030233400000000000000)
      constant := (19085499403091684430382902600574979155607032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167186688731157328609/50000000000000000000)
  centralHi := (334373377462314657219/100000000000000000000)
  directionLo := (168994164922277058417/50000000000000000000)
  directionHi := (67597665968910823367/20000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree048.table
  base := (-1841547928235133473499721128587529873433/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-1995734450412916324373302491662400000000000000)
      constant := (28863506915319725399585029568078414064920304288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree048.table
  base := (-1883072540004372896784655938799968449197/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-454996534683787537955979016800000000000000)
      constant := (6627628245116956929726621977337601514438544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168994164922277058417/50000000000000000000)
  centralHi := (67597665968910823367/20000000000000000000)
  directionLo := (170782512765993306387/50000000000000000000)
  directionHi := (13662601021279464511/4000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree049.table
  base := (-3552446548505955450276684885063764636527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-6105071808769964385125994492208200000000000000)
      constant := (90132193101330750792683354720764869224179307408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree049.table
  base := (-7269495505421606581360063096894924239363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1391873029248277275626843867400000000000000)
      constant := (20696430277628717617157205216736782727382932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (170782512765993306387/50000000000000000000)
  centralHi := (13662601021279464511/4000000000000000000)
  directionLo := (345104654014144269149/100000000000000000000)
  directionHi := (6902093080282885383/2000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree050.table
  base := (-3415381001434364992664608048871949957961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-6222940266301179797132081509429200000000000000)
      constant := (93744140570356865728323441707077278206172437744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree050.table
  base := (-437113644935907144921547577726418047887/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1418756454445191937385750684400000000000000)
      constant := (21526121589084741459073362827729583204417088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345104654014144269149/100000000000000000000)
  centralHi := (6902093080282885383/2000000000000000000)
  directionLo := (34860834438919814499/10000000000000000000)
  directionHi := (348608344389198144991/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree051.table
  base := (-1308836363524601833472104848512256099137/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-2113602907944131736379389508883400000000000000)
      constant := (32475434058694709587928004669274708653240764040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree051.table
  base := (-67056456685509501337256362930286159073/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-481879959880702199714885833800000000000000)
      constant := (7457314911758483947629584571158656609112400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34860834438919814499/10000000000000000000)
  centralHi := (348608344389198144991/100000000000000000000)
  directionLo := (70415433914258693101/20000000000000000000)
  directionHi := (176038584785646732753/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree052.table
  base := (-3122761392525871863285863617460120778789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-6458677181363610621144255543871200000000000000)
      constant := (101178619031980296353783650398395805420750334256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree052.table
  base := (-6405351379929629307282352228037125572707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1472523304839021260903564318400000000000000)
      constant := (23233886258472815018488109970590663479382548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70415433914258693101/20000000000000000000)
  centralHi := (176038584785646732753/50000000000000000000)
  directionLo := (355512150128359029181/100000000000000000000)
  directionHi := (177756075064179514591/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree053.table
  base := (-148378568535128271369050494014685844511/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-6576545638894826033150342561092200000000000000)
      constant := (105001034224905447135361072562410502332088578880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree053.table
  base := (-3046648382371853596077494626697973049993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1499406730035935922662471135400000000000000)
      constant := (24111933151458037393172788711702745940400504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (355512150128359029181/100000000000000000000)
  centralHi := (177756075064179514591/50000000000000000000)
  directionLo := (1794571288946502429/500000000000000000)
  directionHi := (358914257789300485801/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree054.table
  base := (-140334694204935437885500300900116064641/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-2231471365475347148385476526104400000000000000)
      constant := (36297830903762301052489114674054527868679709760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree054.table
  base := (-1442457816849091816400732846500350618531/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-508763385077616861473792650800000000000000)
      constant := (8335357611410868120587150704067983170310512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1794571288946502429/500000000000000000)
  centralHi := (358914257789300485801/100000000000000000000)
  directionLo := (181142209327367982171/50000000000000000000)
  directionHi := (362284418654735964343/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree055.table
  base := (-5280592775102561240845074033004747937283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-6812282553957256857162516595534200000000000000)
      constant := (112855941224410840822505314582374973350071013416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree055.table
  base := (-679411630471373000371009292091668871691/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1553173580429765246180284769400000000000000)
      constant := (25916293133184714443141791926502599364952992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181142209327367982171/50000000000000000000)
  centralHi := (362284418654735964343/100000000000000000000)
  directionLo := (365623516141338419183/100000000000000000000)
  directionHi := (22851469758833651199/6250000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree056.table
  base := (-4937082023835354531257973407933613751303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-6930151011488472269168603612755200000000000000)
      constant := (116888328191100045812899871588838174600082760456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree056.table
  base := (-5090009482359486103825860191566969584389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1580057005626679907939191586400000000000000)
      constant := (26842582262328658204129092239503589094961996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (365623516141338419183/100000000000000000000)
  centralHi := (22851469758833651199/6250000000000000000)
  directionLo := (184466196843155461033/50000000000000000000)
  directionHi := (368932393686310922067/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree057.table
  base := (-2291584801022679757333892663184879400981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-2349339823006562560391563543325400000000000000)
      constant := (40330201218780676857105142551539418367355182608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree057.table
  base := (-2367148838305809934471871896562816342381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-535646810274531523232699467800000000000000)
      constant := (9261642935433414925965241558957492407782856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184466196843155461033/50000000000000000000)
  centralHi := (368932393686310922067/100000000000000000000)
  directionLo := (46526482154431863587/12500000000000000000)
  directionHi := (372211857235454908697/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree058.table
  base := (-4219159854718525694672812854202107691347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-7165887926550903093180777647197200000000000000)
      constant := (125162719214675469801103679873691713175906642344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree058.table
  base := (-1092116213951112493026905859567755407511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1633823856020509231457005220400000000000000)
      constant := (28743321704845499836185396899922243221318416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46526482154431863587/12500000000000000000)
  centralHi := (372211857235454908697/100000000000000000000)
  directionLo := (1877313387678134989/500000000000000000)
  directionHi := (375462677535626997801/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree059.table
  base := (-3845347779314025153537908693720425517323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-7283756384082118505186864664418200000000000000)
      constant := (129404627947344477100924567953464766262320811496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree059.table
  base := (-998202195122522271964810470303847892397/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1660707281217423893215912037400000000000000)
      constant := (29717750238584547322714606169501245903494832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1877313387678134989/500000000000000000)
  centralHi := (375462677535626997801/100000000000000000000)
  directionLo := (47335699031257347407/12500000000000000000)
  directionHi := (378685592250058779257/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree060.table
  base := (-3462019389815615997687803301256030412137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-2467208280537777972397650560546400000000000000)
      constant := (44572094788132321237155817121439610291670144808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree060.table
  base := (-144304724302179768808611503229346125219/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-562530235471446184991606284800000000000000)
      constant := (10236068005289830928446250567031196162434300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47335699031257347407/12500000000000000000)
  centralHi := (378685592250058779257/100000000000000000000)
  directionLo := (76376261582597333443/20000000000000000000)
  directionHi := (23867581744561666701/6250000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree061.table
  base := (-383681506751213583972583200866846643797/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-7519493299144549329199038698860200000000000000)
      constant := (138097644351041236624330337654255250699978997952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree061.table
  base := (-3213172729073401103040449439253822427653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1714474131611253216733725671400000000000000)
      constant := (31714672960585609737638704694211862392604492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76376261582597333443/20000000000000000000)
  centralHi := (23867581744561666701/6250000000000000000)
  directionLo := (385050501738264053503/100000000000000000000)
  directionHi := (1504103522415093959/390625000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree062.table
  base := (-2667914807584837825768930544218581590049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-7637361756675764741205125716081200000000000000)
      constant := (142548665117689105780507591951976773035265886648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree062.table
  base := (-561948817690379869835538597255751440941/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1741357556808167878492632488400000000000000)
      constant := (32737147300770314953552118389793964740630620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (385050501738264053503/100000000000000000000)
  centralHi := (1504103522415093959/390625000000000000)
  directionLo := (194096911647535265751/50000000000000000000)
  directionHi := (388193823295070531503/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree063.table
  base := (-282208581006683557628001200636497099769/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-2585076738068993384403737577767400000000000000)
      constant := (49023101717736069548820364667502081258069173568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree063.table
  base := (-2397595476756048419016878536137496956397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-589413660668360846750513101800000000000000)
      constant := (11258539185981743430834985938841350036523236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194096911647535265751/50000000000000000000)
  centralHi := (388193823295070531503/100000000000000000000)
  directionLo := (391311896062463196871/100000000000000000000)
  directionHi := (48913987007807899609/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree064.table
  base := (-114935425687845746758107940956147904509/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-7873098671738195565217299750523200000000000000)
      constant := (151659524180984437817562227724025705409338441088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree064.table
  base := (-1976982311667068711372219918441768434659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1795124407201997202010446122400000000000000)
      constant := (34830074537073831820139911276536096336352276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (391311896062463196871/100000000000000000000)
  centralHi := (48913987007807899609/12500000000000000000)
  directionLo := (394405318873307736171/100000000000000000000)
  directionHi := (98601329718326934043/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree065.table
  base := (-706027515398031969270930795558768470887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-7990967129269410977223386767744200000000000000)
      constant := (156319283117460093583518254426449250484484728848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree065.table
  base := (-154815240109349835742790958519600724099/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1822007832398911863769352939400000000000000)
      constant := (35900509317071412163734347841557943739324360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (394405318873307736171/100000000000000000000)
  centralHi := (98601329718326934043/25000000000000000000)
  directionLo := (198737333628530343573/50000000000000000000)
  directionHi := (397474667257060687147/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree066.table
  base := (-977171787432149702046655573291850341031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-2702945195600208796409824594988400000000000000)
      constant := (53682848010955669682113403944928509262319900504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree066.table
  base := (-111134619314983423040970596114473475403/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-616297085865275508509419918800000000000000)
      constant := (12328971080601949811950713402766263182951640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198737333628530343573/50000000000000000000)
  centralHi := (397474667257060687147/100000000000000000000)
  directionLo := (40052049468993052599/10000000000000000000)
  directionHi := (400520494689930525991/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree067.table
  base := (-534548541144964600738649227581231314003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-8226704044331841801235560802186200000000000000)
      constant := (165847270113918336227037687515207872821970450856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree067.table
  base := (-333398506969826501962980268001016012101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1875774682792741187287166573400000000000000)
      constant := (38089277911537414876243387723128926847128728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40052049468993052599/10000000000000000000)
  centralHi := (400520494689930525991/100000000000000000000)
  directionLo := (4035433337601083731/1000000000000000000)
  directionHi := (403543333760108373101/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree068.table
  base := (-84409955901022088350974444021956064329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-8344572501863057213241647819407200000000000000)
      constant := (170715425628259529093821334306869795931880601208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree068.table
  base := (-107365647178599122221657452437353305729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1902658107989655849046073390400000000000000)
      constant := (39207595174753915716515291288624510561987512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4035433337601083731/1000000000000000000)
  centralHi := (403543333760108373101/100000000000000000000)
  directionLo := (406543697255015598867/100000000000000000000)
  directionHi := (101635924313753899717/25000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree069.table
  base := (373025887085460217489936573048651949071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-2820813653131424208415911612209400000000000000)
      constant := (58550991963503209587680967806845284831731948136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree069.table
  base := (6115780326604833173485778342988056193/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-643180511062190170268326735800000000000000)
      constant := (13447285706788050611569431370679634266972640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406543697255015598867/100000000000000000000)
  centralHi := (101635924313753899717/25000000000000000000)
  directionLo := (409522079176853825141/100000000000000000000)
  directionHi := (204761039588426912571/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree070.table
  base := (837547284936727751934203195696010138227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-8580309416925488037253821853849200000000000000)
      constant := (180659887229749334126672151042094309020464727896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree070.table
  base := (142215445276473069609385985379250283979/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1956424958383485172563887024400000000000000)
      constant := (41492056070218205601784083677868265051116220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409522079176853825141/100000000000000000000)
  centralHi := (204761039588426912571/50000000000000000000)
  directionLo := (412478955692152722567/100000000000000000000)
  directionHi := (51559869461519090321/12500000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree071.table
  base := (65447435851120510651780508323303964391/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-8698177874456703449259908871070200000000000000)
      constant := (185736126958333426048925135527277609478569195360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree071.table
  base := (1184399734808590393519559717115834583111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-1983308383580399834322793841400000000000000)
      constant := (42658184571927682830429713602841170044991996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (412478955692152722567/100000000000000000000)
  centralHi := (51559869461519090321/12500000000000000000)
  directionLo := (103853696505120980589/25000000000000000000)
  directionHi := (415414786020483922357/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree072.table
  base := (446757664134415354709187275993393167941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-2938682110662639620421998629430400000000000000)
      constant := (63627221113974215784751298329281062928766240224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree072.table
  base := (1664397806961188301829192779305302674527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-670063936259104832027233552800000000000000)
      constant := (14613411797320947678276723762951663632094324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103853696505120980589/25000000000000000000)
  centralHi := (415414786020483922357/100000000000000000000)
  directionLo := (418330013267037773989/100000000000000000000)
  directionHi := (41833001326703777399/10000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree073.table
  base := (2271599389180758217794500308743822115159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-8933914789519134273272082905512200000000000000)
      constant := (196096465570644737578851799321828999919771808632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree073.table
  base := (2150876406258173000082632436668609516273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-2037075233974229157840607475400000000000000)
      constant := (45038201509006734716361301655545069942585828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418330013267037773989/100000000000000000000)
  centralHi := (41833001326703777399/10000000000000000000)
  directionLo := (421225065203337057487/100000000000000000000)
  directionHi := (26326566575208566093/6250000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree074.table
  base := (172654177402430893306200385191328315703/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-9051783247050349685278169922733200000000000000)
      constant := (201380503731306487903611096504452616175294891904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree074.table
  base := (2643646212970099243328017276529414221339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-2063958659171143819599514292400000000000000)
      constant := (46252076107549097846204837692055058911968204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (421225065203337057487/100000000000000000000)
  centralHi := (26326566575208566093/6250000000000000000)
  directionLo := (106025088749995604257/25000000000000000000)
  directionHi := (424100354999982417029/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree075.table
  base := (651890079410950919808477524178029957199/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-3056550568193855032428085646651400000000000000)
      constant := (68911249593529612295079124386800049681054310920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree075.table
  base := (628504690503120658353687814197562364471/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-696947361456019493786140369800000000000000)
      constant := (15827284190568334443242696900726853741868260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106025088749995604257/25000000000000000000)
  centralHi := (424100354999982417029/100000000000000000000)
  directionLo := (426956281914983265967/100000000000000000000)
  directionHi := (26684767619686454123/6250000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree076.table
  base := (3762372764299838270993724195195765575779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-9287520162112780509290343957175200000000000000)
      constant := (212156172519165517918117477276849696123296498392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree076.table
  base := (1823664864816688883916034946247783600119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-2117725509564973143117327926400000000000000)
      constant := (48727524479245044101338474880529840419208568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426956281914983265967/100000000000000000000)
  centralHi := (26684767619686454123/6250000000000000000)
  directionLo := (429793231940920891721/100000000000000000000)
  directionHi := (214896615970460445861/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree077.table
  base := (1067765447181303045275474118886054951801/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-9405388619643995921296430974396200000000000000)
      constant := (217647747566692881086164721804210569571896181792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree077.table
  base := (2078945934053617551723456848480465911709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-2144608934761887804876234743400000000000000)
      constant := (49989085595825437408585398369515593545643048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429793231940920891721/100000000000000000000)
  centralHi := (214896615970460445861/50000000000000000000)
  directionLo := (54076447301739209001/12500000000000000000)
  directionHi := (432611578413913672009/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree078.table
  base := (957070063219582369757141260472431681397/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-3174419025725070444434172663872400000000000000)
      constant := (74402815779208160618223876112532982190104716760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree078.table
  base := (2337020877878467864036149361335214542399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-723830786652934155545047186800000000000000)
      constant := (17088843289802564875643132328572045149017576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54076447301739209001/12500000000000000000)
  centralHi := (432611578413913672009/100000000000000000000)
  directionLo := (54426460323388047181/12500000000000000000)
  directionHi := (435411682587104377449/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree079.table
  base := (530507604226279112805253539843435529551/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-9641125534706426745308605008838200000000000000)
      constant := (228838246017809052539410362925260299841040274480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree079.table
  base := (103912323888755493540684871749462495369/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-2198375785155717128394048377400000000000000)
      constant := (52559851424858606377642207399374032491664200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54426460323388047181/12500000000000000000)
  centralHi := (435411682587104377449/100000000000000000000)
  directionLo := (438193894171163559001/100000000000000000000)
  directionHi := (219096947085581779501/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree080.table
  base := (728760171337034238393614017608090026571/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-9758993992237642157314692026059200000000000000)
      constant := (234537118541834711406958759412516252020368515264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree080.table
  base := (2861228377408757205683501632976704851397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-2225259210352631790152955194400000000000000)
      constant := (53869044558722212109321062789574322749300584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438193894171163559001/100000000000000000000)
  centralHi := (219096947085581779501/50000000000000000000)
  directionLo := (1763834207376393727/400000000000000000)
  directionHi := (440958551844098431751/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree081.table
  base := (3180106637270510346978306607601746156339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-3292287483256285856440259681093400000000000000)
      constant := (80101680190361950775258132872550065848448936848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree081.table
  base := (6254409635720931990718361653591828121581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-750714211849848817303954003800000000000000)
      constant := (18398034578052067932037761125518101937458972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1763834207376393727/400000000000000000)
  centralHi := (440958551844098431751/100000000000000000000)
  directionLo := (55463247966558900399/12500000000000000000)
  directionHi := (443705983732471203193/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree082.table
  base := (430957697683105351388060786289663563551/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-9994730907300072981326866060501200000000000000)
      constant := (246141988472482205670519299840202424567290551168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree082.table
  base := (6791325527850683783758159918905179436371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-2279026060746461113670768828400000000000000)
      constant := (56535023576025877067290983442380586459709356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55463247966558900399/12500000000000000000)
  centralHi := (443705983732471203193/100000000000000000000)
  directionLo := (44643650786596245343/10000000000000000000)
  directionHi := (446436507865962453431/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree083.table
  base := (1858816687855569999124915000361498110267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-10112599364831288393332953077722200000000000000)
      constant := (252047939297872160119166477068843394705766983264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree083.table
  base := (1466611896341786516934191901351305335669/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-2305909485943375775429675645400000000000000)
      constant := (57891798866149309783444807199068234960420420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44643650786596245343/10000000000000000000)
  centralHi := (446436507865962453431/100000000000000000000)
  directionLo := (22457521630353109331/5000000000000000000)
  directionHi := (449150432607062186621/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree084.table
  base := (1994975984098913121502134490017035384631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-3410155940787501268446346698314400000000000000)
      constant := (86007623588018220232950549690559572591806388384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree084.table
  base := (3939735389778843074381019643717357871081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-777597637046763479062860820800000000000000)
      constant := (19754808179562644741255248228649216588905944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22457521630353109331/5000000000000000000)
  centralHi := (449150432607062186621/100000000000000000000)
  directionLo := (451848057057531969937/100000000000000000000)
  directionHi := (225924028528765984969/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree085.table
  base := (2132274668308909201691357221264170078423/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-10348336279893719217345127112164200000000000000)
      constant := (264066761233405913490441927046325307390532085216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree085.table
  base := (4215211405633719632147943257558880835971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-2359676336337205098947489279400000000000000)
      constant := (60652895675677088200631317444169239420189912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451848057057531969937/100000000000000000000)
  centralHi := (225924028528765984969/50000000000000000000)
  directionLo := (90905934288630953429/20000000000000000000)
  directionHi := (227264835721577383573/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree086.table
  base := (4541359429096415313640987824037928503089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-10466204737424934629351214129385200000000000000)
      constant := (270179589695088783551918750768235618905118598544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree086.table
  base := (4492891476956902294764445222548848381061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-2386559761534119760706396096400000000000000)
      constant := (62057207502691493769738755486923517083436392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90905934288630953429/20000000000000000000)
  centralHi := (227264835721577383573/50000000000000000000)
  directionLo := (45719555747817342257/10000000000000000000)
  directionHi := (457195557478173422571/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree087.table
  base := (1928127242754404759840455267949372049793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-3528024398318716680452433715535400000000000000)
      constant := (92120445248941404233202136916842257042959128440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree087.table
  base := (4772711227495308821085623579230168064091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-804481062243678140821767637800000000000000)
      constant := (21159118461546976336575208624376524033538184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45719555747817342257/10000000000000000000)
  centralHi := (457195557478173422571/100000000000000000000)
  directionLo := (459845988710713158193/100000000000000000000)
  directionHi := (229922994355356579097/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree088.table
  base := (1020272617753321277493626668195519415201/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-10701941652487365453363388163827200000000000000)
      constant := (282611979577205243249267802449893209719488886480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree088.table
  base := (252730407977893025055697915967108138323/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-2440326611927949084224209730400000000000000)
      constant := (64913334821691636253472107162192635719185120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (459845988710713158193/100000000000000000000)
  centralHi := (229922994355356579097/50000000000000000000)
  directionLo := (462481230850386931557/100000000000000000000)
  directionHi := (231240615425193465779/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree089.table
  base := (10768867794189105809619626238681207763913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-10819810110018580865369475181048200000000000000)
      constant := (288931501948535342023465745429626881232434834824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree089.table
  base := (10677043198112447665715279198156483871189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-2467210037124863745983116547400000000000000)
      constant := (66365141445309255488834789045358633419362804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462481230850386931557/100000000000000000000)
  centralHi := (231240615425193465779/50000000000000000000)
  directionLo := (93020308415838838143/20000000000000000000)
  directionHi := (116275385519798547679/25000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree090.table
  base := (11338943610890193144703947785131460838983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-3645892855849932092458520732756400000000000000)
      constant := (98439961393391233398040877539146279527839522728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree090.table
  base := (5624392642177939448682817294318421599571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-831364487440592802580674454800000000000000)
      constant := (22610923671473096547114678104563642118389704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93020308415838838143/20000000000000000000)
  centralHi := (116275385519798547679/25000000000000000000)
  directionLo := (467707173346742673197/100000000000000000000)
  directionHi := (233853586673371336599/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree091.table
  base := (2382567915118790905236540350193031193931/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-11055547025081011689381649215490200000000000000)
      constant := (301777108132371058999879233498225518626661688440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree091.table
  base := (5912164103639184075731740660468449456223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-2520976887518693069500930181400000000000000)
      constant := (69316219411681303435354084913578728360848056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467707173346742673197/100000000000000000000)
  centralHi := (233853586673371336599/50000000000000000000)
  directionLo := (470298368650748729721/100000000000000000000)
  directionHi := (235149184325374364861/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree092.table
  base := (12490444938419708154567435177760044267959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-11173415482612227101387736232711200000000000000)
      constant := (308303156190580395761890508605855779520730343032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree092.table
  base := (1550445116616712407084249082684664334351/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-2547860312715607731259836998400000000000000)
      constant := (70815482639873233088696887082613183328293088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470298368650748729721/100000000000000000000)
  centralHi := (235149184325374364861/50000000000000000000)
  directionLo := (118218841325925895933/25000000000000000000)
  directionHi := (472875365303703583733/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree093.table
  base := (13071652155895057622108847413557880616979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-3763761313381147504464607749977400000000000000)
      constant := (104966003750075837592098915723412322098789758664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree093.table
  base := (12986375666523666616009715367485554169879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-858247912637507464339581271800000000000000)
      constant := (24110185606127447733293630834684826650038548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118218841325925895933/25000000000000000000)
  centralHi := (472875365303703583733/100000000000000000000)
  directionLo := (475438394186530403171/100000000000000000000)
  directionHi := (118859598546632600793/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree094.table
  base := (13656356798003938884860606584380613550331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33840000000000000000000000000000000000000000
      center := (80319)
      previous := (0)
      next := (58425)
      square := (2166035973008552747431920684000000000000000)
      linear := (-242747923354779955859572558875600000000000000)
      constant := (6841737376636749257213539851052693996254320104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree094.table
  base := (13572667757794896084885443077869892583829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-2601627163109437054777650632400000000000000)
      constant := (73861438179799512299701033748903316133017844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (475438394186530403171/100000000000000000000)
  centralHi := (118859598546632600793/25000000000000000000)
  directionLo := (477987679989999556287/100000000000000000000)
  directionHi := (7468557499843743067/1562500000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree095.table
  base := (14244457457949967918181434905516460245491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-11527020855205873337405997284374200000000000000)
      constant := (328294076417131351413758240144471894469124852568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree095.table
  base := (7081167804608712124077212021656554945353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-2628510588306351716536557449400000000000000)
      constant := (75408123066613661705212027754184271956065416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (477987679989999556287/100000000000000000000)
  centralHi := (7468557499843743067/1562500000000000000)
  directionLo := (480523441444616495389/100000000000000000000)
  directionHi := (48052344144461649539/10000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree096.table
  base := (7417927832276095681288462426602384706551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-3881629770912362916470694767198400000000000000)
      constant := (111698418244731844493513827359127904055205015632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree096.table
  base := (2951056117371993639894817828753125125021/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-885131337834422126098488088800000000000000)
      constant := (25656869309334421743928514010525187507501260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (480523441444616495389/100000000000000000000)
  centralHi := (48052344144461649539/10000000000000000000)
  directionLo := (483045891539647952457/100000000000000000000)
  directionHi := (241522945769823976229/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree097.table
  base := (7715227898596744376961923390672027687581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-11762757770268304161418171318816200000000000000)
      constant := (341965176444851849513808227369458921819308765776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree097.table
  base := (3837851733469996718225472494754821637799/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-2682277438700181040054371083400000000000000)
      constant := (78548889316721991401047644838669694315843056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483045891539647952457/100000000000000000000)
  centralHi := (241522945769823976229/50000000000000000000)
  directionLo := (485555237731907170587/100000000000000000000)
  directionHi := (121388809432976792647/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree098.table
  base := (16028165003244800489087211977357977422857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-11880626227799519573424258336037200000000000000)
      constant := (348903826781075352841799062335939681593150560136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree098.table
  base := (996913855409349448015744879920389991313/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-2709160863897095701813277900400000000000000)
      constant := (80142963886075636205391643470534144634996288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (485555237731907170587/100000000000000000000)
  centralHi := (121388809432976792647/25000000000000000000)
  directionLo := (488051682144877402987/100000000000000000000)
  directionHi := (122012920536219350747/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree099.table
  base := (8314446558945544705227757335980205454081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-3999498228443578328476781784419400000000000000)
      constant := (118637063800777513811556730735744190644707116592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree099.table
  base := (16552834592741130809600585241385532781891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-912014763031336787857394905800000000000000)
      constant := (27250942795662534744961429583971626393382692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (488051682144877402987/100000000000000000000)
  centralHi := (122012920536219350747/25000000000000000000)
  directionLo := (490535421758714586713/100000000000000000000)
  directionHi := (245267710879357293357/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree100.table
  base := (17232552586287509959448510604023381332719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-12116363142861950397436432370479200000000000000)
      constant := (362987256383200452296020546294093710754206291512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree100.table
  base := (17157958032798893861572526992521285657513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-2762927714290925025331091534400000000000000)
      constant := (83378479665150289859852067561730766283670468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (490535421758714586713/100000000000000000000)
  centralHi := (245267710879357293357/50000000000000000000)
  directionLo := (493006648591634670213/100000000000000000000)
  directionHi := (246503324295817335107/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree101.table
  base := (17839058387976677477389151280764726533317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-12234231600393165809442519387700200000000000000)
      constant := (370132008201345379310656857387843080725671002216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree101.table
  base := (17765906942725819177375862222225756825289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-2789811139487839687089998351400000000000000)
      constant := (85019914658259798879010472180025127245710404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (493006648591634670213/100000000000000000000)
  centralHi := (246503324295817335107/50000000000000000000)
  directionLo := (30966596867072393523/6250000000000000000)
  directionHi := (495465549873158296369/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree102.table
  base := (4612081990875054598602307272056704427157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-4117366685974793740482868801640400000000000000)
      constant := (125781811241950195693012908934631982967640622048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree102.table
  base := (229707484245205734729190352211490864467/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-938898188228251449616301722800000000000000)
      constant := (28892376797777178388375729849223031229888320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30966596867072393523/6250000000000000000)
  centralHi := (495465549873158296369/100000000000000000000)
  directionLo := (497912308209655193563/100000000000000000000)
  directionHi := (124478077052413798391/25000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree103.table
  base := (9530140571569977008874949711423538296509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-12469968515455596633454693422142200000000000000)
      constant := (384627520205882738716440245825744894337966326864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree103.table
  base := (18989953249269649743184329762659518492189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-2843577989881669010607811985400000000000000)
      constant := (88350123984094256853036633041280742665718804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497912308209655193563/100000000000000000000)
  centralHi := (124478077052413798391/25000000000000000000)
  directionLo := (250173550871301252263/50000000000000000000)
  directionHi := (500347101742602504527/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree104.table
  base := (4918710019431534612005655137128868213597/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-12587836972986812045460780439363200000000000000)
      constant := (391978255259687084477055465667345088926544702624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree104.table
  base := (9802946317958237496465305532240330190597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-2870461415078583672366718802400000000000000)
      constant := (90038892628460282927895070647921303773722984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250173550871301252263/50000000000000000000)
  centralHi := (500347101742602504527/100000000000000000000)
  directionLo := (4022160834399561623/800000000000000000)
  directionHi := (125692526074986300719/25000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree105.table
  base := (20291929171452144998819091148871590810671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-4235235143506009152488955818861400000000000000)
      constant := (133132542287967257333221506273644013758418533736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree105.table
  base := (20224341334001119029984134747888950245567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-965781613425166111375208539800000000000000)
      constant := (30581144535356534677263088207849667402946804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4022160834399561623/800000000000000000)
  centralHi := (125692526074986300719/25000000000000000000)
  directionLo := (101036297108184508789/20000000000000000000)
  directionHi := (252590742770461271973/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree106.table
  base := (5227868754159221003743308792274752911033/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-12823573888049242869472954473805200000000000000)
      constant := (406885623343181939336792551222139309603975906336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree106.table
  base := (20845225981954166421940406610970935548841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-2924228265472412995884532436400000000000000)
      constant := (93463744275905721209152653176894953679758276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101036297108184508789/20000000000000000000)
  centralHi := (252590742770461271973/50000000000000000000)
  directionLo := (507581411094702018037/100000000000000000000)
  directionHi := (253790705547351009019/50000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree107.table
  base := (4306681266075609108479009018021842259213/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-12941442345580458281479041491026200000000000000)
      constant := (414442233360124539894861455355070902338216546120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree107.table
  base := (21468475357899754607005504809460849045083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-2951111690669327657643439253400000000000000)
      constant := (95199822073981103407760655121565590565622988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507581411094702018037/100000000000000000000)
  centralHi := (253790705547351009019/50000000000000000000)
  directionLo := (509970042693141382571/100000000000000000000)
  directionHi := (127492510673285345643/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree108.table
  base := (4431530778608199839824084817569513044587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-4353103601037224564495042836082400000000000000)
      constant := (140689148635161708326960201849351526517859121960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree108.table
  base := (4418804063447956888173353149032167006291/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-992665038622080773134115356800000000000000)
      constant := (32317221503696739686139338189341930020377460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509970042693141382571/100000000000000000000)
  centralHi := (127492510673285345643/25000000000000000000)
  directionLo := (512347538297979919161/100000000000000000000)
  directionHi := (256173769148989959581/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree109.table
  base := (22784150488529856249696909209855750880867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-13177179260642889105491215525468200000000000000)
      constant := (429761250288678075683253758473427749966100134616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree109.table
  base := (4544358746412023395564879256545760499309/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-3004878541063156981161252887400000000000000)
      constant := (98719269170628159159079538963403236889875620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512347538297979919161/100000000000000000000)
  centralHi := (256173769148989959581/50000000000000000000)
  directionLo := (128678513055685494357/25000000000000000000)
  directionHi := (514714052222741977429/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree110.table
  base := (234128308462888099726787451467682469593/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-13295047718174104517497302542689200000000000000)
      constant := (437523636128552032054548409640746446142382746400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree110.table
  base := (11675865216152673883546219601938356959623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-3031761966260071642920159704400000000000000)
      constant := (100502633706472929149516933847839561701092856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128678513055685494357/25000000000000000000)
  centralHi := (514714052222741977429/100000000000000000000)
  directionLo := (258534867624809512419/50000000000000000000)
  directionHi := (517069735249619024839/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree111.table
  base := (2404363158498342399823754659488162477263/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-4470972058568439976501129853303400000000000000)
      constant := (148451531114810838219672031341409081718945752080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree111.table
  base := (4796753429734070871693953546903312509943/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-1019548463818995434893022173800000000000000)
      constant := (34100585280309848207174319552489198750596580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258534867624809512419/50000000000000000000)
  centralHi := (517069735249619024839/100000000000000000000)
  directionLo := (259707367370790362541/50000000000000000000)
  directionHi := (519414734741580725083/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree112.table
  base := (6169122789453259482532124931351110312713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-13530784633236535341509476577131200000000000000)
      constant := (453254112147423972061954866474028525572065508896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree112.table
  base := (3077230307144795272479711019413460485143/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-3085528816653900966437973338400000000000000)
      constant := (104116633362734121690501340418391076619721184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259707367370790362541/50000000000000000000)
  centralHi := (519414734741580725083/100000000000000000000)
  directionLo := (260874597374975464581/50000000000000000000)
  directionHi := (521749194749950929163/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree113.table
  base := (2531134979940690837368469411070685195119/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-13648653090767750753515563594352200000000000000)
      constant := (461222183031963718267929744220456615889132867120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree113.table
  base := (2525389672525677149973246804989572729717/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-3112412241850815628196880155400000000000000)
      constant := (105947264125116206766119384763621246182698120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260874597374975464581/50000000000000000000)
  centralHi := (521749194749950929163/100000000000000000000)
  directionLo := (524073256117670803033/100000000000000000000)
  directionHi := (262036628058835401517/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree114.table
  base := (3243518684282263028548177510276358219303/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-4588840516099655388507216870524400000000000000)
      constant := (156419598922540148966421703144047841258836542784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree114.table
  base := (12945936029841718255751062499591523990989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-1046431889015910096651928990800000000000000)
      constant := (35931215347972547533112540108690196575783736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524073256117670803033/100000000000000000000)
  centralHi := (262036628058835401517/50000000000000000000)
  directionLo := (526387056578458560157/100000000000000000000)
  directionHi := (263193528289229280079/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree115.table
  base := (3323354228331316278205941639126819665201/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-13884390005830181577527737628794200000000000000)
      constant := (477363944391130224435683350138374551812887109184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree115.table
  base := (530634245113149781542339122112659549983/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-3166179092244644951714693789400000000000000)
      constant := (109655777095766317937186977801427787189969400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526387056578458560157/100000000000000000000)
  centralHi := (263193528289229280079/50000000000000000000)
  directionLo := (264345365426031674587/50000000000000000000)
  directionHi := (21147629234082533967/4000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree116.table
  base := (13613674066017882199860461254221244078861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-14002258463361396989533824646015200000000000000)
      constant := (485537617198663073460375842733382960856509368656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree116.table
  base := (5434672549530031302902287833727087485299/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-3193062517441559613473600606400000000000000)
      constant := (111533655316303196963113098390470875747353820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264345365426031674587/50000000000000000000)
  centralHi := (21147629234082533967/4000000000000000000)
  directionLo := (530984410735799704461/100000000000000000000)
  directionHi := (265492205367899852231/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree117.table
  base := (6967409812454416363869734856778887411489/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-4706708973630870800513303887745400000000000000)
      constant := (164593268912771152964211761324081695480030003296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree117.table
  base := (27816770561572336965194157798224224042373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-1073315314212824758410835807800000000000000)
      constant := (37809092932820357336736763701053690688508476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530984410735799704461/100000000000000000000)
  centralHi := (265492205367899852231/50000000000000000000)
  directionLo := (133317056298134635943/25000000000000000000)
  directionHi := (533268225192538543773/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree118.table
  base := (28513655577503936641419665802672275150351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-14237995378423827813545998680457200000000000000)
      constant := (502090504802808185918728796790342270018113025848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree118.table
  base := (28461884268356969128810053058727557701693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-3246829367835388936991414240400000000000000)
      constant := (115336645690793528871665773817814192077260948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133317056298134635943/25000000000000000000)
  centralHi := (533268225192538543773/100000000000000000000)
  directionLo := (535542300435320940443/100000000000000000000)
  directionHi := (133885575108830235111/25000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree119.table
  base := (5831869401237005078584698768681510607771/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-14355863835955043225552085697678200000000000000)
      constant := (510469703422425408022358761807619396995723810040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree119.table
  base := (29108653938895467140935107591770921256199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-3273712793032303598750321057400000000000000)
      constant := (117261754195852658456360281909528753165223164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535542300435320940443/100000000000000000000)
  centralHi := (133885575108830235111/25000000000000000000)
  directionLo := (2151227040035007039/400000000000000000)
  directionHi := (537806760008751759751/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree120.table
  base := (7451666219325473547395476248901752946117/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-4824577431162086212519390904966400000000000000)
      constant := (172972464952706209134659748321715101336765355488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree120.table
  base := (29757031100288687615645887195088667496659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-1100198739409739420169742624800000000000000)
      constant := (39734200856204697200800190582341064009959908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2151227040035007039/400000000000000000)
  centralHi := (537806760008751759751/100000000000000000000)
  directionLo := (540061724867321685913/100000000000000000000)
  directionHi := (270030862433660842957/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree121.table
  base := (30455561940665319166168403894905330512633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-14591600751017474049564259732120200000000000000)
      constant := (527433571594839748386273702628208415507373253384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree121.table
  base := (6081393738674811156458233566839596877283/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-3327479643426132922268134691400000000000000)
      constant := (121159189114947975618043199265056127437910940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540061724867321685913/100000000000000000000)
  centralHi := (270030862433660842957/50000000000000000000)
  directionLo := (108461462690159627447/20000000000000000000)
  directionHi := (135576828362699534309/25000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree122.table
  base := (6221198462738092065056726399617511820559/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-14709469208548689461570346749341200000000000000)
      constant := (536018226335055417337335761619227480100181339160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree122.table
  base := (7764605257872900632198577603551588260579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-3354363068623047584027041508400000000000000)
      constant := (123131512190134551615253405456211428709523376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108461462690159627447/20000000000000000000)
  centralHi := (135576828362699534309/25000000000000000000)
  directionLo := (544543641756818034539/100000000000000000000)
  directionHi := (27227182087840901727/5000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree123.table
  base := (15878955720905750965235461570843837775363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-4942445888693301624525477922187400000000000000)
      constant := (181557117330817016798637820699411851306997289616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree123.table
  base := (317113437604527552517058004113383388607/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-1127082164606654081928649441800000000000000)
      constant := (41706523399141010326769002599211060066328400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544543641756818034539/100000000000000000000)
  centralHi := (27227182087840901727/5000000000000000000)
  directionLo := (136692705852702079479/25000000000000000000)
  directionHi := (546770823410808317917/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree124.table
  base := (6482255212008436989214131812385522029111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-14945206123611120285582520783783200000000000000)
      constant := (553392941685817113034903213099615262538430231640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree124.table
  base := (3236569381967678386377663090286990330823/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-3408129919016876907544855142400000000000000)
      constant := (127123361586632507430063042040103316519096280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136692705852702079479/25000000000000000000)
  centralHi := (546770823410808317917/100000000000000000000)
  directionLo := (137247242433338366711/25000000000000000000)
  directionHi := (109797793946670693369/20000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree125.table
  base := (8266511038912261575653824535739578382517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-15063074581142335697588607801004200000000000000)
      constant := (562182988733112373420032341064449046350330255264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree125.table
  base := (33021429404460830216875768664234545112961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-3435013344213791569303761959400000000000000)
      constant := (129142884852793678071188790987537443624066596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137247242433338366711/25000000000000000000)
  centralHi := (109797793946670693369/20000000000000000000)
  directionLo := (551198189805123039687/100000000000000000000)
  directionHi := (68899773725640379961/12500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree126.table
  base := (8430543732976285828541788802173750457897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-5060314346224517036531564939408400000000000000)
      constant := (190347162215233001590329276346950324217103469408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree126.table
  base := (33678509929350445598784693636785617158123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-1153965589803568743687556258800000000000000)
      constant := (43726046178276727583348129305941427405897476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551198189805123039687/100000000000000000000)
  centralHi := (68899773725640379961/12500000000000000000)
  directionLo := (553398590529466383099/100000000000000000000)
  directionHi := (5533985905294663831/1000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree127.table
  base := (34379628772892976714741273601334325242421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-15298811496204766521600781835446200000000000000)
      constant := (579968429122744560664513301642310734261156575208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree127.table
  base := (1373475839703141113727784814823707017783/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-3488780194607620892821575593400000000000000)
      constant := (133229121214278405788642716554766336316004700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553398590529466383099/100000000000000000000)
  centralHi := (5533985905294663831/1000000000000000000)
  directionLo := (4444722213542209159/800000000000000000)
  directionHi := (138897569173194036219/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree128.table
  base := (218989795058288958915318164192250848931/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (3774993)
      previous := (0)
      next := (2745975)
      square := (101803690731401979129300272148000000000000000)
      linear := (-15416679953735981933606868852667200000000000000)
      constant := (588963810045785991578197027524001458083324430080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree128.table
  base := (1093642166923171496684216144772539774537/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (861)
      previous := (0)
      next := (615)
      square := (23042935883069710079062986000000000000000)
      linear := (-3515663619804535554580482410400000000000000)
      constant := (135295831514044617980960194137977965820266624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell170.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4444722213542209159/800000000000000000)
  centralHi := (138897569173194036219/25000000000000000000)
  directionLo := (111554670204543406397/20000000000000000000)
  directionHi := (278886675511358515993/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree129.table
  base := (35698352885360851191992425377088866558713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1258331)
      previous := (0)
      next := (915325)
      square := (33934563577133993043100090716000000000000000)
      linear := (-5178182803755732448537651956629400000000000000)
      constant := (199342541157817003699379793095081780849476728408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree129.table
  base := (35657432839282386286082353766597305633477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (287)
      previous := (0)
      next := (205)
      square := (7680978627689903359687662000000000000000)
      linear := (-1180849015000483405446463075800000000000000)
      constant := (45792756032399456502087968145274167667601724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell170.Kernel129
