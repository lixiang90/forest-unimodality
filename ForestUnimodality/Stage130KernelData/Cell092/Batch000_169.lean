import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell092.Parameters
import ForestUnimodality.BinomialMassData.Q21967_42642.Batch000_049
import ForestUnimodality.BinomialMassData.Q21967_42642.Batch050_099
import ForestUnimodality.BinomialMassData.Q21967_42642.Batch100_149
import ForestUnimodality.BinomialMassData.Q21967_42642.Batch150_199
import ForestUnimodality.BinomialMassData.Q10996_21321.Batch000_049
import ForestUnimodality.BinomialMassData.Q10996_21321.Batch050_099
import ForestUnimodality.BinomialMassData.Q10996_21321.Batch100_149
import ForestUnimodality.BinomialMassData.Q10996_21321.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree000.table
  base := (449707915192960154487877847/5000000000000000000000000)
  polynomial :=
    { denominator := 1000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (9)
      square := (60786982288656657424930074000000000000)
      linear := (-2360020918369480722592834700000000000)
      constant := (89941583038592030897575569400000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree000.table
  base := (449707915192960154487877847/5000000000000000000000000)
  polynomial :=
    { denominator := 1000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (9)
      square := (60786982288656657424930074000000000000)
      linear := (-2360020918369480722592834700000000000)
      constant := (89941583038592030897575569400000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree001.table
  base := (122810905032058248203202279008286322565523/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-49238207328317157148189241555729734500000000000)
      constant := (37231809938747736223865375669115524535374998760962) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree001.table
  base := (245390090951530042954596767317262106225741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-49292208963707842506229113810219484500000000000)
      constant := (37196726807680104331151754433818485404124942580127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49975232767290864339/100000000000000000000)
  directionHi := (2498761638364543217/5000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree002.table
  base := (284061346806237604052237408925727780876867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-193376728626809135101328388261566529000000000000)
      constant := (43144806456690462138285489166302272771249867048849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree002.table
  base := (70898041686434325617298087618987969018843/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-96796367584185938266743938639762764500000000000)
      constant := (21536969624378763540440186987400990560624983285042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49975232767290864339/100000000000000000000)
  centralHi := (2498761638364543217/5000000000000000000)
  directionLo := (14135130392451008451/20000000000000000000)
  directionHi := (4417228247640940141/6250000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree003.table
  base := (88205786612800267248771106513947284986927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (5117194969621344527858294835448710000000000000)
      linear := (-16015391255387997550348794078426310500000000000)
      constant := (1497604224037897563773816069217654449328551657741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree003.table
  base := (176047555786014387570579087414355381161293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-10688927867012150668685834331059707000000000000)
      constant := (996378680993970373437957392997554146293543284173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14135130392451008451/20000000000000000000)
  centralHi := (4417228247640940141/6250000000000000000)
  directionLo := (43279821136514379971/50000000000000000000)
  directionHi := (86559642273028759943/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree004.table
  base := (14802458800703236458601370972905218979259/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-191588678283579388355614099280890324500000000000)
      constant := (9171204259393705489744735285714143461400574219492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree004.table
  base := (59080074636024617097624447305784886662001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-191804684825142129787773588298849324500000000000)
      constant := (9151991404195391493343204327922106621475359242347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43279821136514379971/50000000000000000000)
  centralHi := (86559642273028759943/100000000000000000000)
  directionLo := (49975232767290864339/50000000000000000000)
  directionHi := (99950465534581728679/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree005.table
  base := (85514219932686576794097222958336917764209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-478077670537333597516178103711887709000000000000)
      constant := (13578137499343950081649057566444016250385525532523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree005.table
  base := (42666141077747184369055782643588031790127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-239308843445620225548288413128392604500000000000)
      constant := (6775985494291254017729800645103826816141395230069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49975232767290864339/50000000000000000000)
  centralHi := (99950465534581728679/100000000000000000000)
  directionLo := (55874008829518650603/50000000000000000000)
  directionHi := (111748017659037301207/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree006.table
  base := (6553668211902079823311082176671189563887/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5612161000000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (341146331308089635190552989029914000000000000)
      linear := (-2122140683361142290078251884674054700000000000)
      constant := (40080368716782714953318015454594866594053629807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree006.table
  base := (13081271572105876876886883828841932573999/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (606113388)
      previous := (303056694)
      next := (303056694)
      square := (2046877987848537811143317934179484000000000000)
      linear := (-12747244536271036502613477242574928200000000000)
      constant := (240088186995232195903121093816572662669280405517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55874008829518650603/50000000000000000000)
  centralHi := (111748017659037301207/100000000000000000000)
  directionLo := (24482764011336150617/20000000000000000000)
  directionHi := (61206910028340376543/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree007.table
  base := (52433931291471846534969325338893332436721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-667878298477683239126077914012101829000000000000)
      constant := (9155874553912861391678396737098234168957815230187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree007.table
  base := (52336386906034811519388352694678809410949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-668634321373152834138636125574958329000000000000)
      constant := (9143836294946184386977171711431235793969145671303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24482764011336150617/20000000000000000000)
  centralHi := (61206910028340376543/50000000000000000000)
  directionLo := (66111018807408946019/50000000000000000000)
  directionHi := (132222037614817892039/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree008.table
  base := (43158135364812220984435351128613878338243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-762778612447858059931027819162208889000000000000)
      constant := (8118829542680448842175416969674334277853068674321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree008.table
  base := (21540619156897042335456072011316465085001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-381821319307054512829832887617022444500000000000)
      constant := (4055378539462532787735528559769944144213416023347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66111018807408946019/50000000000000000000)
  centralHi := (132222037614817892039/100000000000000000000)
  directionLo := (141351303924510084511/100000000000000000000)
  directionHi := (4417228247640940141/3125000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree009.table
  base := (36146625190338231365661049933225627423083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-31765886163630847434665841641196887000000000000)
      constant := (276806512845301037691830632492089225924356912363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree009.table
  base := (7216609673384501175319488272972495443791/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (682292662616179270381105978059828000000000000)
      linear := (-6360377450778260868005151295504677400000000000)
      constant := (55323483354453911920622961217763326602321542351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141351303924510084511/100000000000000000000)
  centralHi := (4417228247640940141/3125000000000000000)
  directionLo := (149925698301872593017/100000000000000000000)
  directionHi := (74962849150936296509/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree010.table
  base := (30575174191072923495186407450760129754011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-952579240388207701540927629462423009000000000000)
      constant := (7095819775578112793675996352160820570130803449817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree010.table
  base := (3815081987280944542535673786244397638711/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-476829636548010704350862537276109004500000000000)
      constant := (3546573311221289775703959242300096068818324162868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149925698301872593017/100000000000000000000)
  centralHi := (74962849150936296509/50000000000000000000)
  directionLo := (39508890535429668833/25000000000000000000)
  directionHi := (158035562141718675333/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree011.table
  base := (25990439445214090058229942695927081987701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-1047479554358382522345877534612530069000000000000)
      constant := (6916267025380564434804978314384597707629806860247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree011.table
  base := (25942543403236178375580067095745717297281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-1048667590336977600222754724211304569000000000000)
      constant := (6915768486595510663767294574019085478386297524507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39508890535429668833/25000000000000000000)
  centralHi := (158035562141718675333/100000000000000000000)
  directionLo := (165749095899778371993/100000000000000000000)
  directionHi := (82874547949889185997/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree012.table
  base := (4425691487611817229874751621116303045409/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (606113388)
      previous := (303056694)
      next := (303056694)
      square := (2046877987848537811143317934179484000000000000)
      linear := (-25386219296190163181129498661391936200000000000)
      constant := (153224880915095132489342835599979005646876856547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree012.table
  base := (1104289152382373344903687306604321095583/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5612161000000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (341146331308089635190552989029914000000000000)
      linear := (-4235836694733088117569571755075522700000000000)
      constant := (25543314167434285552363073669845752968216369726) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165749095899778371993/100000000000000000000)
  centralHi := (82874547949889185997/50000000000000000000)
  directionLo := (34623856909211503977/20000000000000000000)
  directionHi := (86559642273028759943/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree013.table
  base := (3764904934664421420139304377210315860241/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303056694000000000000000000000000000000000000000
      center := (5455020492)
      previous := (2727510246)
      next := (2727510246)
      square := (18421901890636840300289861407615356000000000000)
      linear := (-247456036459746432791155468982548837800000000000)
      constant := (1401484074887390750885468176454110538550201751627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree013.table
  base := (9393118317327175476945772217896513514857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-619342112409444991632407011764738844500000000000)
      constant := (3505527024316526075513875087444110815969441151379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34623856909211503977/20000000000000000000)
  centralHi := (86559642273028759943/50000000000000000000)
  directionLo := (180188264245715327139/100000000000000000000)
  directionHi := (9009413212285766357/5000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree014.table
  base := (998002500539188780439272904752425453239/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-666090248134453492380363625031425624500000000000)
      constant := (3618205008436507906693313464713306075860251727464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree014.table
  base := (15933601379817870792705207888883050843487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-1333692542059846174785843673188564249000000000000)
      constant := (7242132158277362926069682372214862026630540825989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180188264245715327139/100000000000000000000)
  centralHi := (9009413212285766357/5000000000000000000)
  directionLo := (93495099419740491329/50000000000000000000)
  directionHi := (186990198839480982659/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree015.table
  base := (53918131101686118772881725222304743753/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5612161000000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (341146331308089635190552989029914000000000000)
      linear := (-5285484482366969650243248723010956700000000000)
      constant := (28037209294247232406485495342098719575139505825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree015.table
  base := (13448559616716851735064667050777914076261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (3030566940)
      previous := (1515283470)
      next := (1515283470)
      square := (10234389939242689055716589670897420000000000000)
      linear := (-158744539922311374034097035871961201000000000000)
      constant := (841990031028832379920944732385798627120429030063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93495099419740491329/50000000000000000000)
  centralHi := (186990198839480982659/100000000000000000000)
  directionLo := (1209707776440979489/625000000000000000)
  directionHi := (193553244230556718241/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree016.table
  base := (5649346251763196224523297221413846803371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-760990562104628313185313530181532684500000000000)
      constant := (3999595553152555594300409874269560021026041657737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree016.table
  base := (11270877966213140813329238473445559189783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-1523709176541758557827902972506737369000000000000)
      constant := (8009261347204409026864473579829640402518477278701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1209707776440979489/625000000000000000)
  centralHi := (193553244230556718241/100000000000000000000)
  directionLo := (199900931069163457357/100000000000000000000)
  directionHi := (99950465534581728679/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree017.table
  base := (9377899796213806245147482357727299821307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-1616881438179431447175576965513172429000000000000)
      constant := (8516628118976790006750157047977549029196045089529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree017.table
  base := (1870595280524081952966662565669999297113/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303056694000000000000000000000000000000000000000
      center := (5455020492)
      previous := (2727510246)
      next := (2727510246)
      square := (18421901890636840300289861407615356000000000000)
      linear := (-323743498756542949869786524433164785800000000000)
      constant := (1705795127893929777331298748397276370582694762211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199900931069163457357/100000000000000000000)
  centralHi := (99950465534581728679/50000000000000000000)
  directionLo := (206053163364369008517/100000000000000000000)
  directionHi := (103026581682184504259/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree018.table
  base := (3839273034177449965135276930341806380353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-31699662076844560518157905012282953500000000000)
      constant := (168824208377355603271737242493958222937368272833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree018.table
  base := (3828134112268519048991464031926698491847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-31735663167105017423517819848609453500000000000)
      constant := (169096410684734090045407455797722280134702551367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206053163364369008517/100000000000000000000)
  centralHi := (103026581682184504259/50000000000000000000)
  directionLo := (106013477943382563383/50000000000000000000)
  directionHi := (212026955886765126767/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree019.table
  base := (3084399352607570193676549731018516943763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-903341033059890544392738387906693274500000000000)
      constant := (4897002481507468625663256012159186255629899349761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree019.table
  base := (3074467735318496659164841164808511602199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-904367064132313566195495960741998524500000000000)
      constant := (4905565818318870661149473591963966972611536035053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106013477943382563383/50000000000000000000)
  centralHi := (212026955886765126767/100000000000000000000)
  directionLo := (108918494656271700083/50000000000000000000)
  directionHi := (217836989312543400167/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree020.table
  base := (4822141164367680804936086156627384054199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-1901582380089955909590426680963493609000000000000)
      constant := (10545103243047898564945651907421070030666932879053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree020.table
  base := (2402236954408707735755412054684932518451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-951871222752791661956010785571541804500000000000)
      constant := (5282367937988449781670122139453442270327427030497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108918494656271700083/50000000000000000000)
  centralHi := (217836989312543400167/100000000000000000000)
  directionLo := (223496035318074602413/100000000000000000000)
  directionHi := (111748017659037301207/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree021.table
  base := (361634918065423716739282406442709659319/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16836483000000000000000000000000000000000000000
      center := (303056694)
      previous := (151528347)
      next := (151528347)
      square := (1023438993924268905571658967089742000000000000)
      linear := (-22183141045112563671059739845706674100000000000)
      constant := (126293716514592911636519958415329234503060135077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree021.table
  base := (360067133592107907884653576056898158667/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5612161000000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (341146331308089635190552989029914000000000000)
      linear := (-7402780602764961168270560077045074700000000000)
      constant := (42180196728020270472908360697695874827042749387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223496035318074602413/100000000000000000000)
  centralHi := (111748017659037301207/50000000000000000000)
  directionLo := (229015287029147799967/100000000000000000000)
  directionHi := (7156727719660868749/3125000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree022.table
  base := (633182082347778038072830236245282304609/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-1045691504015152775600163245631853864500000000000)
      constant := (6127582978770445522616749635040538324831504502646) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree022.table
  base := (2518845847210590494588010597659372755231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-2093759079987495706954080870461256729000000000000)
      constant := (12280052520259792987105366258056240990656989033157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229015287029147799967/100000000000000000000)
  centralHi := (7156727719660868749/3125000000000000000)
  directionLo := (23440461937254533349/10000000000000000000)
  directionHi := (234404619372545333491/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree023.table
  base := (311103991255325784073410331627250566441/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 572886000000000000000000000000000000000000000
      center := (10311948)
      previous := (5155974)
      next := (5155974)
      square := (34824011135419357845538490373564000000000000)
      linear := (-826572144423622068811068580874788200000000000)
      constant := (4993916738711987912288779869677899634003059363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree023.table
  base := (771625914220130650080182678380950720003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1432215000000000000000000000000000000000000000
      center := (25779870)
      previous := (12889935)
      next := (12889935)
      square := (87060027838548394613846225933910000000000000)
      linear := (-2068778258249954535420709376295220500000000000)
      constant := (12510915104121654653739957212900168667089819329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23440461937254533349/10000000000000000000)
  centralHi := (234404619372545333491/100000000000000000000)
  directionLo := (23967279669026428239/10000000000000000000)
  directionHi := (239672796690264282391/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree024.table
  base := (671423679980864620677662885068723144583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-84488282813727970104082455613478587000000000000)
      constant := (526875946317515560161368315642192918351826073863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree024.table
  base := (330301129378653101934899648958486254789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (5117194969621344527858294835448710000000000000)
      linear := (-126876428581633782777563342765523880500000000000)
      constant := (792007040886769380652417130648935793534488667087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23967279669026428239/10000000000000000000)
  centralHi := (239672796690264282391/100000000000000000000)
  directionLo := (24482764011336150617/10000000000000000000)
  directionHi := (244827640113361506171/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree025.table
  base := (-130794177328193603185829120997328161693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-2376083949940830013615176206714028909000000000000)
      constant := (15303686066947411882478462908105755534742110988529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree025.table
  base := (-35080783135352320899045134859308479813/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-1189392015855182140758584909719258204500000000000)
      constant := (7668543999295334587240527947295284866981706481778) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24482764011336150617/10000000000000000000)
  centralHi := (244827640113361506171/100000000000000000000)
  directionLo := (7808630119889197553/3125000000000000000)
  directionHi := (249876163836454321697/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree026.table
  base := (-860625699377517616486718485168803454891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-2470984263911004834420126111864135969000000000000)
      constant := (16441578003259949656309524234045424635512477704823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree026.table
  base := (-173800647493508794521897361716553437891/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303056694000000000000000000000000000000000000000
      center := (5455020492)
      previous := (2727510246)
      next := (2727510246)
      square := (18421901890636840300289861407615356000000000000)
      linear := (-494758469790264094607639893819520593800000000000)
      constant := (3295599129441850685521174996079468347819209603823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7808630119889197553/3125000000000000000)
  centralHi := (249876163836454321697/100000000000000000000)
  directionLo := (127412343538378832637/50000000000000000000)
  directionHi := (10192987483070306611/4000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree027.table
  base := (-1526093328284696067179709474178150866839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-95032762143747394637965778407934927000000000000)
      constant := (653263360448798224385169897472088931153009970921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree027.table
  base := (-766723869167101406903529952386835791513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-47570382707264382677022761458457213500000000000)
      constant := (327363629405494475583526545071681265257466610407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127412343538378832637/50000000000000000000)
  centralHi := (10192987483070306611/4000000000000000000)
  directionLo := (64919731704771569957/25000000000000000000)
  directionHi := (259678926819086279829/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree028.table
  base := (-426795672194805088993462833998979177429/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303056694000000000000000000000000000000000000000
      center := (5455020492)
      previous := (2727510246)
      next := (2727510246)
      square := (18421901890636840300289861407615356000000000000)
      linear := (-532156978370270895206005184432870017800000000000)
      constant := (3778451338961352851505225544736062869956763920137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree028.table
  base := (-428085153311996326096932655453874479423/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303056694000000000000000000000000000000000000000
      center := (5455020492)
      previous := (2727510246)
      next := (2727510246)
      square := (18421901890636840300289861407615356000000000000)
      linear := (-532761796686646571216051753683155217800000000000)
      constant := (3786996661071705669205924025488322079787547296219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64919731704771569957/25000000000000000000)
  centralHi := (259678926819086279829/100000000000000000000)
  directionLo := (264444075229635784077/100000000000000000000)
  directionHi := (132222037614817892039/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree029.table
  base := (-1345006716691806082529583542190571865729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-1377842602910764648417487913657228574500000000000)
      constant := (10101573617239966097141167066902850200451378680037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree029.table
  base := (-673914624525170154454344276999030478861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-1379408650337094523800644209037431324500000000000)
      constant := (10124585339629627436263138892775031839871148454466) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264444075229635784077/100000000000000000000)
  centralHi := (132222037614817892039/50000000000000000000)
  directionLo := (134562432363384926821/50000000000000000000)
  directionHi := (269124864726769853643/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree030.table
  base := (-3199044914641384759100430762236340393987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (3030566940)
      previous := (1515283470)
      next := (1515283470)
      square := (10234389939242689055716589670897420000000000000)
      linear := (-316731724421300457515547303607173801000000000000)
      constant := (2396671998759349891859319754571959217974424572279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree030.table
  base := (-16019908075588574108982272429281239777/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5612161000000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (341146331308089635190552989029914000000000000)
      linear := (-10569724510796834218971548399014626700000000000)
      constant := (80072093950645720932964529078430127361837438060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134562432363384926821/50000000000000000000)
  centralHi := (269124864726769853643/100000000000000000000)
  directionLo := (8553925719755166339/3125000000000000000)
  directionHi := (273725623032165322849/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree031.table
  base := (-1832585018112469310108072213249168305727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-1472742916880939469222437818807335634500000000000)
      constant := (11496169055578169178712853168972087513258397056731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree031.table
  base := (-458685308426552287853930592414266938321/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-1474416967578050715321673858696517884500000000000)
      constant := (11522624009122395377791699085781327108477871658452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8553925719755166339/3125000000000000000)
  centralHi := (273725623032165322849/100000000000000000000)
  directionLo := (69562580006464313129/25000000000000000000)
  directionHi := (278250320025857252517/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree032.table
  base := (-4091852746302381673353038571542272776053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-3040386147732053759249825542764778329000000000000)
      constant := (24469492715106493114373041639328168773621587725609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree032.table
  base := (-163824637275197045212677056768878559829/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303056694000000000000000000000000000000000000000
      center := (5455020492)
      previous := (2727510246)
      next := (2727510246)
      square := (18421901890636840300289861407615356000000000000)
      linear := (-608768450479411524432875473410424465800000000000)
      constant := (4905199024437116974833622593627467395526855136685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69562580006464313129/25000000000000000000)
  centralHi := (278250320025857252517/100000000000000000000)
  directionLo := (141351303924510084511/50000000000000000000)
  directionHi := (282702607849020169023/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree033.table
  base := (-1120505404778325055601182441738010678781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-58060860401893121852866211998423803500000000000)
      constant := (481501259975389296351537857641828820251923488518) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree033.table
  base := (-4485302306837731156511783614560967250933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (3030566940)
      previous := (1515283470)
      next := (1515283470)
      square := (10234389939242689055716589670897420000000000000)
      linear := (-348761174404223757076156335190134321000000000000)
      constant := (2895696018946658937174162590981361710416109811361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141351303924510084511/50000000000000000000)
  centralHi := (282702607849020169023/100000000000000000000)
  directionLo := (71771463851755604353/25000000000000000000)
  directionHi := (287085855407022417413/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree034.table
  base := (-4838152613238619938527005483471246746243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-3230186775672403400859725353064992449000000000000)
      constant := (27586688903938916890575612303010848969512669749679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree034.table
  base := (-605126255108178892494081632955733841271/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-1616929443439485002603218333185147724500000000000)
      constant := (13825340561657453245252743759875553775440979963852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71771463851755604353/25000000000000000000)
  centralHi := (287085855407022417413/100000000000000000000)
  directionLo := (145701589099884807229/50000000000000000000)
  directionHi := (291403178199769614459/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree035.table
  base := (-2581169515174963872866230508893388473189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-1662543544821289110832337629107549754500000000000)
      constant := (14613019058184054936844151218948753734178817011417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree035.table
  base := (-1032965130476916323404825067408229893641/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303056694000000000000000000000000000000000000000
      center := (5455020492)
      previous := (2727510246)
      next := (2727510246)
      square := (18421901890636840300289861407615356000000000000)
      linear := (-665773440823985239345493263205876401800000000000)
      constant := (5858785962776621936477026041092894338020593458573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145701589099884807229/50000000000000000000)
  centralHi := (291403178199769614459/100000000000000000000)
  directionLo := (295657464230266961113/100000000000000000000)
  directionHi := (147828732115133480557/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree036.table
  base := (-2728175328733485802034236920661970986077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-63333100066902834119807873395651973500000000000)
      constant := (572571250056610305325528029025715093248807117603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree036.table
  base := (-5458512826636782751405402817044976378921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-126810204494847495861055406136609947000000000000)
      constant := (1147805296070935260806264903729786800320298341719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295657464230266961113/100000000000000000000)
  centralHi := (147828732115133480557/50000000000000000000)
  directionLo := (59970279320749037207/20000000000000000000)
  directionHi := (74962849150936296509/25000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree037.table
  base := (-2860841883384774893288072885336080205451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-1757443858791463931637287534257656814500000000000)
      constant := (16332445168177694906569436435078839947258589580503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree037.table
  base := (-1144712473377628402009343684235943842139/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303056694000000000000000000000000000000000000000
      center := (5455020492)
      previous := (2727510246)
      next := (2727510246)
      square := (18421901890636840300289861407615356000000000000)
      linear := (-703776767720367715953905123069511025800000000000)
      constant := (6548178952891343620613245636042654317215848385767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59970279320749037207/20000000000000000000)
  centralHi := (74962849150936296509/25000000000000000000)
  directionLo := (75996868329952169397/25000000000000000000)
  directionHi := (303987473319808677589/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree038.table
  base := (-2979801693531359707550002472301504534731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-1804894015776551342039762486832710344500000000000)
      constant := (17231987464269836079727850703170829200739207480343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree038.table
  base := (-2980617208024166201662247275965511361531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-1806946077921397385645277632503320844500000000000)
      constant := (17272097089067710672351752204784568590377488180743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75996868329952169397/25000000000000000000)
  centralHi := (303987473319808677589/100000000000000000000)
  directionLo := (308068024672321835387/100000000000000000000)
  directionHi := (77017006168080458847/25000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree039.table
  base := (-1234235808369853355481064392438660669257/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (606113388)
      previous := (303056694)
      next := (303056694)
      square := (2046877987848537811143317934179484000000000000)
      linear := (-82326407678295055664099441751456172200000000000)
      constant := (807020871477363303787770253290105355399285896869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree039.table
  base := (-6172594145191989923881798173888700705877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-137366684188287072696725367209841787000000000000)
      constant := (1348165919679227776336632332985823643557804629803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308068024672321835387/100000000000000000000)
  centralHi := (77017006168080458847/25000000000000000000)
  directionLo := (156047614300612745377/50000000000000000000)
  directionHi := (62419045720245098151/20000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree040.table
  base := (-6357314963994106200294158820987246333547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-3799588659493452325689424783965634809000000000000)
      constant := (38220646183269095803883818594617536514995812443191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree040.table
  base := (-6358541920061852754637230555918998509263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-3803908790324707154332614564324814809000000000000)
      constant := (38309615293135211408111494637534170449995913421739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156047614300612745377/50000000000000000000)
  centralHi := (62419045720245098151/20000000000000000000)
  directionLo := (39508890535429668833/12500000000000000000)
  directionHi := (63214224856687470133/20000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree041.table
  base := (-3259387820366436009956420371017821852541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-1947244486731813573247187344557870934500000000000)
      constant := (20088989993707897644652738992579903390393984520273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree041.table
  base := (-6519838800057916234878667896082154642183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-3898917107565663345853644213983901369000000000000)
      constant := (40271485241450755580200773312887220854871633538499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39508890535429668833/12500000000000000000)
  centralHi := (63214224856687470133/20000000000000000000)
  directionLo := (15999881210179421407/5000000000000000000)
  directionHi := (319997624203588428141/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree042.table
  base := (-3328103705381660133461214352821427167761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-73877579396922258653691196190108313500000000000)
      constant := (781256346116425444866283105223515420984751258479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree042.table
  base := (-832141011492362703075808408738247275981/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (5117194969621344527858294835448710000000000000)
      linear := (-221884745822589974298592992424610440500000000000)
      constant := (2349221788726445528721960982756217029152598340708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15999881210179421407/5000000000000000000)
  centralHi := (319997624203588428141/100000000000000000000)
  directionLo := (161938262453693988853/50000000000000000000)
  directionHi := (323876524907387977707/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree043.table
  base := (-1692539180895668654458441528145871069637/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-2042144800701988394052137249707977994500000000000)
      constant := (22125075744646799359757148428626189898635566999922) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree043.table
  base := (-3385476784342784212251247835795766509517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-2044466871023787864447851756651037244500000000000)
      constant := (22176526881495042734276099544601540837214929221601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161938262453693988853/50000000000000000000)
  centralHi := (323876524907387977707/100000000000000000000)
  directionLo := (81927379152298198457/25000000000000000000)
  directionHi := (327709516609192793829/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree044.table
  base := (-686108557691965877155767382439783437271/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151528347000000000000000000000000000000000000000
      center := (2727510246)
      previous := (1363755123)
      next := (1363755123)
      square := (9210950945318420150144930703807678000000000000)
      linear := (-417918991537415160890922440456606304900000000000)
      constant := (4636483637868351812299482312514513031312347178963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree044.table
  base := (-3430887434754971038062899969866429993701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-2091971029644265960208366581480580524500000000000)
      constant := (23236300145411469418595045020656507740263267057753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81927379152298198457/25000000000000000000)
  centralHi := (327709516609192793829/100000000000000000000)
  directionLo := (165749095899778371993/50000000000000000000)
  directionHi := (331498191799556743987/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree045.table
  base := (-1385876913676000871433715876981483433111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (682292662616179270381105978059828000000000000)
      linear := (-31659927624772788368253143034934593400000000000)
      constant := (359495097569238470827715565481937336454548337129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree045.table
  base := (-173249512928829842858509373326430409201/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5612161000000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (341146331308089635190552989029914000000000000)
      linear := (-15847964357516622636806528935630546700000000000)
      constant := (180165084845799400192588575315489881953072426556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165749095899778371993/50000000000000000000)
  centralHi := (331498191799556743987/100000000000000000000)
  directionLo := (335244052977111903619/100000000000000000000)
  directionHi := (16762202648855595181/5000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree046.table
  base := (-1743845982505084453467405936445031800909/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1432215000000000000000000000000000000000000000
      center := (25779870)
      previous := (12889935)
      next := (12889935)
      square := (87060027838548394613846225933910000000000000)
      linear := (-4129480664758507798222234607624080500000000000)
      constant := (47968910046566122893218982567473882011704446626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree046.table
  base := (-10899842064266806497309569840994402759/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 286443000000000000000000000000000000000000000
      center := (5155974)
      previous := (2577987)
      next := (2577987)
      square := (17412005567709678922769245186782000000000000)
      linear := (-826835291828061305001662091168116100000000000)
      constant := (9616053280201846976730825628668440178592240832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335244052977111903619/100000000000000000000)
  centralHi := (16762202648855595181/5000000000000000000)
  directionLo := (169474259805630597649/50000000000000000000)
  directionHi := (338948519611261195299/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree047.table
  base := (-6999362857580439225522174226390841371311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-4463890857284676071324074120016384229000000000000)
      constant := (53022600044873873182596035407057914386566030947083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree047.table
  base := (-3499903839271142872662053253664269816751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-2234483505505700247489911055969210364500000000000)
      constant := (26572802529349546641419757365899533635705728059403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169474259805630597649/50000000000000000000)
  centralHi := (338948519611261195299/100000000000000000000)
  directionLo := (342612934427190617139/100000000000000000000)
  directionHi := (17130646721359530857/5000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree048.table
  base := (-7001557397926676065536557183411203340319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (3030566940)
      previous := (1515283470)
      next := (1515283470)
      square := (10234389939242689055716589670897420000000000000)
      linear := (-506532352361650099125447113907387921000000000000)
      constant := (6149586894541829317034691520724021720951175941923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree048.table
  base := (-1400388287169897254494597592757493465623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (682292662616179270381105978059828000000000000)
      linear := (-33807224653721160640747050085907461400000000000)
      constant := (410922866459772851886200231509966707914475758697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342612934427190617139/100000000000000000000)
  centralHi := (17130646721359530857/5000000000000000000)
  directionLo := (34623856909211503977/10000000000000000000)
  directionHi := (346238569092115039771/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree049.table
  base := (-6982167117528242640040866377541189623637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-4653691485225025712933973930316598349000000000000)
      constant := (57722122607297536393544846376942329470416733261961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree049.table
  base := (-218203079195952443155559540109833645131/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-2329491822746656439010940705628296924500000000000)
      constant := (28927918769030785957694309401216988846933039544688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34623856909211503977/10000000000000000000)
  centralHi := (346238569092115039771/100000000000000000000)
  directionLo := (2798613034968288403/800000000000000000)
  directionHi := (43728328671379506297/12500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree050.table
  base := (-6941360740351687697247646923788972778019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-4748591799195200533738923835466705409000000000000)
      constant := (60150096147673340388182337312396203053118782995407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree050.table
  base := (-6941646626990825029962046915818069409773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-4753991962734269069542911060915680409000000000000)
      constant := (60289331352465726284716903862471363989605831664769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2798613034968288403/800000000000000000)
  centralHi := (43728328671379506297/12500000000000000000)
  directionLo := (353378259811275211277/100000000000000000000)
  directionHi := (176689129905637605639/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree051.table
  base := (-3439640457222551728964701169051016395929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-89694298391951395454516180381792823500000000000)
      constant := (1159818167718165660120508888371381601022406707431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree051.table
  base := (-214985232102274108716747826170024910271/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (5117194969621344527858294835448710000000000000)
      linear := (-269388904443068070059107817254153720500000000000)
      constant := (3487502607872523455658704437579962725818332529712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353378259811275211277/100000000000000000000)
  centralHi := (176689129905637605639/50000000000000000000)
  directionLo := (71378909601475428429/20000000000000000000)
  directionHi := (178447274003688571073/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree052.table
  base := (-679604824186872712902081935075519147049/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151528347000000000000000000000000000000000000000
      center := (2727510246)
      previous := (1363755123)
      next := (1363755123)
      square := (9210950945318420150144930703807678000000000000)
      linear := (-493839242713555017534882364576691952900000000000)
      constant := (6516235905998951963012556433871616107280815101997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree052.table
  base := (-6796260721930982836822114159510457902103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-4944008597216181452584970360233853529000000000000)
      constant := (65312966154682641037188667232441596272881244586259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71378909601475428429/20000000000000000000)
  centralHi := (178447274003688571073/50000000000000000000)
  directionLo := (360376528491430654279/100000000000000000000)
  directionHi := (9009413212285766357/2500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree053.table
  base := (-334588234290908521146579694797638145091/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151528347000000000000000000000000000000000000000
      center := (2727510246)
      previous := (1363755123)
      next := (1363755123)
      square := (9210950945318420150144930703807678000000000000)
      linear := (-503329274110572499615377355091702658900000000000)
      constant := (6774661470698457645860130980069826643190429210846) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree053.table
  base := (-6691947763838016741870592398107469164041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-5039016914457137644106000009892940089000000000000)
      constant := (67903073648716975130126620319003104441219395429773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360376528491430654279/100000000000000000000)
  centralHi := (9009413212285766357/2500000000000000000)
  directionLo := (363825186288250023109/100000000000000000000)
  directionHi := (36382518628825002311/10000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree054.table
  base := (-262660658047685146102252925706748919373/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (682292662616179270381105978059828000000000000)
      linear := (-37986615222784443088583136711608397400000000000)
      constant := (521355073594668989101593705657447527989513524735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree054.table
  base := (-6566674139536682014863767535326177987699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-190149082655484956875075172576000987000000000000)
      constant := (2612790979815595082048902313202823509618377192461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363825186288250023109/100000000000000000000)
  centralHi := (36382518628825002311/10000000000000000000)
  directionLo := (73448292034008451851/20000000000000000000)
  directionHi := (45905182521255282407/12500000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree055.table
  base := (-6420376419981179861947544447202906530751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-5223093369046074637763673361217240709000000000000)
      constant := (73071308701189172479877311561131746607299796301403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree055.table
  base := (-3210256096585649461272677514193046876711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-2614516774469525013574029654605556604500000000000)
      constant := (36619901805703156656655809684495082877878469373283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73448292034008451851/20000000000000000000)
  centralHi := (45905182521255282407/12500000000000000000)
  directionLo := (370626245641036109331/100000000000000000000)
  directionHi := (92656561410259027333/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree056.table
  base := (-1563351552569484279460870731406892573247/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-2658996841508124729284311633183673884500000000000)
      constant := (37905863333911717180587174879637472609938611334582) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree056.table
  base := (-1250704615076936299351950936907561207703/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303056694000000000000000000000000000000000000000
      center := (5455020492)
      previous := (2727510246)
      next := (2727510246)
      square := (18421901890636840300289861407615356000000000000)
      linear := (-1064808373236001243733817791774039953800000000000)
      constant := (15197281170363377965285320758509019395195440743059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370626245641036109331/100000000000000000000)
  centralHi := (92656561410259027333/25000000000000000000)
  directionLo := (93495099419740491329/25000000000000000000)
  directionHi := (373980397678961965317/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree057.table
  base := (-6065657917076080256540047380059070468149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (3030566940)
      previous := (1515283470)
      next := (1515283470)
      square := (10234389939242689055716589670897420000000000000)
      linear := (-601432666331824919930397019057494981000000000000)
      constant := (8733797882368313321285012799393063395567207320033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree057.table
  base := (-6065758475206565654005858585116176309219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-200705562348924533710745133649232827000000000000)
      constant := (2917968716440724549533026243804628418848277187741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93495099419740491329/25000000000000000000)
  centralHi := (373980397678961965317/100000000000000000000)
  directionLo := (377304733257163688391/100000000000000000000)
  directionHi := (47163091657145461049/12500000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree058.table
  base := (-1464293896009072920667845171527664320153/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-2753897155478299550089261538333780944500000000000)
      constant := (40724332423900115018691705528608060105092674245818) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree058.table
  base := (-2928631041990707121738505555418866171517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-2757029250330959300855574129094186444500000000000)
      constant := (40818022733588563841532877991059031312415810507601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377304733257163688391/100000000000000000000)
  centralHi := (47163091657145461049/12500000000000000000)
  directionLo := (380600033668422506013/100000000000000000000)
  directionHi := (190300016834211253007/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree059.table
  base := (-5627996447796900642654823832026403123917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-5602694624926773920983472981817668949000000000000)
      constant := (84345172744873410931077861995226623447777220824801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree059.table
  base := (-2814035416397394255861373666416116745507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-2804533408951437396616088953923729724500000000000)
      constant := (42269535312771618176095917743888781533394304613071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380600033668422506013/100000000000000000000)
  centralHi := (190300016834211253007/50000000000000000000)
  directionLo := (383867046669220159099/100000000000000000000)
  directionHi := (3838670466692201591/1000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree060.table
  base := (-5378151989981395469736638871171995580873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-211022034773961064510682329146954667000000000000)
      constant := (3233099994895407204042143584284953772108852203447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree060.table
  base := (-672276992305358732556122381383068528377/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (5117194969621344527858294835448710000000000000)
      linear := (-316893063063546165819622642083697000500000000000)
      constant := (4860790338264909157836517072473722080936582487636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383867046669220159099/100000000000000000000)
  centralHi := (3838670466692201591/1000000000000000000)
  directionLo := (387106488461113436481/100000000000000000000)
  directionHi := (193553244230556718241/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree061.table
  base := (-1021533765324473824241948975737397649839/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303056694000000000000000000000000000000000000000
      center := (5455020492)
      previous := (2727510246)
      next := (2727510246)
      square := (18421901890636840300289861407615356000000000000)
      linear := (-1158499050573424712518674558423576613800000000000)
      constant := (18058848433324911652524203555271368011338211513867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree061.table
  base := (-1021544757513516612890605037394190059393/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303056694000000000000000000000000000000000000000
      center := (5455020492)
      previous := (2727510246)
      next := (2727510246)
      square := (18421901890636840300289861407615356000000000000)
      linear := (-1159816690476957435254847441433126513800000000000)
      constant := (18100301571705655881527757287233860873696346886629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387106488461113436481/100000000000000000000)
  centralHi := (193553244230556718241/50000000000000000000)
  directionLo := (195159522762046544111/50000000000000000000)
  directionHi := (390319045524093088223/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree062.table
  base := (-4816569460128449074509015874349704557121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-5887395566837298383398322697267990129000000000000)
      constant := (93346796248466319351332798736845633421521087791013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree062.table
  base := (-2408308341998278114032325652392229507417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-2947045884812871683897633428412359564500000000000)
      constant := (46780456277580423896178219981929366031096477750301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195159522762046544111/50000000000000000000)
  centralHi := (390319045524093088223/100000000000000000000)
  directionLo := (196752688157610666957/50000000000000000000)
  directionHi := (78701075263044266783/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree063.table
  base := (-4504872915037575600624926057644090267887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-221566514103980489044565651941411007000000000000)
      constant := (3572272563886833009156492631443191903218085026193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree063.table
  base := (-4504913480453055902037576624394497683989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-221818521735803687382085055795696507000000000000)
      constant := (3580460641553484332086450563337159507483326609771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196752688157610666957/50000000000000000000)
  centralHi := (78701075263044266783/20000000000000000000)
  directionLo := (99166528211113419029/25000000000000000000)
  directionHi := (396666112844453676117/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree064.table
  base := (-4172595275516932470492151250815047981031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-6077196194777648025008222507568204249000000000000)
      constant := (99607928658851807721843566640392848032708685214243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree064.table
  base := (-2086315056263171280520091200085640139257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-3042054202053827875418663078071446124500000000000)
      constant := (49918039872092233909446513495131261619261536981821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99166528211113419029/25000000000000000000)
  centralHi := (396666112844453676117/100000000000000000000)
  directionLo := (199900931069163457357/50000000000000000000)
  directionHi := (79960372427665382943/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree065.table
  base := (-763950027958830945195423115477287369813/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303056694000000000000000000000000000000000000000
      center := (5455020492)
      previous := (2727510246)
      next := (2727510246)
      square := (18421901890636840300289861407615356000000000000)
      linear := (-1234419301749564569162634482543662261800000000000)
      constant := (20563300497934262621514860093777427833308258410889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree065.table
  base := (-3819780050024861888468253603610483089103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-6179116721348611942358355805801978809000000000000)
      constant := (103051837780824212168988776660838199725636768697259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199900931069163457357/50000000000000000000)
  centralHi := (79960372427665382943/20000000000000000000)
  directionLo := (201456603800557170179/50000000000000000000)
  directionHi := (402913207601114340359/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree066.table
  base := (-53849203193089471941467417787446332497/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (5117194969621344527858294835448710000000000000)
      linear := (-348166490150999870367673462103801020500000000000)
      constant := (5893171054186617285779683036758384096204061182368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree066.table
  base := (-430796834811866209804487759793295014467/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-116187500714621632108877508434464173500000000000)
      constant := (1968883513085746242451839083792431762633255467252) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201456603800557170179/50000000000000000000)
  centralHi := (402913207601114340359/100000000000000000000)
  directionLo := (16240028411283697759/4000000000000000000)
  directionHi := (50750088785261555497/12500000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree067.table
  base := (-190775099298777519413113628174944324753/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-3180948568344086243711536111509262714500000000000)
      constant := (54694828321562201450173934119471181069975173813672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree067.table
  base := (-3052423621709820051306889814189965730453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-6369133355830524325400415105120151929000000000000)
      constant := (109639694063328266458888028689104369696877809348809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16240028411283697759/4000000000000000000)
  centralHi := (50750088785261555497/12500000000000000000)
  directionLo := (409064910056715164909/100000000000000000000)
  directionHi := (40906491005671516491/10000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree068.table
  base := (-1318958055171190930678417536572801370457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-3228398725329173654114011064084316244500000000000)
      constant := (56377117123908160144139731878052985354175316155421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree068.table
  base := (-1318967507131208843401221270944061746533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-3232070836535740258460722377389619244500000000000)
      constant := (56505894809148353467487574698991715010081921529049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409064910056715164909/100000000000000000000)
  centralHi := (40906491005671516491/10000000000000000000)
  directionLo := (206053163364369008517/50000000000000000000)
  directionHi := (82421265345747603407/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree069.table
  base := (-137681219763231784542372692589790022843/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (954810)
      previous := (477405)
      next := (477405)
      square := (3224445475501792393105415775330000000000000)
      linear := (-229352998831776312015436954187451500000000000)
      constant := (4066751058487081006829487622572424091181268904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree069.table
  base := (-68841116624421889751924695681994449607/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 159135000000000000000000000000000000000000000
      center := (2864430)
      previous := (1432215)
      next := (1432215)
      square := (9673336426505377179316247325990000000000000)
      linear := (-688841628892295390510656837265104500000000000)
      constant := (12228102849154867627850487594653124602437728176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206053163364369008517/50000000000000000000)
  centralHi := (82421265345747603407/20000000000000000000)
  directionLo := (415125461059663591271/100000000000000000000)
  directionHi := (51890682632457948909/12500000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree070.table
  base := (-349471535948500814437640981894318203397/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303056694000000000000000000000000000000000000000
      center := (5455020492)
      previous := (2727510246)
      next := (2727510246)
      square := (18421901890636840300289861407615356000000000000)
      linear := (-1329319615719739389967584387693769321800000000000)
      constant := (23927877043984334902379788299606023134947242805241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree070.table
  base := (-436842896674315017306345230124849272733/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-3327079153776696449981752027048705804500000000000)
      constant := (59956155158369536161941096823916996912157232675298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415125461059663591271/100000000000000000000)
  centralHi := (51890682632457948909/12500000000000000000)
  directionLo := (104530698932820440833/25000000000000000000)
  directionHi := (418122795731281763333/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree071.table
  base := (-1271295566435269011723995102944423625859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-6741498392568871770642871843618953669000000000000)
      constant := (123159956944941392818349361349902014886605839274927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree071.table
  base := (-635653745436008483312467880775280309979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-3374583312397174545742266851878249084500000000000)
      constant := (61720366917589340063031827060959775118167234525287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104530698932820440833/25000000000000000000)
  centralHi := (418122795731281763333/100000000000000000000)
  directionLo := (210549398123271820997/50000000000000000000)
  directionHi := (84219759249308728399/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree072.table
  base := (-387358687124286633370571052966611881723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-126599976047019381323107810162390013500000000000)
      constant := (2346898616216507186846296694758143888495257566597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree072.table
  base := (-387363798379324968850112251394093009163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-126743980408061208944547469507696013500000000000)
      constant := (2352245652884952924303814410805070067583602768757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210549398123271820997/50000000000000000000)
  centralHi := (84219759249308728399/20000000000000000000)
  directionLo := (424053911773530253533/100000000000000000000)
  directionHi := (212026955886765126767/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree073.table
  base := (-51525330445160594271955836074825662477/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303056694000000000000000000000000000000000000000
      center := (5455020492)
      previous := (2727510246)
      next := (2727510246)
      square := (18421901890636840300289861407615356000000000000)
      linear := (-1386259804101844282450554330783833557800000000000)
      constant := (26071417934878196518752995581308496021951680264481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree073.table
  base := (-3220442675348348401475190025020874611/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151528347000000000000000000000000000000000000000
      center := (2727510246)
      previous := (1363755123)
      next := (1363755123)
      square := (9210950945318420150144930703807678000000000000)
      linear := (-693918325927626147452659300307467128900000000000)
      constant := (13065390404675080465053975508786746631037607215864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424053911773530253533/100000000000000000000)
  centralHi := (212026955886765126767/50000000000000000000)
  directionLo := (106747143984212138111/25000000000000000000)
  directionHi := (85397715187369710489/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree074.table
  base := (69993399802918389625399221550316069287/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-3513099667239698116528860779534637424500000000000)
      constant := (67016824843195643043077463456885335978113193157178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree074.table
  base := (69991522701081353370589749220856727261/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-3517095788258608833023811326366878924500000000000)
      constant := (67169324879278726966541967794309622463611378335134) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106747143984212138111/25000000000000000000)
  centralHi := (85397715187369710489/20000000000000000000)
  directionLo := (429903207560402816283/100000000000000000000)
  directionHi := (107475801890100704071/25000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree075.table
  base := (83808084347152919526685646590225455399/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16836483000000000000000000000000000000000000000
      center := (303056694)
      previous := (151528347)
      next := (151528347)
      square := (1023438993924268905571658967089742000000000000)
      linear := (-79123329427217456154029682935770910100000000000)
      constant := (1530691165859185069159388883327248252595992521717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree075.table
  base := (167614882066610930340959739231909792167/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (682292662616179270381105978059828000000000000)
      linear := (-52808888101912398944952980017724773400000000000)
      constant := (1022781496379736961118731894442568874091117742887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429903207560402816283/100000000000000000000)
  centralHi := (107475801890100704071/25000000000000000000)
  directionLo := (432798211365143799713/100000000000000000000)
  directionHi := (216399105682571899857/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree076.table
  base := (1416692936102187694844108646743574570713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-7215999962419745874667621369369488969000000000000)
      constant := (141542755072251890438523482917590042301571375501411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree076.table
  base := (708343712612324886133592143165665215533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-3612104105499565024544840976025965484500000000000)
      constant := (70932230241866392168590571081583503629265114213951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432798211365143799713/100000000000000000000)
  centralHi := (216399105682571899857/50000000000000000000)
  directionLo := (108918494656271700083/25000000000000000000)
  directionHi := (435673978625086800333/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree077.table
  base := (1007904032091965871181822638962391474493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-3655450138194960347736285637259798014500000000000)
      constant := (72687649923229130360130445885860276525546816953071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree077.table
  base := (2015803344168414700119312892789601237311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-7319216528240086240610711601711017529000000000000)
      constant := (145705524904527988951869199645275696882278890554917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108918494656271700083/25000000000000000000)
  centralHi := (435673978625086800333/100000000000000000000)
  directionLo := (43853088778460918429/10000000000000000000)
  directionHi := (438530887784609184291/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree078.table
  base := (1317712347543560675466272246711692357941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-137144455377038805856991132956846353500000000000)
      constant := (2764071092920535762206263702694172793595234520501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree078.table
  base := (2635420653119421524455728545941002671033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (3030566940)
      previous := (1515283470)
      next := (1515283470)
      square := (10234389939242689055716589670897420000000000000)
      linear := (-823802760609004714681304583485567121000000000000)
      constant := (16622077227136597598337162668268789218473801696939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43853088778460918429/10000000000000000000)
  centralHi := (438530887784609184291/100000000000000000000)
  directionLo := (44136930503978456339/10000000000000000000)
  directionHi := (441369305039784563391/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree079.table
  base := (3275541533149861864504736947388787256519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-7500700904330270337082471084819810149000000000000)
      constant := (153196372389674396587036732995060264102814989044093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree079.table
  base := (3275538072394793633591328171339648618533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-7509233162721998623652770901029190649000000000000)
      constant := (153543970708928721659503330717201822446727139054951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44136930503978456339/10000000000000000000)
  centralHi := (441369305039784563391/100000000000000000000)
  directionLo := (444189584886281746877/100000000000000000000)
  directionHi := (222094792443140873439/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree080.table
  base := (3936157483051191110460096712924106238673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-7595601218300445157887420989969917209000000000000)
      constant := (157184899796382482171489714579810825074798507163531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree080.table
  base := (3936154520408359884198492985784834798457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-7604241479962954815173800550688277209000000000000)
      constant := (157541351734735054123868265599959301234678267360579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444189584886281746877/100000000000000000000)
  centralHi := (222094792443140873439/50000000000000000000)
  directionLo := (223496035318074602413/50000000000000000000)
  directionHi := (446992070636149204827/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree081.table
  base := (2308635809422504508923207311206934988887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-142416695042048518123932794354074523500000000000)
      constant := (2985655946250483443660170624603148063224167054807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree081.table
  base := (4617269083016567437746530210282547157399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-285157399896441148396104822235087547000000000000)
      constant := (5984845851227026455399983513967620002137415529239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223496035318074602413/50000000000000000000)
  centralHi := (446992070636149204827/100000000000000000000)
  directionLo := (449777094905617779053/100000000000000000000)
  directionHi := (224888547452808889527/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree082.table
  base := (5318883157779893902142264108295928548451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-7785401846240794799497320800270131329000000000000)
      constant := (165317936174496238905759743187473198722776889440497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree082.table
  base := (1329720246901864489419043062329509738703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-3897129057222433599107929925003225164500000000000)
      constant := (82846214668520044628062751531211062364052135027882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449777094905617779053/100000000000000000000)
  centralHi := (224888547452808889527/50000000000000000000)
  directionLo := (5656812250948546667/1250000000000000000)
  directionHi := (452544980075883733361/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree083.table
  base := (6040991438165155422328908412408019555897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-7880302160210969620302270705420238389000000000000)
      constant := (169462444927027984483157867479527968622348746512259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree083.table
  base := (6040989581198841026130066347962693004861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-7889266431685823389736889499665536889000000000000)
      constant := (169846125697520867070388946211098225780695050294767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5656812250948546667/1250000000000000000)
  centralHi := (452544980075883733361/100000000000000000000)
  directionLo := (9105920774573583071/2000000000000000000)
  directionHi := (455296038728679153551/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree084.table
  base := (1695898975164446135417302974024936873079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (5117194969621344527858294835448710000000000000)
      linear := (-443066804121174691172623367253908080500000000000)
      constant := (9647719292798056729138930342660823409479335482314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree084.table
  base := (6783594311925344178520385644751429017949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-295713879589880725231774783308319387000000000000)
      constant := (6446367665961066669721910180833853392628801677789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9105920774573583071/2000000000000000000)
  centralHi := (455296038728679153551/100000000000000000000)
  directionLo := (229015287029147799967/50000000000000000000)
  directionHi := (91606114811659119987/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree085.table
  base := (7546696072441604969766281073838111167391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-8070102788151319261912170515720452509000000000000)
      constant := (177907443132862295201643946008775872883296998532677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree085.table
  base := (7546694713389996536881868351197979706691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-8079283066167735772778948798983710009000000000000)
      constant := (178309833116651526249488174234437984474694432069777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229015287029147799967/50000000000000000000)
  centralHi := (91606114811659119987/20000000000000000000)
  directionLo := (230374440130799185359/50000000000000000000)
  directionHi := (460748880261598370719/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree086.table
  base := (4165145776925819378685721337697437390661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-4082501551060747041358560210435279784500000000000)
      constant := (91103966226979616626073182824795177138442854567367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree086.table
  base := (8330290391437130786131162178461271997513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-8174291383408691964299978448642796569000000000000)
      constant := (182619844044903288842442235727323300053300533001011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230374440130799185359/50000000000000000000)
  centralHi := (460748880261598370719/100000000000000000000)
  directionLo := (463451242907451500997/100000000000000000000)
  directionHi := (231725621453725750499/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree087.table
  base := (1826876401413155848134195319388994085429/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (682292662616179270381105978059828000000000000)
      linear := (-61184469748827177063126446859412345400000000000)
      constant := (1381929001351601554616167610126555441735475302069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree087.table
  base := (9134381012971963765160485023117275701579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (3030566940)
      previous := (1515283470)
      next := (1515283470)
      square := (10234389939242689055716589670897420000000000000)
      linear := (-918811077849960906202334233144653681000000000000)
      constant := (20775773301692309552736406938911329111355947906657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463451242907451500997/100000000000000000000)
  centralHi := (231725621453725750499/50000000000000000000)
  directionLo := (466137939286866584171/100000000000000000000)
  directionHi := (116534484821716646043/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree088.table
  base := (1244870893318033617226605617621158329687/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-4177401865030921862163510115585386844500000000000)
      constant := (95482445637557928805373404680033667281691008549556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree088.table
  base := (1991793259302036267295493969815487018187/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303056694000000000000000000000000000000000000000
      center := (5455020492)
      previous := (2727510246)
      next := (2727510246)
      square := (18421901890636840300289861407615356000000000000)
      linear := (-1672861603578120869468407549592193937800000000000)
      constant := (38279236016996232963672301060195636425265835046889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466137939286866584171/100000000000000000000)
  centralHi := (116534484821716646043/25000000000000000000)
  directionLo := (468809238745090666981/100000000000000000000)
  directionHi := (234404619372545333491/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree089.table
  base := (2160809346189371646787028072449515719931/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303056694000000000000000000000000000000000000000
      center := (5455020492)
      previous := (2727510246)
      next := (2727510246)
      square := (18421901890636840300289861407615356000000000000)
      linear := (-1689940808806403709026394027264176149800000000000)
      constant := (39084272139067657475226300035049806221691659384057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree089.table
  base := (10804046004189850069366954949523570270343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-8459316335131560538863067397620056249000000000000)
      constant := (195862505118111599786663456798380102996603417913021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468809238745090666981/100000000000000000000)
  centralHi := (234404619372545333491/50000000000000000000)
  directionLo := (471465402996758949579/100000000000000000000)
  directionHi := (23573270149837947479/5000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree090.table
  base := (5834810278149633853566337637745028000319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-158233414037077654924757778545759033500000000000)
      constant := (3702404137263437292185542428650114476587298279359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree090.table
  base := (729351245938712140319651474605362127597/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-158413419488379939451557352727391533500000000000)
      constant := (3710758051558632771295395726986857769787015256936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471465402996758949579/100000000000000000000)
  centralHi := (23573270149837947479/5000000000000000000)
  directionLo := (118526671606289006499/25000000000000000000)
  directionHi := (474106686425156025997/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree091.table
  base := (6277844225107936059026324441167781730391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-4319752335986184093370934973310547434500000000000)
      constant := (102245139699828263988664786510421421646012947893677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree091.table
  base := (12555687919170384696835341224605116202227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-8649332969613472921905126696938229369000000000000)
      constant := (204951469057411053262960642016428458709866375028769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118526671606289006499/25000000000000000000)
  centralHi := (474106686425156025997/100000000000000000000)
  directionLo := (476733336366554219301/100000000000000000000)
  directionHi := (238366668183277109651/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree092.table
  base := (13462250267015364515179964264387493972661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2864430000000000000000000000000000000000000000
      center := (51559740)
      previous := (25779870)
      next := (25779870)
      square := (174120055677096789227692451867820000000000000)
      linear := (-16511162544314826101222721836996601000000000000)
      constant := (395279260180635505374101425358921708936010934823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree092.table
  base := (13462249813153477482142962882073493684499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2864430000000000000000000000000000000000000000
      center := (51559740)
      previous := (25779870)
      next := (25779870)
      square := (174120055677096789227692451867820000000000000)
      linear := (-16529945721842021008367025229862601000000000000)
      constant := (396170336325337518952716348539250689751468947057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476733336366554219301/100000000000000000000)
  centralHi := (238366668183277109651/50000000000000000000)
  directionLo := (479345593380528564781/100000000000000000000)
  directionHi := (239672796690264282391/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree093.table
  base := (719465294179569380170475009320922099487/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16836483000000000000000000000000000000000000000
      center := (303056694)
      previous := (151528347)
      next := (151528347)
      square := (1023438993924268905571658967089742000000000000)
      linear := (-98103392221252420315019663965792322100000000000)
      constant := (2375190790014116378317898487968642188994674368442) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree093.table
  base := (575572219829634136276081721807812639731/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (682292662616179270381105978059828000000000000)
      linear := (-65476663734039891147756933305602981400000000000)
      constant := (1587028528458327417675022981419076461160026843455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479345593380528564781/100000000000000000000)
  centralHi := (239672796690264282391/50000000000000000000)
  directionLo := (481943691507084604067/100000000000000000000)
  directionHi := (120485922876771151017/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree094.table
  base := (15336855195921449209377789117316345038207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-8924205613882892649156719662071416049000000000000)
      constant := (218483606781037046804612999062589900340721158553829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree094.table
  base := (1917106858064956545087084347103945082993/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-4467178960668170748234107822957744524500000000000)
      constant := (109487849659602281719655272249336535930418828410284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481943691507084604067/100000000000000000000)
  centralHi := (120485922876771151017/25000000000000000000)
  directionLo := (30282991156961053863/6250000000000000000)
  directionHi := (484527858511376861809/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree095.table
  base := (3260979623223094385825394730994472646809/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303056694000000000000000000000000000000000000000
      center := (5455020492)
      previous := (2727510246)
      next := (2727510246)
      square := (18421901890636840300289861407615356000000000000)
      linear := (-1803821185570613493992333913444304621800000000000)
      constant := (44650407132307612492836454812260525439807682594723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree095.table
  base := (8152448916489384037336944349460837409057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-4514683119288648843994622647787287804500000000000)
      constant := (111877325917492874377736823181328865023830170038779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30282991156961053863/6250000000000000000)
  centralHi := (484527858511376861809/100000000000000000000)
  directionLo := (48709831611674222429/10000000000000000000)
  directionHi := (487098316116742224291/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree096.table
  base := (270209915155008958007743792186652399607/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-168777893367097079458641101340215373500000000000)
      constant := (4223564032065224157215933598983266466164186263264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree096.table
  base := (17293434328046475410506516363856773764927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (3030566940)
      previous := (1515283470)
      next := (1515283470)
      square := (10234389939242689055716589670897420000000000000)
      linear := (-1013819395090917097723363882803740241000000000000)
      constant := (25398412097571702179107593989274729601928039431741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48709831611674222429/10000000000000000000)
  centralHi := (487098316116742224291/100000000000000000000)
  directionLo := (24482764011336150617/5000000000000000000)
  directionHi := (489655280226723012341/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree097.table
  base := (18302464494611562941367704978599085630493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-9208906555793417111571569377521737229000000000000)
      constant := (232944872981484528461730067932577421751800057085071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree097.table
  base := (18302464288009131464979018183478934800649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-9219382873059210071031304594892748729000000000000)
      constant := (233468870439331909712322111422610950167663117497203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24482764011336150617/5000000000000000000)
  centralHi := (489655280226723012341/100000000000000000000)
  directionLo := (24609948056835448283/5000000000000000000)
  directionHi := (492198961136708965661/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree098.table
  base := (386639756744150812946345967876071933697/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151528347000000000000000000000000000000000000000
      center := (2727510246)
      previous := (1363755123)
      next := (1363755123)
      square := (9210950945318420150144930703807678000000000000)
      linear := (-930380686976359193237651928267184428900000000000)
      constant := (23786928140339722615529762416471621007531000044295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree098.table
  base := (9665993830375992631668526256995406828837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-4657195595150083131276167122275917644500000000000)
      constant := (119202068255324328493506889399857503459366182542439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24609948056835448283/5000000000000000000)
  centralHi := (492198961136708965661/100000000000000000000)
  directionLo := (123682390933946323947/25000000000000000000)
  directionHi := (494729563735785295789/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree099.table
  base := (10191002276482096880975610741822884907599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-174050133032106791725582762737443543500000000000)
      constant := (4497142277601484552482783484057127693835915711439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree099.table
  base := (20382004402272254298505631532511449162823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-348496278057078609410124588674478587000000000000)
      constant := (9014500262423255279235028123145868735045077890503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123682390933946323947/25000000000000000000)
  centralHi := (494729563735785295789/100000000000000000000)
  directionLo := (497247287699335115979/100000000000000000000)
  directionHi := (24862364384966755799/5000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree100.table
  base := (21452514604099180993521100839021701658077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-9493607497703941573986419092972058409000000000000)
      constant := (247874077737008251776319644093063208699375567008719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree100.table
  base := (4290502895084467607870520612773941929511/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303056694000000000000000000000000000000000000000
      center := (5455020492)
      previous := (2727510246)
      next := (2727510246)
      square := (18421901890636840300289861407615356000000000000)
      linear := (-1900881564956415729118878708774001681800000000000)
      constant := (49686196431608140373163855188125032185252792348317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497247287699335115979/100000000000000000000)
  centralHi := (24862364384966755799/5000000000000000000)
  directionLo := (499752327672908643393/100000000000000000000)
  directionHi := (249876163836454321697/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree101.table
  base := (11271758979357288171046539780029827809021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-4794253905837058197395684499061082734500000000000)
      constant := (126477232819074021991273666290639520506845583818287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree101.table
  base := (5635879462211889297027961653007991383663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-4799708071011517418557711596764547484500000000000)
      constant := (126761280861867981120864353807704163106313394390122) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499752327672908643393/100000000000000000000)
  centralHi := (249876163836454321697/50000000000000000000)
  directionLo := (502244873447838343133/100000000000000000000)
  directionHi := (251122436723919171567/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree102.table
  base := (11827507294942957229206867916183464307257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (5117194969621344527858294835448710000000000000)
      linear := (-537967118091349511977573272404015140500000000000)
      constant := (14338158149434429040251234717339095850190239257131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree102.table
  base := (23655014496088317531071299185215984017691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-359052757750518186245794549747710427000000000000)
      constant := (9580231325129788707169611137414196866080708740251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502244873447838343133/100000000000000000000)
  centralHi := (251122436723919171567/50000000000000000000)
  directionLo := (126181277532262104819/25000000000000000000)
  directionHi := (504725110129048419277/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree103.table
  base := (12393502237446043160070552877023383973601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1285470)
      previous := (642735)
      next := (642735)
      square := (4341102340144415190001381234710000000000000)
      linear := (-460849676671433030276240400057610500000000000)
      constant := (12407918790111244976438969611968572743294943083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree103.table
  base := (1549187774676328421857724108440720603791/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1285470)
      previous := (642735)
      next := (642735)
      square := (4341102340144415190001381234710000000000000)
      linear := (-461373964393672693946530421945860500000000000)
      constant := (12435763706238244788703433461050124499071574824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126181277532262104819/25000000000000000000)
  centralHi := (504725110129048419277/100000000000000000000)
  directionLo := (253596609147739275203/50000000000000000000)
  directionHi := (507193218295478550407/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree104.table
  base := (20751590075651451227646391460044796849/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151528347000000000000000000000000000000000000000
      center := (2727510246)
      previous := (1363755123)
      next := (1363755123)
      square := (9210950945318420150144930703807678000000000000)
      linear := (-987320875358464085720621871357248664900000000000)
      constant := (26850758823152545031113324887074045188159972325375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree104.table
  base := (25939487526217853449165115071642189114357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-9884441093745903411678512142506354649000000000000)
      constant := (269109927342259256926864765617174238307959910177879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253596609147739275203/50000000000000000000)
  centralHi := (507193218295478550407/100000000000000000000)
  directionLo := (127412343538378832637/25000000000000000000)
  directionHi := (509649374153515330549/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree105.table
  base := (13556231966367899208613216174886301643013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-184594612362126216259466085531899883500000000000)
      constant := (5070295346596391806869943861495430255265153481093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree105.table
  base := (13556231937201180707523347312765020954993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (5117194969621344527858294835448710000000000000)
      linear := (-554413856165936644622196766231413400500000000000)
      constant := (15244995824777066977979084511177042448303383409619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127412343538378832637/25000000000000000000)
  centralHi := (509649374153515330549/100000000000000000000)
  directionLo := (512093749683800341883/100000000000000000000)
  directionHi := (128023437420950085471/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree106.table
  base := (5661186695155295560481477920298747367461/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303056694000000000000000000000000000000000000000
      center := (5455020492)
      previous := (2727510246)
      next := (2727510246)
      square := (18421901890636840300289861407615356000000000000)
      linear := (-2012601876304998099763223704774540153800000000000)
      constant := (55827260468110835395179142424045399726561966916967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree106.table
  base := (7076483356498408244250791872778867016237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-5037228864113907897360285720912263884500000000000)
      constant := (139881013414059650536294539408148986723006429540478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512093749683800341883/100000000000000000000)
  centralHi := (128023437420950085471/25000000000000000000)
  directionLo := (514526512781760999561/100000000000000000000)
  directionHi := (257263256390880499781/50000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree107.table
  base := (29519896212199741683257681949049156201203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-10157909695495165319621068429022807829000000000000)
      constant := (284528649102831961423154700547190623706413090001441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree107.table
  base := (7379974042429478250071052377981114390709/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-5084733022734385993120800545741807164500000000000)
      constant := (142583116643473624926854979792681595175684093856046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514526512781760999561/100000000000000000000)
  centralHi := (257263256390880499781/50000000000000000000)
  directionLo := (1033895654784378263/200000000000000000)
  directionHi := (516947827392189131501/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree108.table
  base := (30754352132329976206778227107103297037941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-379733704054271857052815493858256107000000000000)
      constant := (10739740333391569671829580810015934392607748000501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree108.table
  base := (7688588024020395696847156339078315043409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-190082858568698669958567235947087053500000000000)
      constant := (5381898967056157399976028043504709639264666593698) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1033895654784378263/200000000000000000)
  centralHi := (516947827392189131501/100000000000000000000)
  directionLo := (64919731704771569957/12500000000000000000)
  directionHi := (519357853638172559657/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree109.table
  base := (32009301228021537707914092047258693211497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-10347710323435514961230968239323021949000000000000)
      constant := (295469322035541140204810860423957041212218261805459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree109.table
  base := (32009301197094587968128558929693088313191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-10359482679950684369283660390801787449000000000000)
      constant := (296130959629164330576421051194484449325422850525277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64919731704771569957/12500000000000000000)
  centralHi := (519357853638172559657/100000000000000000000)
  directionLo := (52175674794466661767/10000000000000000000)
  directionHi := (521756747944666617671/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree110.table
  base := (2080296468276325245528407762906361588401/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-5221305318702844891017959072236564504500000000000)
      constant := (150508824101849890589490476847135801780697583225176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree110.table
  base := (6656948693207340880628411386168535242811/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303056694000000000000000000000000000000000000000
      center := (5455020492)
      previous := (2727510246)
      next := (2727510246)
      square := (18421901890636840300289861407615356000000000000)
      linear := (-2090898199438328112160938008092174801800000000000)
      constant := (60338295902064887666309911140525665056754394463417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52175674794466661767/10000000000000000000)
  centralHi := (521756747944666617671/100000000000000000000)
  directionLo := (2047440090456935417/390625000000000000)
  directionHi := (524144663156975466753/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree111.table
  base := (270161554060682667129540421144641779483/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (5117194969621344527858294835448710000000000000)
      linear := (-585417275076436922380048224979068670500000000000)
      constant := (17034331528065292184801790149019463490876737810496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree111.table
  base := (34580678897260011891630891763110652684881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-390722196830836916752804432967405947000000000000)
      constant := (11381633476431740846373191272793910495682634437841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2047440090456935417/390625000000000000)
  centralHi := (524144663156975466753/100000000000000000000)
  directionLo := (52652174865439716019/10000000000000000000)
  directionHi := (526521748654397160191/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree112.table
  base := (8974276876305096579756941330141025948679/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-5316205632673019711822908977386671564500000000000)
      constant := (156135139969617112681893339522661274841774871407226) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree112.table
  base := (717942149720439428715642329154107933337/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151528347000000000000000000000000000000000000000
      center := (2727510246)
      previous := (1363755123)
      next := (1363755123)
      square := (9210950945318420150144930703807678000000000000)
      linear := (-1064450763167355294384674933977904712900000000000)
      constant := (31296883268844339504307924471352656869790709019695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52652174865439716019/10000000000000000000)
  centralHi := (526521748654397160191/100000000000000000000)
  directionLo := (105777630091854313631/20000000000000000000)
  directionHi := (132222037614817892039/25000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree113.table
  base := (37234029244718994791412989994403140170709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-10727311579316214244450767859923450189000000000000)
      constant := (317974585505261288744198196891418821756176832588023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree113.table
  base := (3723402922834436902982962995766301992637/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151528347000000000000000000000000000000000000000
      center := (2727510246)
      previous := (1363755123)
      next := (1363755123)
      square := (9210950945318420150144930703807678000000000000)
      linear := (-1073951594891450913536777898943813368900000000000)
      constant := (31868566598408080271225281098510459040447090781039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105777630091854313631/20000000000000000000)
  centralHi := (132222037614817892039/25000000000000000000)
  directionLo := (531244011341656427309/100000000000000000000)
  directionHi := (53124401134165642731/10000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree114.table
  base := (4823930516857400062345626150109586685797/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-200411331357155353060291069723584393500000000000)
      constant := (5995016374124826778114586028421534148996596709268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree114.table
  base := (9647861030223530493250092491415672004869/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (5117194969621344527858294835448710000000000000)
      linear := (-601918014786414740382711591060956680500000000000)
      constant := (18025255763892453852640801412673811107287105671454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531244011341656427309/100000000000000000000)
  centralHi := (53124401134165642731/10000000000000000000)
  directionLo := (133397367729960962411/25000000000000000000)
  directionHi := (106717894183968769929/20000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree115.table
  base := (1249042255399742068056328868610494468807/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1432215000000000000000000000000000000000000000
      center := (25779870)
      previous := (12889935)
      next := (12889935)
      square := (87060027838548394613846225933910000000000000)
      linear := (-10318631575856865676805924073935410500000000000)
      constant := (311473701352779351552431253232498822624055736016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree115.table
  base := (19984676080441281657170825343092767625749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1432215000000000000000000000000000000000000000
      center := (25779870)
      previous := (12889935)
      next := (12889935)
      square := (87060027838548394613846225933910000000000000)
      linear := (-10330371061811362493771113694476660500000000000)
      constant := (312169797718309010260408976832507791637022420807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133397367729960962411/25000000000000000000)
  centralHi := (106717894183968769929/20000000000000000000)
  directionLo := (66990583219614692977/12500000000000000000)
  directionHi := (535924665756917543817/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree116.table
  base := (41367753356135525674969585655359791243379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-11012012521226738706865617575373771369000000000000)
      constant := (335399460990400207437572197055982467631374294564513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree116.table
  base := (20683876672990171886501909264037308277789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-5512270450318688854965433969207696684500000000000)
      constant := (168074396345724065395037420201453947781662783984783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66990583219614692977/12500000000000000000)
  centralHi := (535924665756917543817/100000000000000000000)
  directionLo := (107649945890707941457/20000000000000000000)
  directionHi := (269124864726769853643/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree117.table
  base := (42786647682904402296005102260316808392351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-411367142044330130654465462241625127000000000000)
      constant := (12641175521478468536788518933584611201204024980511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree117.table
  base := (21393323837122766587011439601870035312577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-205917578108858035212072177556934813500000000000)
      constant := (6334704516040768623737391469102900401249867448897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107649945890707941457/20000000000000000000)
  centralHi := (269124864726769853643/50000000000000000000)
  directionLo := (540564792737145981419/100000000000000000000)
  directionHi := (27028239636857299071/5000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree118.table
  base := (11056508787861342125690477091586513988117/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-5600906574583544174237758692836992744500000000000)
      constant := (173638005149772702804895864490110735672723493305198) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree118.table
  base := (44226035144062877635899496438176230849359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-11214557535119290092972927237733566489000000000000)
      constant := (348051399509986300780096665967390675787293775279573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540564792737145981419/100000000000000000000)
  centralHi := (27028239636857299071/5000000000000000000)
  directionLo := (33929373971732310717/6250000000000000000)
  directionHi := (542869983547716971473/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree119.table
  base := (45685915760386292770392921397737887803761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-11296713463137263169280467290824092549000000000000)
      constant := (353292274649072555965250682525823589341675364713067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree119.table
  base := (45685915754092485041129101457312852959323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-11309565852360246284493956887392653049000000000000)
      constant := (354080859622599484447183623239127377346780272429081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33929373971732310717/6250000000000000000)
  centralHi := (542869983547716971473/100000000000000000000)
  directionLo := (136291356780071392617/25000000000000000000)
  directionHi := (545165427120285570469/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree120.table
  base := (47166289508591770595562620030991993137551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (3030566940)
      previous := (1515283470)
      next := (1515283470)
      square := (10234389939242689055716589670897420000000000000)
      linear := (-1265734864123048665565046355108244401000000000000)
      constant := (39928948014258672843566676034561955785596494073133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree120.table
  base := (368486636743956864634658134262670084043/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-211195817955577823629907158093550733500000000000)
      constant := (6669674522293947813991716631039923651298102203072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136291356780071392617/25000000000000000000)
  centralHi := (545165427120285570469/100000000000000000000)
  directionLo := (8553925719755166339/1562500000000000000)
  directionHi := (547451246064330645697/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree121.table
  base := (48667156395125825910070703528877280177443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-11486514091077612810890367101124306669000000000000)
      constant := (365480782737170077583893983500308000837643804476721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree121.table
  base := (48667156390552384886574670233684079500893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-11499582486842158667536016186710826169000000000000)
      constant := (366296093253669127681998051167861157330986901313871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8553925719755166339/1562500000000000000)
  centralHi := (547451246064330645697/100000000000000000000)
  directionLo := (137431890110049876933/25000000000000000000)
  directionHi := (549727560440199507733/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree122.table
  base := (12547129104805100745520688321260310417321/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-5790707202523893815847658503137206864500000000000)
      constant := (185826513237741119862591817682224073259987062596774) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree122.table
  base := (25094258207661105844625182645105361637939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-5797295402041557429528522918184956364500000000000)
      constant := (186240933385936989818209371881352060373834109156833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137431890110049876933/25000000000000000000)
  centralHi := (549727560440199507733/100000000000000000000)
  directionLo := (551994487832693946453/100000000000000000000)
  directionHi := (275997243916346973227/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree123.table
  base := (25865184790124376377895622358499474103299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-216228050352184489861116053915268903500000000000)
      constant := (6997727098947584662362198425061708011333044619139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree123.table
  base := (25865184788463168287839996710816260347409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (5117194969621344527858294835448710000000000000)
      linear := (-649422173406892836143226415890499960500000000000)
      constant := (21039985819910853484902763063917242697462725722547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551994487832693946453/100000000000000000000)
  centralHi := (275997243916346973227/50000000000000000000)
  directionLo := (2165047435241982233/390625000000000000)
  directionHi := (554252143421947451649/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree124.table
  base := (13323178969425739030023747169425751367631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-5885607516494068636652608408287313924500000000000)
      constant := (192076746670077554783852174862886913760940229471914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree124.table
  base := (53292715874871458417018085430638866453589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-11784607438565027242099105135688085849000000000000)
      constant := (385009727213158527852863837365372007883666093387383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2165047435241982233/390625000000000000)
  centralHi := (554252143421947451649/100000000000000000000)
  directionLo := (556500640051714505033/100000000000000000000)
  directionHi := (278250320025857252517/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree125.table
  base := (54875555311174943722489021487537416336917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-11866115346958312094110166721724734909000000000000)
      constant := (390481716466377019051174102226105681610683828086199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree125.table
  base := (54875555308761983570840520299807444470771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-11879615755805983433620134785347172409000000000000)
      constant := (391351814136103531359540814276591076978950219445537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556500640051714505033/100000000000000000000)
  centralHi := (278250320025857252517/50000000000000000000)
  directionLo := (34921255518449156627/6250000000000000000)
  directionHi := (558740088295186506033/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree126.table
  base := (56478887880340470965486306030396508399951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-443000580034388404256115430624994147000000000000)
      constant := (14698590100806895110003225235785061305978377404111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree126.table
  base := (56478887878284313873778532276484819415407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-443504595298034800931154238333565147000000000000)
      constant := (14731333538043809416183820772527325552615189964527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34921255518449156627/6250000000000000000)
  centralHi := (558740088295186506033/100000000000000000000)
  directionLo := (22438823860737717919/4000000000000000000)
  directionHi := (70121324564805368497/12500000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree127.table
  base := (58102713584945590537720809726260836152773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-12055915974898661735720066532024949029000000000000)
      constant := (403294142106344076108126897917248256668567532156231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree127.table
  base := (58102713583193586594373269167822070927119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-12069632390287895816662194084665345529000000000000)
      constant := (404192301386359392840191012339012424585703099542293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22438823860737717919/4000000000000000000)
  centralHi := (70121324564805368497/12500000000000000000)
  directionLo := (563192270941640868863/100000000000000000000)
  directionHi := (549992452091446161/97656250000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree128.table
  base := (59747032424795235606122337115658522884899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-12150816288868836556525016437175056089000000000000)
      constant := (409778344620021185310523900226319806861210416731953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree128.table
  base := (29873516211651243041504849668877515041377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-6082320353764426004091611867162216044500000000000)
      constant := (205345350856802381769235485894374735935687493413819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563192270941640868863/100000000000000000000)
  centralHi := (549992452091446161/97656250000000000)
  directionLo := (141351303924510084511/25000000000000000000)
  directionHi := (113081043139608067609/20000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree129.table
  base := (30705922199871793314648387424603677159771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (5117194969621344527858294835448710000000000000)
      linear := (-680317589046611743184998130129175730500000000000)
      constant := (23128585570155299987956130012336043635487972725393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree129.table
  base := (61411844398471805734885806702278796986873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-454061074991474377766824199406796987000000000000)
      constant := (15453378018848069355003181757332305783576646162553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141351303924510084511/25000000000000000000)
  centralHi := (113081043139608067609/20000000000000000000)
  directionLo := (567609532890958785041/100000000000000000000)
  directionHi := (283804766445479392521/50000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree130.table
  base := (31548574754842972668231833252531025660299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-6170308458404593099067458123737635104500000000000)
      constant := (211451364517325427385140548471463721282019690995753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree130.table
  base := (31548574754301244324359744933693617397371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-6177328671005382195612641516821302604500000000000)
      constant := (211921907886111855025762800155880315908674069775737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (567609532890958785041/100000000000000000000)
  centralHi := (283804766445479392521/50000000000000000000)
  directionLo := (569805322648742309301/100000000000000000000)
  directionHi := (284902661324371154651/50000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree131.table
  base := (64802947754551882180624974655538309101993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-12435517230779361018939866152625377269000000000000)
      constant := (429542910935576878198899598965294643494900053695571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree131.table
  base := (12960589550725783485664721902564419702949/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303056694000000000000000000000000000000000000000
      center := (5455020492)
      previous := (2727510246)
      next := (2727510246)
      square := (18421901890636840300289861407615356000000000000)
      linear := (-2489933131850344116549262536660338353800000000000)
      constant := (86099705900714466608442273811251432675402092995303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569805322648742309301/100000000000000000000)
  centralHi := (284902661324371154651/50000000000000000000)
  directionLo := (142998170794459427723/25000000000000000000)
  directionHi := (571992683177837710893/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree132.table
  base := (66529239134299459727739880648125142274607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-464089538694427253323882076213906827000000000000)
      constant := (16156855035761745013296600722526245600593000695727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree132.table
  base := (13305847826702651825629719479138212586709/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33672966000000000000000000000000000000000000000
      center := (606113388)
      previous := (303056694)
      next := (303056694)
      square := (2046877987848537811143317934179484000000000000)
      linear := (-278770532810948372761496496288017296200000000000)
      constant := (9715674393398622417632043257756726273266512104447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (142998170794459427723/25000000000000000000)
  centralHi := (571992683177837710893/100000000000000000000)
  directionLo := (71771463851755604353/12500000000000000000)
  directionHi := (22966868432561793393/4000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree133.table
  base := (68276023648910365007430551616560347677467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-12625317858719710660549765962925591389000000000000)
      constant := (442979254124618791316476945592002422013811863657049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree133.table
  base := (17069005912060175348711291820198037672709/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-6319841146866816482894185991309932444500000000000)
      constant := (221982135185159246406899567841648589868378643564046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71771463851755604353/12500000000000000000)
  centralHi := (22966868432561793393/4000000000000000000)
  directionLo := (576342500072024909507/100000000000000000000)
  directionHi := (144085625018006227377/25000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree134.table
  base := (17510825324596452422269606443648586812397/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-6360109086344942740677357934037849224500000000000)
      constant := (224887707706366044836782128530844124997637033035518) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree134.table
  base := (70043301297815441256397963518340269842643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-12734690610974589157309401632278951449000000000000)
      constant := (450775297505714421071995762208761609808789643901121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (576342500072024909507/100000000000000000000)
  centralHi := (144085625018006227377/25000000000000000000)
  directionLo := (289252571846568433983/50000000000000000000)
  directionHi := (578505143693136867967/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree135.table
  base := (35915536041371539395249644970749932658223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-237317009012223338928882699504181583500000000000)
      constant := (8455992033887215362971252697120275904067105449903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree135.table
  base := (8978884010282163684777770895989487707063/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-237587017189176765719082060776630333500000000000)
      constant := (8474785724243125897983980246853887247278233572572) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289252571846568433983/50000000000000000000)
  centralHi := (578505143693136867967/100000000000000000000)
  directionLo := (290329866345835077361/50000000000000000000)
  directionHi := (580659732691670154723/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree136.table
  base := (9204917000251578386528551180773841268917/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-6455009400315117561482307839187956284500000000000)
      constant := (231761858688078012929839933935459546095277501960796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree136.table
  base := (18409834000399732887555214552071038611349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-6462353622728250770175730465798562284500000000000)
      constant := (232276832590283284378885863973366578166701778820206) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290329866345835077361/50000000000000000000)
  centralHi := (580659732691670154723/100000000000000000000)
  directionLo := (582806356399539228917/100000000000000000000)
  directionHi := (291403178199769614459/50000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree137.table
  base := (37734046528117819020441012728872196860837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-6502459557300204971884782791763009814500000000000)
      constant := (235237929025738759455425222754332241959831219646439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree137.table
  base := (75468093055883341704449742674525474414599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-13019715562697457731872490581256211129000000000000)
      constant := (471521005720034252777953961606045008775434979137853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (582806356399539228917/100000000000000000000)
  centralHi := (291403178199769614459/50000000000000000000)
  directionLo := (146236275627375465777/25000000000000000000)
  directionHi := (584945102509501863109/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree138.table
  base := (77317343245461973121474939933538585350919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318270000000000000000000000000000000000000000
      center := (5728860)
      previous := (2864430)
      next := (2864430)
      square := (19346672853010754358632494651980000000000000)
      linear := (-2751484862123626289555663828749449000000000000)
      constant := (100289853361873905520345019275123899555963699013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree138.table
  base := (15463468649032395864885897904638625982987/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (381924)
      previous := (190962)
      next := (190962)
      square := (1289778190200716957242166310132000000000000)
      linear := (-183641026114099473827536515170696600000000000)
      constant := (6700839469684795142147129038932523983053509083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146236275627375465777/25000000000000000000)
  centralHi := (584945102509501863109/100000000000000000000)
  directionLo := (293538028558480198043/50000000000000000000)
  directionHi := (587076057116960396087/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree139.table
  base := (3959354328487422541706564553212797370583/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151528347000000000000000000000000000000000000000
      center := (2727510246)
      previous := (1363755123)
      next := (1363755123)
      square := (9210950945318420150144930703807678000000000000)
      linear := (-1319471974254075958537946539382623374900000000000)
      constant := (48453611878937707128761927160635400938970776832602) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree139.table
  base := (79187086569493008061722102813252846798513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-13209732197179370114914549880574384249000000000000)
      constant := (485612000203091559095198178517759097724422916948011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293538028558480198043/50000000000000000000)
  centralHi := (587076057116960396087/100000000000000000000)
  directionLo := (589199304760402316477/100000000000000000000)
  directionHi := (294599652380201158239/50000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree140.table
  base := (20269330757289350960203931209901515898689/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-6644810028255467203092207649488170404500000000000)
      constant := (245822119425986592695925981300196363478845127274166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree140.table
  base := (20269330757234976808431972959615722531819/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-6652370257210163153217789765116735404500000000000)
      constant := (246367827073349806875135596708897814260914375946386) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (589199304760402316477/100000000000000000000)
  centralHi := (294599652380201158239/50000000000000000000)
  directionLo := (295657464230266961113/50000000000000000000)
  directionHi := (591314928460533922227/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree141.table
  base := (41494026311877735409630424971736617710281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-247861488342242763462766022298637923500000000000)
      constant := (9237117630438520447106366623200886522935548327241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree141.table
  base := (41494026311785146450642992677431108780677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84182415000000000000000000000000000000000000000
      center := (1515283470)
      previous := (757641735)
      next := (757641735)
      square := (5117194969621344527858294835448710000000000000)
      linear := (-744430490647849027664256065549586520500000000000)
      constant := (27772856253243003043976992757155474564657019038991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295657464230266961113/50000000000000000000)
  centralHi := (591314928460533922227/100000000000000000000)
  directionLo := (593423009758158310023/100000000000000000000)
  directionHi := (74177876219769788753/12500000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree142.table
  base := (84919275353612586299673709020230126878859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-13479420684451284047794315109276554929000000000000)
      constant := (506016458364508424607055271503379743858553773516073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree142.table
  base := (84919275353454932637473436439668438104863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-13494757148902238689477638829551643929000000000000)
      constant := (507139275438125605512511774707189886302101703051461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (593423009758158310023/100000000000000000000)
  centralHi := (74177876219769788753/12500000000000000000)
  directionLo := (595523628750846590069/100000000000000000000)
  directionHi := (59552362875084659007/10000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree143.table
  base := (10858873902350142181964229852469826772023/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-6787160499210729434299632507213330994500000000000)
      constant := (256640278907234557745277507848241847482313964143924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree143.table
  base := (10858873902333365448444729390283525754839/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-6794882733071597440499334239605365244500000000000)
      constant := (257209621392982671101320862721398151041850723684532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (595523628750846590069/100000000000000000000)
  centralHi := (59552362875084659007/10000000000000000000)
  directionLo := (597616864128448987199/100000000000000000000)
  directionHi := (373510540080280617/62500000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree144.table
  base := (88843200219395261635825569823918892003121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-506267456014504951459415367391732187000000000000)
      constant := (19281357421984200396448287505614730160863127554481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree144.table
  base := (88843200219281008142903882884194838948091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-506843473458672261945174004772956187000000000000)
      constant := (19324122763033503350110742300935666079545757334651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (597616864128448987199/100000000000000000000)
  centralHi := (373510540080280617/62500000000000000)
  directionLo := (599702793207490372071/100000000000000000000)
  directionHi := (74962849150936296509/12500000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree145.table
  base := (45417951177735131245270696659416567562557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-6882060813180904255104582412363438054500000000000)
      constant := (263982368050916360442694883221549899588418081303279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree145.table
  base := (90835902355373005542770101800237270466311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-13779782100625107264040727778528903609000000000000)
      constant := (529135490885954839027552366110245709981552025017917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (599702793207490372071/100000000000000000000)
  centralHi := (74962849150936296509/12500000000000000000)
  directionLo := (601781491964492758817/100000000000000000000)
  directionHi := (300890745982246379409/50000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree146.table
  base := (92849097627102125991052673874867728301539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-13859021940331983331014114729876983169000000000000)
      constant := (535384814939258560063022844165011932932177322226033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree146.table
  base := (46424548813509670545312585691582903872653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-6937395208933031727780878714093995084500000000000)
      constant := (268285885819063834263116139885293664809283007594591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (601781491964492758817/100000000000000000000)
  centralHi := (300890745982246379409/50000000000000000000)
  directionLo := (4717601836470823453/781250000000000000)
  directionHi := (120770607013653080397/20000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree147.table
  base := (94882786034367120541562452457663213872991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (3030566940)
      previous := (1515283470)
      next := (1515283470)
      square := (10234389939242689055716589670897420000000000000)
      linear := (-1550435806033573127979896070558565581000000000000)
      constant := (60317431878429165006913356718581212309597977130653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree147.table
  base := (94882786034296657521603220578186733878511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-517399953152111838780843965846188027000000000000)
      constant := (20150376179942025647999785795875548322590358172271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4717601836470823453/781250000000000000)
  centralHi := (120770607013653080397/20000000000000000000)
  directionLo := (605917495911201319599/100000000000000000000)
  directionHi := (1514793739778003299/250000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree148.table
  base := (96936967577341467845031333489860165904009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-14048822568272332972624014540177197289000000000000)
      constant := (550380952001656045631637010744040348302580244443123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree148.table
  base := (96936967577281495465926581352450292505953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-14064807052347975838603816727506163289000000000000)
      constant := (551600646546887509012014104469870669975093545749691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605917495911201319599/100000000000000000000)
  centralHi := (1514793739778003299/250000000000000000)
  directionLo := (75996868329952169397/12500000000000000000)
  directionHi := (607974946639617355177/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree149.table
  base := (99011642256101073258512022332082901256817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-14143722882242507793428964445327304349000000000000)
      constant := (557957010226650743584555886230613687102909702491499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree149.table
  base := (99011642256050031987952230114709764739569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-14159815369588932030124846377165249849000000000000)
      constant := (559193240703497661058933268967416306431745776062443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75996868329952169397/12500000000000000000)
  centralHi := (607974946639617355177/100000000000000000000)
  directionLo := (305012729091586632121/50000000000000000000)
  directionHi := (610025458183173264243/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree150.table
  base := (20221362014144261225838140498981688990193/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (682292662616179270381105978059828000000000000)
      linear := (-105471282934908760105436402596128973400000000000)
      constant := (4189518974673022218619040210485535709664890537073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree150.table
  base := (101106810070677867899757951072328788149791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (3030566940)
      previous := (1515283470)
      next := (1515283470)
      square := (10234389939242689055716589670897420000000000000)
      linear := (-1583869298536654246849541780758259601000000000000)
      constant := (62981993258697400478093079361960136812094557625053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (305012729091586632121/50000000000000000000)
  centralHi := (610025458183173264243/100000000000000000000)
  directionLo := (24482764011336150617/4000000000000000000)
  directionHi := (306034550141701882713/50000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree151.table
  base := (103222471021276822085266220038907969197211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-14333523510182857435038864255627518469000000000000)
      constant := (573265106064289125862615855029707061009080299840217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree151.table
  base := (51611235510619928000371020584138623501273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-7174916002035422206583452838241711484500000000000)
      constant := (287267371210617840532344293435464412220003250085731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24482764011336150617/4000000000000000000)
  centralHi := (306034550141701882713/50000000000000000000)
  directionLo := (76763242690174503477/12500000000000000000)
  directionHi := (614105941521396027817/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree152.table
  base := (52679312553920710254480795443566865875069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-7214211912076516127921907080388812764500000000000)
      constant := (290498571838477652665045020430633847764019914080943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree152.table
  base := (105358625107809963621868898018274902467659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-14444840321311800604687935326142509529000000000000)
      constant := (582283649982386099491878923893839842450510589229673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76763242690174503477/12500000000000000000)
  centralHi := (614105941521396027817/100000000000000000000)
  directionLo := (308068024672321835387/50000000000000000000)
  directionHi := (24645441973785746831/4000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree153.table
  base := (3359852260327747858682335261598098748367/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-268950447002281612530532667887550603500000000000)
      constant := (10903355081830880995134392931743125521265745457392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree153.table
  base := (53757636165230581944931075173121297533893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-269256456269495496226091943996325853500000000000)
      constant := (10927493740958128094105121820606513512289110472773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308068024672321835387/50000000000000000000)
  centralHi := (24645441973785746831/4000000000000000000)
  directionLo := (618159490093107025551/100000000000000000000)
  directionHi := (38634968130819189097/6250000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree154.table
  base := (3427887896540253979849906944931144318531/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-7309112226046690948726856985538919824500000000000)
      constant := (298308599145018403315845122861453313333987102372112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree154.table
  base := (109692412689265351002333621258748374579811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-14634856955793712987729994625460682649000000000000)
      constant := (597937778509305027843004561030659147505015580402417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (618159490093107025551/100000000000000000000)
  centralHi := (38634968130819189097/6250000000000000000)
  directionLo := (620176329024508146271/100000000000000000000)
  directionHi := (19380510282015879571/3125000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree155.table
  base := (111890046184312654966272283202882269228001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-14713124766063556718258663876227946709000000000000)
      constant := (604505215290473709010036085030403689849227957644347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree155.table
  base := (11189004618429327554447957649816203760417/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151528347000000000000000000000000000000000000000
      center := (2727510246)
      previous := (1363755123)
      next := (1363755123)
      square := (9210950945318420150144930703807678000000000000)
      linear := (-1472986527303466917925102427511976920900000000000)
      constant := (60584299947509515249508694486607611911631172040699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620176329024508146271/100000000000000000000)
  centralHi := (19380510282015879571/3125000000000000000)
  directionLo := (38886664396180491081/6250000000000000000)
  directionHi := (622186630338887857297/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree156.table
  base := (114108172815630984935218067761990079731259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (3030566940)
      previous := (1515283470)
      next := (1515283470)
      square := (10234389939242689055716589670897420000000000000)
      linear := (-1645336120003747948784845975708672641000000000000)
      constant := (68049469491132089737904265448884048249563986722097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree156.table
  base := (57054086407807248251327045758711433898091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-274534696116215284643926924532941773500000000000)
      constant := (11366672683502219096224906637575922415576944284651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38886664396180491081/6250000000000000000)
  centralHi := (622186630338887857297/100000000000000000000)
  directionLo := (156047614300612745377/25000000000000000000)
  directionHi := (624190457202450981509/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree157.table
  base := (23269358516662275059489607178468768423271/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303056694000000000000000000000000000000000000000
      center := (5455020492)
      previous := (2727510246)
      next := (2727510246)
      square := (18421901890636840300289861407615356000000000000)
      linear := (-2980585078800781271973712737305632165800000000000)
      constant := (124087445735838489110454571421826727754404050963037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree157.table
  base := (58173396291648673578829278958417354872669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-7459940953758290781146541787218971164500000000000)
      constant := (310904877405694709187631761712111973873967929048143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156047614300612745377/25000000000000000000)
  centralHi := (624190457202450981509/100000000000000000000)
  directionLo := (626187871770724806393/100000000000000000000)
  directionHi := (313093935885362403197/50000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree158.table
  base := (29651476371855211739297715567333691154209/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-7498912853987040590336756795839133944500000000000)
      constant := (314240612533747389155135852810749047394511623725046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree158.table
  base := (14825738185926114060752978146282116657767/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-7507445112378768876907056612048514444500000000000)
      constant := (314935644590957039654022446633364130527250392884596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (626187871770724806393/100000000000000000000)
  centralHi := (313093935885362403197/50000000000000000000)
  directionLo := (314089467605527404519/50000000000000000000)
  directionHi := (628178935211054809039/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree159.table
  base := (120885511528025168944877115312260881678427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-558989852664602074128831981364013887000000000000)
      constant := (23576933873522435992133328566959127272481282550747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree159.table
  base := (12088551152801501607363345740747673410681/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16836483000000000000000000000000000000000000000
      center := (303056694)
      previous := (151528347)
      next := (151528347)
      square := (1023438993924268905571658967089742000000000000)
      linear := (-167887761577761043837057143041734616100000000000)
      constant := (7088721422452264312596129077374087751068482674923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314089467605527404519/50000000000000000000)
  centralHi := (628178935211054809039/100000000000000000000)
  directionLo := (630163707724460674437/100000000000000000000)
  directionHi := (315081853862230337219/50000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree160.table
  base := (4927424428207554070149278495798552619591/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303056694000000000000000000000000000000000000000
      center := (5455020492)
      previous := (2727510246)
      next := (2727510246)
      square := (18421901890636840300289861407615356000000000000)
      linear := (-3037525267182886164456682680395696401800000000000)
      constant := (128945039446407040230531983695857043105195720230385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree160.table
  base := (3849550334536881714484338093159753391943/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-7602453429619725068428086261707601004500000000000)
      constant := (323075335663884163529472789878804893734540254531536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (630163707724460674437/100000000000000000000)
  centralHi := (315081853862230337219/50000000000000000000)
  directionLo := (39508890535429668833/6250000000000000000)
  directionHi := (632142248566874701329/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree161.table
  base := (31376550754743786827285781063405257172441/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1432215000000000000000000000000000000000000000
      center := (25779870)
      previous := (12889935)
      next := (12889935)
      square := (87060027838548394613846225933910000000000000)
      linear := (-14444732183255770929195050384809630500000000000)
      constant := (617131543486098913861200771070808153410491034726) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree161.table
  base := (125506203018967800327439427558705301503731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2864430000000000000000000000000000000000000000
      center := (51559740)
      previous := (25779870)
      next := (25779870)
      square := (174120055677096789227692451867820000000000000)
      linear := (-28922334927184132945892631707134761000000000000)
      constant := (1236991529495495815758092231083277698678633218833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39508890535429668833/6250000000000000000)
  centralHi := (632142248566874701329/100000000000000000000)
  directionLo := (4954020438045185887/781250000000000000)
  directionHi := (634114616069783793537/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree162.table
  base := (3995227764670189198619067741735940785017/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-284767165997310749331357652079235113500000000000)
      constant := (12244021146553472509117995622681035251251708667792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree162.table
  base := (127847288469439804877527766562188257861693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3411463313080896351905529890299140000000000000)
      linear := (-570182351619309722959193771212347227000000000000)
      constant := (24542165605435558008658111654707796079429336848573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4954020438045185887/781250000000000000)
  centralHi := (634114616069783793537/100000000000000000000)
  directionLo := (6360808676602953803/1000000000000000000)
  directionHi := (636080867660295380301/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree163.table
  base := (130208867056662328242990105640399299909009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-15472327277824955284698263117428803189000000000000)
      constant := (669481103948829001191968284802556389584669384178123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree163.table
  base := (26041773411331402504783835343316450452821/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 303056694000000000000000000000000000000000000000
      center := (5455020492)
      previous := (2727510246)
      next := (2727510246)
      square := (18421901890636840300289861407615356000000000000)
      linear := (-3097986362192463742283852294478492337800000000000)
      constant := (134192105611741175330548624610612763477423367616887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6360808676602953803/1000000000000000000)
  centralHi := (636080867660295380301/100000000000000000000)
  directionLo := (127608211976129358803/20000000000000000000)
  directionHi := (19938783121270212313/3125000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree164.table
  base := (33147734695170873563234306147408708361953/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-7783613795897565052751606511289455124500000000000)
      constant := (338918529556563063865782339905835737725983631563382) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree164.table
  base := (132590938780678972946591579731527771148317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-15584940128203274902940291122051548249000000000000)
      constant := (679334689238963741257524548844071109202698766841999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127608211976129358803/20000000000000000000)
  centralHi := (19938783121270212313/3125000000000000000)
  directionLo := (15999881210179421407/2500000000000000000)
  directionHi := (639995248407176856281/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree165.table
  base := (134993503641567863756627112487219860535587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (3030566940)
      previous := (1515283470)
      next := (1515283470)
      square := (10234389939242689055716589670897420000000000000)
      linear := (-1740236433973922769589795880858779701000000000000)
      constant := (76249445267420858992979575918284654751669781420521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree165.table
  base := (33748375910391004571050900484291683265939/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-290369415656374649897431866142789533500000000000)
      constant := (12736313979398935167049281638800545384898910968358) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15999881210179421407/2500000000000000000)
  centralHi := (639995248407176856281/100000000000000000000)
  directionLo := (641943488068777681013/100000000000000000000)
  directionHi := (320971744034388840507/50000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree166.table
  base := (137416561639372552598058315228630397182771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-15757028219735479747113112832879124369000000000000)
      constant := (694704948829822465477151404691172757008058746509537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree166.table
  base := (137416561639369282057661756913364372292987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-15774956762685187285982350421369721369000000000000)
      constant := (696239325004450807290134355950828873566248919802489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (641943488068777681013/100000000000000000000)
  centralHi := (320971744034388840507/50000000000000000000)
  directionLo := (321942916432421997543/50000000000000000000)
  directionHi := (643885832864843995087/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree167.table
  base := (139860112774153501207222719721789547929117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-15851928533705654567918062738029231429000000000000)
      constant := (703216883382238807913457483938072597415076372179599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree167.table
  base := (139860112774150719742379048015560926970643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-15869965079926143477503380071028807929000000000000)
      constant := (704769799589697144906638922751624690289649251317121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321942916432421997543/50000000000000000000)
  centralHi := (643885832864843995087/100000000000000000000)
  directionLo := (161455583995684150103/25000000000000000000)
  directionHi := (645822335982736600413/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree168.table
  base := (71162078522982748012543424227366783848613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1705731656540448175952764945149570000000000000)
      linear := (-295311645327330173865240974873691453500000000000)
      constant := (13181126130815649258232816504448368055010615782693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree168.table
  base := (142324157045963130584406868855455689755971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 168364830000000000000000000000000000000000000000
      center := (3030566940)
      previous := (1515283470)
      next := (1515283470)
      square := (10234389939242689055716589670897420000000000000)
      linear := (-1773885933018566629891601080076432721000000000000)
      constant := (79261375404809979501038435872071561625829679889993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell092.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161455583995684150103/25000000000000000000)
  centralHi := (645822335982736600413/100000000000000000000)
  directionLo := (647753049814775955413/100000000000000000000)
  directionHi := (323876524907387977707/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree169.table
  base := (18101086806857773986755898227210259437153/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 757641735000000000000000000000000000000000000000
      center := (13637551230)
      previous := (6818775615)
      next := (6818775615)
      square := (46054754726592100750724653519038390000000000000)
      linear := (-8020864580823002104763981274164722774500000000000)
      constant := (360198365937624675900036055697925935755061777904364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 10996
  qDenominator := 21321
  table := BinomialMassData.Q10996_21321.Degree169.table
  base := (144808694454860180323993765991962096936481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1515283470000000000000000000000000000000000000000
      center := (27275102460)
      previous := (13637551230)
      next := (13637551230)
      square := (92109509453184201501449307038076780000000000000)
      linear := (-16059981714408055860545439370346981049000000000000)
      constant := (721987062165236950979165749871111657711438729926907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10996_21321.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell092.Kernel169
