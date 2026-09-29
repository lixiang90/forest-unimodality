import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell133.Parameters
import ForestUnimodality.BinomialMassData.Q23557_44732.Batch000_049
import ForestUnimodality.BinomialMassData.Q23557_44732.Batch050_099
import ForestUnimodality.BinomialMassData.Q23557_44732.Batch100_149
import ForestUnimodality.BinomialMassData.Q23557_44732.Batch150_199
import ForestUnimodality.BinomialMassData.Q11791_22366.Batch000_049
import ForestUnimodality.BinomialMassData.Q11791_22366.Batch050_099
import ForestUnimodality.BinomialMassData.Q11791_22366.Batch100_149
import ForestUnimodality.BinomialMassData.Q11791_22366.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree000.table
  base := (151870586184680418686525627/2000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (38)
      previous := (19)
      next := (19)
      square := (174529484794989017681920985000000000000)
      linear := (-12737215645499259161071981000000000000)
      constant := (189838232730850523358157033750000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree000.table
  base := (151870586184680418686525627/2000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (38)
      previous := (19)
      next := (19)
      square := (174529484794989017681920985000000000000)
      linear := (-12737215645499259161071981000000000000)
      constant := (189838232730850523358157033750000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree001.table
  base := (209110885126369139346093822992062838320239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-49163505732705750986972141666037453000000000000)
      constant := (26165084676048862389079066596007978429843707697871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree001.table
  base := (208930496682154312034992009813382028161963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-49212299813417310041590564725418828000000000000)
      constant := (26142552879726707346392446378987334389218702016907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9985209535862424591/20000000000000000000)
  directionHi := (12481511919828030739/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree002.table
  base := (123046275640969989540506565471275539746359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-95141192105593616972819822059919488000000000000)
      constant := (15439885840506252790322786066822647122378846150551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree002.table
  base := (122864918616044224015478994247755429102381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-95238780267016735082056668178682238000000000000)
      constant := (15417311823966837268625707606313604316519496543309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9985209535862424591/20000000000000000000)
  centralHi := (12481511919828030739/25000000000000000000)
  directionLo := (7060609374376899231/10000000000000000000)
  directionHi := (70606093743768992311/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree003.table
  base := (78020966900603333822311186850059186113603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-141118878478481482958667502453801523000000000000)
      constant := (9871253994933249830409387550279126824748087128867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree003.table
  base := (77879542309137602547303855762718526110101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-141265260720616160122522771631945648000000000000)
      constant := (9853804237767025848346661477853019237662388798389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7060609374376899231/10000000000000000000)
  centralHi := (70606093743768992311/100000000000000000000)
  directionLo := (86474451201674834651/100000000000000000000)
  directionHi := (21618612800418708663/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree004.table
  base := (26619466684564157233305671431347851431927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-93548282425684674472257591423841779000000000000)
      constant := (3429224406274563405120815827269317457324708905303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree004.table
  base := (53136192988056032629174374453915631335133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-187291741174215585162988875085209058000000000000)
      constant := (6846018632275877701863768632691227955884120727037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86474451201674834651/100000000000000000000)
  centralHi := (21618612800418708663/25000000000000000000)
  directionLo := (99852095358624245911/100000000000000000000)
  directionHi := (12481511919828030739/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree005.table
  base := (3094973993744220861882773933504226422077/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-466148502448514429860725726483131186000000000000)
      constant := (10298499228793383210685417510537177853381198466325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree005.table
  base := (4826612339556627695772449926125916732369/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-116659110813907505101727489269236234000000000000)
      constant := (2570306159180779962904616324613489973576467597764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99852095358624245911/100000000000000000000)
  centralHi := (12481511919828030739/12500000000000000000)
  directionLo := (55819018229418763871/50000000000000000000)
  directionHi := (111638036458837527743/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree006.table
  base := (58985150255808848064040039874068320510699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-558103875194290161832421087270895256000000000000)
      constant := (8268453899624631781952802862307983765156235972811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree006.table
  base := (11774967472428577393972769825444011996983/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-558689404162828870487842163983471756000000000000)
      constant := (8256530699266383865697041628230321268262817608435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55819018229418763871/50000000000000000000)
  centralHi := (111638036458837527743/100000000000000000000)
  directionLo := (30573335422044734467/25000000000000000000)
  directionHi := (122293341688178937869/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree007.table
  base := (363211262427158515889710164991722663879/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-162514811985016473451029112014664831500000000000)
      constant := (1756017912152460107537412482389233986694147930592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree007.table
  base := (46405856261450211077502053413110250163491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-650742365070027720568774370889998576000000000000)
      constant := (7015962905189752603440673120424372953108350916099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30573335422044734467/25000000000000000000)
  centralHi := (122293341688178937869/100000000000000000000)
  directionLo := (132091906103813309789/100000000000000000000)
  directionHi := (13209190610381330979/10000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree008.table
  base := (1497904194499171935970167497965991916979/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-742014620685841625775811808846423396000000000000)
      constant := (6259654686491898517453118312376101940888104093275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree008.table
  base := (18689628378886423225252923601393892381551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-371397662988613285324853288898262698000000000000)
      constant := (3127213226826602130152219787242702532957761087439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132091906103813309789/100000000000000000000)
  centralHi := (13209190610381330979/10000000000000000000)
  directionLo := (141212187487537984621/100000000000000000000)
  directionHi := (70606093743768992311/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree009.table
  base := (955258633421258634022036878700487878643/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-208492498357904339436876792408546866500000000000)
      constant := (1453576500414901216757958138662727339042800747416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree009.table
  base := (29796631299900600108850802904250296323/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-208712071721106355182659696175763054000000000000)
      constant := (1452858488277884541456212071790696809230757490432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141212187487537984621/100000000000000000000)
  centralHi := (70606093743768992311/50000000000000000000)
  directionLo := (149778143037936368867/100000000000000000000)
  directionHi := (37444535759484092217/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree010.table
  base := (785658704587889971583610392378481359271/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-231481341544348272429800632605487884000000000000)
      constant := (1399746520297276686167638055398975170841653380152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree010.table
  base := (2509335926991011195881642191838452993607/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-463450623895812135405785495804789518000000000000)
      constant := (2799097954369866239944486669029070689655058434115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149778143037936368867/100000000000000000000)
  centralHi := (37444535759484092217/25000000000000000000)
  directionLo := (39470006309197521287/25000000000000000000)
  directionHi := (157880025236790085149/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree011.table
  base := (10373464869902792388076775733091386347797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-508940369461584410845448945604857803000000000000)
      constant := (2780642374990106256977815887290893510582069095733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree011.table
  base := (20706151353409976468815045097463290176179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-1018954208698823120892503198516105856000000000000)
      constant := (5562445975589499866353936972218587496691665712531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39470006309197521287/25000000000000000000)
  centralHi := (157880025236790085149/100000000000000000000)
  directionLo := (33117193483534453391/20000000000000000000)
  directionHi := (41396491854418066739/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree012.table
  base := (3424391785559990670789031210339753580559/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-1109836111668944553662593251997479676000000000000)
      constant := (5668202445533268054664374969319670767853144371755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree012.table
  base := (17086896412747485279870007219085437563589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-1111007169606021970973435405422632676000000000000)
      constant := (5671264708247896563170339455083881541043845346021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33117193483534453391/20000000000000000000)
  centralHi := (41396491854418066739/25000000000000000000)
  directionLo := (86474451201674834651/50000000000000000000)
  directionHi := (172948902403349669303/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree013.table
  base := (7044463496719946118153496763204083328187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-600895742207360142817144306392621873000000000000)
      constant := (2948786867200479710266255221607123908361485516443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree013.table
  base := (1757338661700287771005023112754198785591/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-300765032628305205263591903082289874000000000000)
      constant := (1475632734925983794965978582628256386210862045998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86474451201674834651/50000000000000000000)
  centralHi := (172948902403349669303/100000000000000000000)
  directionLo := (180010924889019767617/100000000000000000000)
  directionHi := (90005462444509883809/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree014.table
  base := (11522078204524197026000396923461998108823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-1293746857160496017605983973573007816000000000000)
      constant := (6233671668975383144456817494350205933408370771447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree014.table
  base := (11496034214357271226053730020914129309093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-1295113091420419671135299819235686316000000000000)
      constant := (6240542728067578605037912887858685588275093633477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180010924889019767617/100000000000000000000)
  centralHi := (90005462444509883809/50000000000000000000)
  directionLo := (7472246603669047951/4000000000000000000)
  directionHi := (23350770636465774847/12500000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree015.table
  base := (9328375911267832619044237464542353268637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-1385702229906271749577679334360771886000000000000)
      constant := (6664861133376150776486354292067913139883222946493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree015.table
  base := (2326488655311770978468560527986047444039/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-346791513081904630304058006535553284000000000000)
      constant := (1668419994151324081687011710930203396231273436071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7472246603669047951/4000000000000000000)
  centralHi := (23350770636465774847/12500000000000000000)
  directionLo := (193362751203933306243/100000000000000000000)
  directionHi := (48340687800983326561/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree016.table
  base := (7436932516750220230326342201173786049971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-1477657602652047481549374695148535956000000000000)
      constant := (7182276960955936760170751679751406819604701724819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree016.table
  base := (7417662611947870636241704936713570866517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-1479219013234817371297164233048739956000000000000)
      constant := (7193087485235303300908461745192127647931903229813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193362751203933306243/100000000000000000000)
  centralHi := (48340687800983326561/25000000000000000000)
  directionLo := (199704190717248491823/100000000000000000000)
  directionHi := (12481511919828030739/6250000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree017.table
  base := (362041514091259785192488758606208464581/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-392403243849455803380267513984075006500000000000)
      constant := (1944757600098982379360306729341281552044397836436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree017.table
  base := (2888066868452893054704341669112187634413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-785635987071008110689048219977633388000000000000)
      constant := (3895941962206944679174321673238917982731808594957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199704190717248491823/100000000000000000000)
  centralHi := (12481511919828030739/6250000000000000000)
  directionLo := (4117007361028547207/2000000000000000000)
  directionHi := (205850368051427360351/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree018.table
  base := (4352219360802355396360051755268489609157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-1661568348143598945492765416724064096000000000000)
      constant := (8449699913173829293697704790582200431322984140773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree018.table
  base := (135564532120881458650600590889907825927/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-415831233762303767864757161715448399000000000000)
      constant := (2116163461764799540417597997292065245740252570424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4117007361028547207/2000000000000000000)
  centralHi := (205850368051427360351/100000000000000000000)
  directionLo := (52954570307826744233/25000000000000000000)
  directionHi := (211818281231306976933/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree019.table
  base := (770299993369301397522973472976872059333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-438380930222343669366115194377957041500000000000)
      constant := (2297495927331894702965920118491086697371062660837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree019.table
  base := (306910104901359587062302845756448435853/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-877688947978206960769980426884160208000000000000)
      constant := (4603550389961508032504743164514164658713127295585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52954570307826744233/25000000000000000000)
  centralHi := (211818281231306976933/100000000000000000000)
  directionLo := (217622596484514909267/100000000000000000000)
  directionHi := (54405649121128727317/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree020.table
  base := (1952168049993265137768744610465384035351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-1845479093635150409436156138299592236000000000000)
      constant := (9996450404910763228732303654125057699649753995639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree020.table
  base := (1941841999634255662132254188521406513493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-1847430856863612771620893060674847236000000000000)
      constant := (10015798117930136514531915529464898484138706185077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217622596484514909267/100000000000000000000)
  centralHi := (54405649121128727317/25000000000000000000)
  directionLo := (55819018229418763871/25000000000000000000)
  directionHi := (44655214583535011097/20000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree021.table
  base := (943160203111302865647789979852919782459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-1937434466380926141407851499087356306000000000000)
      constant := (10866353269938535172962427803420229440402313703451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree021.table
  base := (467179574542385267360213797468072323049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-969741908885405810850912633790687028000000000000)
      constant := (5444001732615812602767851217595765764035550861961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55819018229418763871/25000000000000000000)
  centralHi := (44655214583535011097/20000000000000000000)
  directionLo := (1429936829002638469/625000000000000000)
  directionHi := (228789892640422155041/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree022.table
  base := (36552148266454541836720084420310322719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-2029389839126701873379546859875120376000000000000)
      constant := (11797488220389222136359223140769066777180663230591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree022.table
  base := (29059594886029036731610988284390047123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-2031536778678010471782757474487900876000000000000)
      constant := (11821516662433417626702707275065537237969888300147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1429936829002638469/625000000000000000)
  centralHi := (228789892640422155041/100000000000000000000)
  directionLo := (117086960430370771497/50000000000000000000)
  directionHi := (46834784172148308599/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree023.table
  base := (-781824367484926419056611000466690653147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-2121345211872477605351242220662884446000000000000)
      constant := (12788083381789668931156953032223378354646359938117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree023.table
  base := (-31527866908828592560903387327748726371/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-2123589739585209321863689681394427696000000000000)
      constant := (12814569367140629992219647012540632861991047889525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117086960430370771497/50000000000000000000)
  centralHi := (46834784172148308599/20000000000000000000)
  directionLo := (59859228323714731243/25000000000000000000)
  directionHi := (239436913294858924973/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree024.table
  base := (-1523375902196463181376745193024775388669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-2213300584618253337322937581450648516000000000000)
      constant := (13836712255818440609824126045551904849553278469859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree024.table
  base := (-382197746524664185728189831432473716933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-553910675123102042986155472075238629000000000000)
      constant := (3466434558935945470566172521930008054954428372763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59859228323714731243/25000000000000000000)
  centralHi := (239436913294858924973/100000000000000000000)
  directionLo := (244586683376357875737/100000000000000000000)
  directionHi := (122293341688178937869/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree025.table
  base := (-549324277346125656002403067751417670927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-576313989341007267323658235559603146500000000000)
      constant := (3735556240951312694635130728364782934860799223697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree025.table
  base := (-2201895639240489876307027953361071333819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-2307695661399607022025554095207481336000000000000)
      constant := (14973876185843189324720427611055048861500047441509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244586683376357875737/100000000000000000000)
  centralHi := (122293341688178937869/50000000000000000000)
  directionLo := (249630238396560614779/100000000000000000000)
  directionHi := (12481511919828030739/5000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree026.table
  base := (-5490250109748621364879168067023674957/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-599302832527451200316582075756544164000000000000)
      constant := (4025923388986236009512301468900202354498861827456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree026.table
  base := (-562982203812539874122817880326539064777/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-2399748622306805872106486302114008156000000000000)
      constant := (16138057728832674400250302631017474053102252405235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249630238396560614779/100000000000000000000)
  centralHi := (12481511919828030739/5000000000000000000)
  directionLo := (254573891353376285057/100000000000000000000)
  directionHi := (127286945676688142529/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree027.table
  base := (-674100626503841841229809633841916807557/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-2489166702855580533238023663813940726000000000000)
      constant := (17320368376899463051129838380119893829582051208135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree027.table
  base := (-337381430103577556598025685538093141909/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-1245900791607002361093709254510267488000000000000)
      constant := (8678767681101117126168090517738867251692279877495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254573891353376285057/100000000000000000000)
  centralHi := (127286945676688142529/50000000000000000000)
  directionLo := (259423353605024503953/100000000000000000000)
  directionHi := (129711676802512251977/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree028.table
  base := (-970157503486942685500902265325827199219/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-645280518900339066302429756150426199000000000000)
      constant := (4647910794709498725760878406047306793963370660909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree028.table
  base := (-776687636876939087598411549356929534999/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-2583854544121203572268350715927061796000000000000)
      constant := (18631704711056302564374446228483058816720087222445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259423353605024503953/100000000000000000000)
  centralHi := (129711676802512251977/50000000000000000000)
  directionLo := (264183812207626619579/100000000000000000000)
  directionHi := (13209190610381330979/5000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree029.table
  base := (-4345313053340718260428607715655711497051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-2673077448347131997181414385389468866000000000000)
      constant := (19917027184196744643534431604627359405497376933061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree029.table
  base := (-2173847026567694635228017820321837679457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-1337953752514201211174641461416794308000000000000)
      constant := (9980038309853656866161313448481670853766161782527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264183812207626619579/100000000000000000000)
  centralHi := (13209190610381330979/5000000000000000000)
  directionLo := (67214998730487730297/25000000000000000000)
  directionHi := (268859994921950921189/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree030.table
  base := (-2383866199273705708371586170362398372899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-1382516410546453864576554873088616468000000000000)
      constant := (10648061342655363452565583007879523492170819611389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree030.table
  base := (-953950173843079342734175008338922654489/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-2767960465935601272430215129740115436000000000000)
      constant := (21342254779395949192487130859384006050095410519395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67214998730487730297/25000000000000000000)
  centralHi := (268859994921950921189/100000000000000000000)
  directionLo := (273456225210376994529/100000000000000000000)
  directionHi := (27345622521037699453/10000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree031.table
  base := (-5150467768052339055148356528680494510993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-2856988193838683461124805106964997006000000000000)
      constant := (22728607063904507658551732482085904069437910537423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree031.table
  base := (-2576089367774450666864987314650302820531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-1430006713421400061255573668323321128000000000000)
      constant := (11388958887181916571175059975315311091069134431341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273456225210376994529/100000000000000000000)
  centralHi := (27345622521037699453/10000000000000000000)
  directionLo := (277976469045826556927/100000000000000000000)
  directionHi := (271461395552564997/97656250000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree032.table
  base := (-5495613973403119050380972847894350399179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-2948943566584459193096500467752761076000000000000)
      constant := (24214218343916390513214279214318607605091728240469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree032.table
  base := (-1099412844344122605847748521883400443831/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-2952066387749998972592079543553169076000000000000)
      constant := (24266804659284938819778760007830007306560609688205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277976469045826556927/100000000000000000000)
  centralHi := (271461395552564997/97656250000000000)
  directionLo := (141212187487537984621/50000000000000000000)
  directionHi := (282424374975075969243/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree033.table
  base := (-11609747657849764766334504193447231797/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-760224734832558731267048957135131286500000000000)
      constant := (6438185893064253177202778734979634420187828533375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree033.table
  base := (-5806103094636280249671208442363772823523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-3044119348657197822673011750459695896000000000000)
      constant := (25808703362416570212519286587903600221578126440253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141212187487537984621/50000000000000000000)
  centralHi := (282424374975075969243/100000000000000000000)
  directionLo := (35850413573481631629/12500000000000000000)
  directionHi := (286803308587853053033/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree034.table
  base := (-1215926588968197035615111179803143220627/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-3132854312076010657039891189328289216000000000000)
      constant := (27344009465219888152538700008640125100172865601985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree034.table
  base := (-3040337475446041233905244745038460799923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-1568086154782198336376971978683111358000000000000)
      constant := (13701720676056691488176576812870328099015098380653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35850413573481631629/12500000000000000000)
  centralHi := (286803308587853053033/100000000000000000000)
  directionLo := (291116382317821839579/100000000000000000000)
  directionHi := (14555819115891091979/5000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree035.table
  base := (-1264203998499436528424215773369184155413/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-3224809684821786389011586550116053286000000000000)
      constant := (28987874871743267755888624967061683397135768180215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree035.table
  base := (-3160951669615432773234199411719469078459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-1614112635235797761417438082136374768000000000000)
      constant := (14525439058971865107635675837766545153196616552549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291116382317821839579/100000000000000000000)
  centralHi := (14555819115891091979/5000000000000000000)
  directionLo := (295366481325645953257/100000000000000000000)
  directionHi := (147683240662822976629/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree036.table
  base := (-6529955309177497395072941965382125396073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-3316765057567562120983281910903817356000000000000)
      constant := (30684224694916704002168122249300128764233188013303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree036.table
  base := (-1632676059916805385772193415855176095583/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-830069557844698593228952092794819089000000000000)
      constant := (7687724776978763208506623952056775993481374862913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295366481325645953257/100000000000000000000)
  centralHi := (147683240662822976629/50000000000000000000)
  directionLo := (59911257215174547547/20000000000000000000)
  directionHi := (37444535759484092217/12500000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree037.table
  base := (-3353595067928129257636546083684359149581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-1704360215156668926477488635845790713000000000000)
      constant := (16216482492463915717360953499839475534085925575891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree037.table
  base := (-6707825191373730238245189229769265979551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-3412331192285993222996740578085803176000000000000)
      constant := (32503410835160420522448322579938068955692267490561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59911257215174547547/20000000000000000000)
  centralHi := (37444535759484092217/12500000000000000000)
  directionLo := (303688292109602168103/100000000000000000000)
  directionHi := (37961036513700271013/12500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree038.table
  base := (-6853338323607475413528562939160810925263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-3500675803059113584926672632479345496000000000000)
      constant := (34234018973875012335453260535289881379860992029393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree038.table
  base := (-6853876903623977363318494805026813702563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-3504384153193192073077672784992329996000000000000)
      constant := (34308336924690151087772651715005242255059273229693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303688292109602168103/100000000000000000000)
  centralHi := (37961036513700271013/12500000000000000000)
  directionLo := (307764827427248420933/100000000000000000000)
  directionHi := (153882413713624210467/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree039.table
  base := (-3484450989642928429140702944009788730761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-1796315587902444658449183996633554783000000000000)
      constant := (18043661934265786714268500278008604282958070758871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree039.table
  base := (-435584926182924596411568528882242958157/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-899109278525097730789651247974714204000000000000)
      constant := (9041403729119826323534981218798108577666148792908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307764827427248420933/100000000000000000000)
  centralHi := (153882413713624210467/50000000000000000000)
  directionLo := (311788067825247201697/100000000000000000000)
  directionHi := (155894033912623600849/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree040.table
  base := (-3527146114776677453003316644603103804521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-1842293274275332524435031677027436818000000000000)
      constant := (18996414126803628357023931442724020450392647850231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree040.table
  base := (-7054679805970301300243271761734183056911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-3688490075007589773239537198805383636000000000000)
      constant := (38075193677618678438304515334078624753070252421521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311788067825247201697/100000000000000000000)
  centralHi := (155894033912623600849/50000000000000000000)
  directionLo := (39470006309197521287/12500000000000000000)
  directionHi := (315760050473580170297/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree041.table
  base := (-7109846049347135639157506120588132972161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-3776541921296440780841758714842637706000000000000)
      constant := (39950489987188614394606110839306637078287494114271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree041.table
  base := (-71101749270904735992082809506128267581/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-945135758978697155830117351427977614000000000000)
      constant := (10009257826345937648801606173726401264946621847275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39470006309197521287/12500000000000000000)
  centralHi := (315760050473580170297/100000000000000000000)
  directionLo := (159841342987315741073/50000000000000000000)
  directionHi := (319682685974631482147/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree042.table
  base := (-3567919957283373699764678543580923525281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-1934248647021108256406727037815200888000000000000)
      constant := (20980137246670464069628011383460573937280279558591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree042.table
  base := (-892014879845429920117850505180564145001/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-968148999205496868350350403154609319000000000000)
      constant := (10512773356591017185307352265678878328588906071022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159841342987315741073/50000000000000000000)
  centralHi := (319682685974631482147/100000000000000000000)
  directionLo := (161778884552984688611/50000000000000000000)
  directionHi := (323557769105969377223/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree043.table
  base := (-1426500177928996013735118583812820741803/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-3960452666787992244785149436418165846000000000000)
      constant := (44022153375502263170566159096411509951157579406665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree043.table
  base := (-891592229328018277468628713644694037049/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-991162239432296580870583454881241024000000000000)
      constant := (11029337953857243943171469462560056988080609984078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161778884552984688611/50000000000000000000)
  centralHi := (323557769105969377223/100000000000000000000)
  directionLo := (327386988418459811859/100000000000000000000)
  directionHi := (16369349420922990593/5000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree044.table
  base := (-1775003910310074566570413333933468039837/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-1013102009883441994189211199301482479000000000000)
      constant := (11534025822308924641418519848931095612940153136707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree044.table
  base := (-7100216821208156911001641693289753280381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-4056701918636385173563266026431490916000000000000)
      constant := (46235783273225928053562430885476541469819478414691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327386988418459811859/100000000000000000000)
  centralHi := (16369349420922990593/5000000000000000000)
  directionLo := (33117193483534453391/10000000000000000000)
  directionHi := (331171934835344533911/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree045.table
  base := (-3519268886782943447994367152108238963937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-2072181706139771854364270078996846993000000000000)
      constant := (24151052512438412586733950728936108063105149351807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree045.table
  base := (-281548344840359154080878925667523913677/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-4148754879543584023644198233338017736000000000000)
      constant := (48406368712863877640431152496155948881506856723675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33117193483534453391/10000000000000000000)
  centralHi := (331171934835344533911/100000000000000000000)
  directionLo := (167457054688256291613/50000000000000000000)
  directionHi := (334914109376512583227/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree046.table
  base := (-868524225510856841000845448423749968713/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-1059079696256329860175058879695364514000000000000)
      constant := (12630035690054026728953938323525641319647972464686) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree046.table
  base := (-6948338920772009910058106856771676465463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-4240807840450782873725130440244544556000000000000)
      constant := (50629092416022671002912307610778230767555871071593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167457054688256291613/50000000000000000000)
  centralHi := (334914109376512583227/100000000000000000000)
  directionLo := (338614930114340323423/100000000000000000000)
  directionHi := (10581716566073135107/3125000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree047.table
  base := (-6829088036676509491731374651582230913649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-4328274157771095172671930879569222126000000000000)
      constant := (52790203451064447207339666704285177373709052934639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree047.table
  base := (-170730283035229385431178022238267368617/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-1083215200339495430951515661787767844000000000000)
      constant := (13225985356606300706240669492583359018103833432870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338614930114340323423/100000000000000000000)
  centralHi := (10581716566073135107/3125000000000000000)
  directionLo := (342275738452518028681/100000000000000000000)
  directionHi := (171137869226259014341/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree048.table
  base := (-6681306539797791571950256081797901748099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-4420229530516870904643626240356986196000000000000)
      constant := (55112276333743851708080629980488227774110532338589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree048.table
  base := (-3340705648243750558524401194551347246673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-2212456881132590286943497427028799098000000000000)
      constant := (27615452527395428929927668750950828513069517669903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342275738452518028681/100000000000000000000)
  centralHi := (171137869226259014341/50000000000000000000)
  directionLo := (86474451201674834651/25000000000000000000)
  directionHi := (69179560961339867721/20000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree049.table
  base := (-6504920397451908150983888089569636284441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-4512184903262646636615321601144750266000000000000)
      constant := (57486352518525453372434514033222834611601949889351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree049.table
  base := (-6505009426504906009421218724140426109887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-4516966723172379423967927060964125016000000000000)
      constant := (57609974474358632991892139278931606045455273932257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86474451201674834651/25000000000000000000)
  centralHi := (69179560961339867721/20000000000000000000)
  directionLo := (349482333755184860691/100000000000000000000)
  directionHi := (87370583438796215173/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree050.table
  base := (-1574997092146255422217153504765365303893/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-1151035069002105592146754240483128584000000000000)
      constant := (14978106164261367736159547710609823393946811709323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree050.table
  base := (-1575016011047428380240003526527205723203/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-1152254921019894568512214816967662959000000000000)
      constant := (15010285597516833029379075756677917657658357376733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349482333755184860691/100000000000000000000)
  centralHi := (87370583438796215173/25000000000000000000)
  directionLo := (353030468718844961553/100000000000000000000)
  directionHi := (176515234359422480777/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree051.table
  base := (-6066559064825476735684862775618952908831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-4696095648754198100558712322720278406000000000000)
      constant := (62390486669958504197342667060334257517756531552641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree051.table
  base := (-3033311700153636466813398817583139715403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-2350536322493388562064895737388589328000000000000)
      constant := (31262201383850448398309596496779146067676095390933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353030468718844961553/100000000000000000000)
  centralHi := (176515234359422480777/50000000000000000000)
  directionLo := (71308659244365075449/20000000000000000000)
  directionHi := (178271648110912688623/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree052.table
  base := (-232186909424300137678328386715472644447/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-4788051021499973832530407683508042476000000000000)
      constant := (64920533523690875768814821157377602379299487310425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree052.table
  base := (-725590929837172517832577197895437590211/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-1198281401473493993552680920420926369000000000000)
      constant := (16264937652975783364169479067436872077073641875642) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71308659244365075449/20000000000000000000)
  centralHi := (178271648110912688623/50000000000000000000)
  directionLo := (72004369955607907047/20000000000000000000)
  directionHi := (90005462444509883809/25000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree053.table
  base := (-5514362732937987771094937278229887152637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6767192)
      previous := (3383596)
      next := (3383596)
      square := (31080908770230824224867216692740000000000000)
      linear := (-1737275327250177844251371678282594000000000000)
      constant := (24030815609561284220715482639526230444077448123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree053.table
  base := (-3446505782822537208528529880973891061/6250000000000000000000000000000000000)
  polynomial :=
    { denominator := 111302500000000000000000000000000000000000000
      center := (1691798)
      previous := (845899)
      next := (845899)
      square := (7770227192557706056216804173185000000000000)
      linear := (-434779153328691244596978986168586000000000000)
      constant := (6020575096481030641755053142215051308429287600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72004369955607907047/20000000000000000000)
  centralHi := (90005462444509883809/25000000000000000000)
  directionLo := (181733556721425427813/50000000000000000000)
  directionHi := (363467113442850855627/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree054.table
  base := (-2597828357246316000913918272624028393397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-2485980883495762648236899202541785308000000000000)
      constant := (35068282890902014382086558694581930809500280205867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree054.table
  base := (-1298924070031854578349330426518604758811/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-1244307881927093418593147023874189779000000000000)
      constant := (17571673213186570763909805021204560215870128092421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181733556721425427813/50000000000000000000)
  centralHi := (363467113442850855627/100000000000000000000)
  directionLo := (183440012532268406803/50000000000000000000)
  directionHi := (366880025064536813607/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree055.table
  base := (-4848577632755366646894029929344241348129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-5063917139737301028445493765871334686000000000000)
      constant := (72822544856904108302730388595353231833160316153919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree055.table
  base := (-1212152822038806697581399686517111647057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-1267321122153893131113380075600821484000000000000)
      constant := (18244570242694266695323280818042151291413103226127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183440012532268406803/50000000000000000000)
  centralHi := (366880025064536813607/100000000000000000000)
  directionLo := (74052295853196100081/20000000000000000000)
  directionHi := (185130739632990250203/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree056.table
  base := (-279571534314636723481357868141747366069/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-1288968128120769190104297281664774689000000000000)
      constant := (18890123972190112089154825767653885073329259685036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree056.table
  base := (-1118293295088582646839273950938695379381/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-1290334362380692843633613127327453189000000000000)
      constant := (18930485943514822573211099319297842529527951003691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74052295853196100081/20000000000000000000)
  centralHi := (185130739632990250203/50000000000000000000)
  directionLo := (7472246603669047951/2000000000000000000)
  directionHi := (373612330183452397551/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree057.table
  base := (-4069373303991737410435643143212258694609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-5247827885228852492388884487446862826000000000000)
      constant := (78350416896347873418119819828820007332366391405199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree057.table
  base := (-4069397663793706967684565144598005756957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-5253390410429970224615384716216339576000000000000)
      constant := (78517679298274933606005537993063942756615899385027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7472246603669047951/2000000000000000000)
  centralHi := (373612330183452397551/100000000000000000000)
  directionLo := (376933393986239965299/100000000000000000000)
  directionHi := (3769333939862399653/1000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree058.table
  base := (-1818638535247008483439077214811308296147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-2669891628987314112180289924117313448000000000000)
      constant := (40596153116137246379868306099856966504562395511117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree058.table
  base := (-454662224753830686411697540790797242709/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-1336360842834292268674079230780716599000000000000)
      constant := (20341371477550608880544928685821228763848406968598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376933393986239965299/100000000000000000000)
  centralHi := (3769333939862399653/1000000000000000000)
  directionLo := (23764090699886528573/6250000000000000000)
  directionHi := (380225451198184457169/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree059.table
  base := (-3176866809843727933858956837571973792949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-5431738630720403956332275209022390966000000000000)
      constant := (84086162525725391733945201257438127171982406256939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree059.table
  base := (-3176884448237842243075755108115495951737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-5437496332244367924777249130029393216000000000000)
      constant := (84265362251048850772238081690746417682294202117607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23764090699886528573/6250000000000000000)
  centralHi := (380225451198184457169/100000000000000000000)
  directionLo := (191744624419916853163/50000000000000000000)
  directionHi := (383489248839833706327/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree060.table
  base := (-2688151648615317258752930026577119441597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-5523694003466179688303970569810155036000000000000)
      constant := (87031984635335833685049274660336926183541913836067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree060.table
  base := (-1344083329706019300030131344270366825241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-2764774646575783387429090668467960018000000000000)
      constant := (43608653594825754436452107048571059426992808238151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191744624419916853163/50000000000000000000)
  centralHi := (383489248839833706327/100000000000000000000)
  directionLo := (193362751203933306243/50000000000000000000)
  directionHi := (386725502407866612487/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree061.table
  base := (-2171139190177311989853965160405930744017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-5615649376211955420275665930597919106000000000000)
      constant := (90029771610232435941706520057647904005833844172687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree061.table
  base := (-108557598283756527622228186087107234177/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-1405400563514691406234778385960611714000000000000)
      constant := (22555329945949243861983217130991914431778105222235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193362751203933306243/50000000000000000000)
  centralHi := (386725502407866612487/100000000000000000000)
  directionLo := (7798697954132953661/2000000000000000000)
  directionHi := (389934897706647683051/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree062.table
  base := (-6503343089749788358339586705124380327/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-2853802374478865576123680645692841588000000000000)
      constant := (46539761328899847920184451786360194387857965887125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree062.table
  base := (-325169329228047779372726073471493552693/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-5713655214965964475020045750748973676000000000000)
      constant := (93277399248222572237301602433409512273167094230615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7798697954132953661/2000000000000000000)
  centralHi := (389934897706647683051/100000000000000000000)
  directionLo := (39311809254519276059/10000000000000000000)
  directionHi := (393118092545192760591/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree063.table
  base := (-32882708789602806202896387225831764337/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-1449890030425876721054764163043361811500000000000)
      constant := (24045309279247304065576120582583456262928870849656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree063.table
  base := (-526127968373137520380098364053189960183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-2902854087936581662550488978827750248000000000000)
      constant := (48192772464062227272589678350909343086259583673513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39311809254519276059/10000000000000000000)
  centralHi := (393118092545192760591/100000000000000000000)
  directionLo := (396275718311439929369/100000000000000000000)
  directionHi := (39627571831143992937/10000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree064.table
  base := (-450376327366685437057818658420204310013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-5891515494449282616190752012961211316000000000000)
      constant := (99334914436201128419354924972450378965714176636643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree064.table
  base := (-450384205776468832519448254902720613089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-5897761136780362175181910164562027316000000000000)
      constant := (99545756277207353839457532561533660079417322948479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396275718311439929369/100000000000000000000)
  centralHi := (39627571831143992937/10000000000000000000)
  directionLo := (399408381434496983647/100000000000000000000)
  directionHi := (12481511919828030739/3125000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree065.table
  base := (179771607057400729672065373028660726009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-5983470867195058348162447373748975386000000000000)
      constant := (102540554154940510843232624686663980063999054549401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree065.table
  base := (179764900602413305131783209486940524217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-5989814097687561025262842371468554136000000000000)
      constant := (102758032839483517502527554435709118449131970145113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399408381434496983647/100000000000000000000)
  centralHi := (12481511919828030739/3125000000000000000)
  directionLo := (40251666474445698679/10000000000000000000)
  directionHi := (402516664744456986791/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree066.table
  base := (52387127909765400310358068488862465443/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-1518856559985208520033535683634184864000000000000)
      constant := (26449538972148329469451366600602211596228326954508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree066.table
  base := (838188337570692944997571103416989359849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-6081867058594759875343774578375080956000000000000)
      constant := (106022374234169352453139976045664133779261153057161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40251666474445698679/10000000000000000000)
  centralHi := (402516664744456986791/100000000000000000000)
  directionLo := (16224045149536710019/4000000000000000000)
  directionHi := (101400282184604437619/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree067.table
  base := (1524888421335132088044097936072623835043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-6167381612686609812105838095324503526000000000000)
      constant := (109107719315782335067407683951581828486949697873027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree067.table
  base := (152488356136938455505847253391600027607/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-3086960009750979362712353392640803888000000000000)
      constant := (54669390071571829910751026362569508945224586564115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16224045149536710019/4000000000000000000)
  centralHi := (101400282184604437619/25000000000000000000)
  directionLo := (6385348636882712247/1562500000000000000)
  directionHi := (408662312760493583809/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree068.table
  base := (89594103329030836551005718991965281437/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-6259336985432385544077533456112267596000000000000)
      constant := (112469244167858734170680453880041814818056310142325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree068.table
  base := (2239848445965795449587467585644928342629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-6265972980409157575505638992188134596000000000000)
      constant := (112707250300525877463042725770028646561970799656581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6385348636882712247/1562500000000000000)
  centralHi := (408662312760493583809/100000000000000000000)
  directionLo := (4117007361028547207/1000000000000000000)
  directionHi := (411700736102854720701/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree069.table
  base := (1491542367902566236929636993991288473737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-3175646179089080638024614408450015833000000000000)
      constant := (57941365110081384488465184037731812669602139140393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree069.table
  base := (1491540606880021368767615478507916772737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-3179012970658178212793285599547330708000000000000)
      constant := (58063892242005136188473761942160830563553018351393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4117007361028547207/1000000000000000000)
  centralHi := (411700736102854720701/100000000000000000000)
  directionLo := (207358449517079826577/50000000000000000000)
  directionHi := (82943379806831930631/20000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree070.table
  base := (1877291688121138381730076745586153367181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-3221623865461968504010462088843897868000000000000)
      constant := (59674088642375585037881468321705158043075285230509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree070.table
  base := (938645094482578563447044303622805119433/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-1612519725555888818916875851500297059000000000000)
      constant := (29900095626913917124948339611685504736982874949737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207358449517079826577/50000000000000000000)
  centralHi := (82943379806831930631/20000000000000000000)
  directionLo := (417711283761148017271/100000000000000000000)
  directionHi := (52213910470143502159/12500000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree071.table
  base := (45543472468755240719032132449474186511/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-1633800775917428184998154884618889951500000000000)
      constant := (30716396301085352616919882558641069826406408821975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree071.table
  base := (910868938886578381481950154477491632621/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-6542131863130754125748435612907715056000000000000)
      constant := (123125044215882594153467648284324029418886789953345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417711283761148017271/100000000000000000000)
  centralHi := (52213910470143502159/12500000000000000000)
  directionLo := (210342177664313955521/50000000000000000000)
  directionHi := (420684355328627911043/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree072.table
  base := (336398455929274453885773981445355411723/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-1656789619103872117991078724815830969000000000000)
      constant := (31608738461816574392751950551672875974853851958188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree072.table
  base := (2691186561008468633068878554404518798591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-3317092412018976487914683909907120938000000000000)
      constant := (63350884739236375781405061118070420436242684379999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210342177664313955521/50000000000000000000)
  centralHi := (420684355328627911043/100000000000000000000)
  directionLo := (52954570307826744233/12500000000000000000)
  directionHi := (84727312492522790773/20000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree073.table
  base := (1247733327715545081036799395279602216313/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-6719113849161264203936010260051087946000000000000)
      constant := (130056283103267989200087695815309285325726856220285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree073.table
  base := (3119332394448624569445534501918611392633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-3363118892472575912955150013360384348000000000000)
      constant := (65165279093200564474550991587262712781852261344537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52954570307826744233/12500000000000000000)
  centralHi := (84727312492522790773/20000000000000000000)
  directionLo := (213284169180472206893/50000000000000000000)
  directionHi := (426568338360944413787/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree074.table
  base := (7123220539502369004405232299797894800519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-6811069221907039935907705620838852016000000000000)
      constant := (133729572879989907972494297223822324326028663074791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree074.table
  base := (7123218964961595764836866505715752702391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-6818290745852350675991232233627295516000000000000)
      constant := (134011410248360263695683908421882140836211387538199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213284169180472206893/50000000000000000000)
  centralHi := (426568338360944413787/100000000000000000000)
  directionLo := (429480101435321574721/100000000000000000000)
  directionHi := (214740050717660787361/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree075.table
  base := (4018018189437239964868383497716773432629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-3451512297326407833939700490813308043000000000000)
      constant := (68727411550024631870902356809443680967838358666581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree075.table
  base := (1004504379822717327765591913849395285879/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-1727585926689887381518041110133455584000000000000)
      constant := (34436081396965060208760792457739573438572073311662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429480101435321574721/100000000000000000000)
  centralHi := (214740050717660787361/50000000000000000000)
  directionLo := (86474451201674834651/20000000000000000000)
  directionHi := (54046532001046771657/12500000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree076.table
  base := (561069602382227647693761029884499868807/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-1748744991849647849962774085603595039000000000000)
      constant := (35308008424648226204845135064990032704454281838492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree076.table
  base := (4488556248628101152286582268844840416843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-3501198333833374188076548323720174578000000000000)
      constant := (70764652070403943870568320104839920110816932573227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86474451201674834651/20000000000000000000)
  centralHi := (54046532001046771657/12500000000000000000)
  directionLo := (87049038593805963707/20000000000000000000)
  directionHi := (54405649121128727317/12500000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree077.table
  base := (9946451882512144204722750275594550852269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-7086935340144367131822791703202144226000000000000)
      constant := (145061204621255756508731084959222503694019275630541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree077.table
  base := (1989290182288835145682443945291858345117/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-7094449628573947226234028854346875976000000000000)
      constant := (145366345853485050075182515360923190789503588326065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87049038593805963707/20000000000000000000)
  centralHi := (54405649121128727317/12500000000000000000)
  directionLo := (438099290389204980279/100000000000000000000)
  directionHi := (10952482259730124507/2500000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree078.table
  base := (10944050747573174782874973566881407615493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-7178890712890142863794487063989908296000000000000)
      constant := (148942335822454784282054107846957326482994263063077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree078.table
  base := (10944049921058541060385008301688657203139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-7186502589481146076314961061253402796000000000000)
      constant := (149255450680859416885470901093479009354920732535971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438099290389204980279/100000000000000000000)
  centralHi := (10952482259730124507/2500000000000000000)
  directionLo := (27558432131535438939/6250000000000000000)
  directionHi := (17637396564182680921/4000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree079.table
  base := (11969909927626240737574626218420587840653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-7270846085635918595766182424777672366000000000000)
      constant := (152875427263962742318394339424172074387681677606317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree079.table
  base := (5984954612087961211365437525558252583609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-3639277775194172463197946634079964808000000000000)
      constant := (76598309292586302533787061701098357347339071315801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27558432131535438939/6250000000000000000)
  centralHi := (17637396564182680921/4000000000000000000)
  directionLo := (221876209130946960817/50000000000000000000)
  directionHi := (88750483652378784327/20000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree080.table
  base := (104192233330232884231849878301857152621/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-7362801458381694327737877785565436436000000000000)
      constant := (156860478913715349157809646940632134287222158833625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree080.table
  base := (3256007141899027724300196494440261323291/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-1842652127823885944119206368766614109000000000000)
      constant := (39297462383689881469870678830167534142117236258299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221876209130946960817/50000000000000000000)
  centralHi := (88750483652378784327/20000000000000000000)
  directionLo := (55819018229418763871/12500000000000000000)
  directionHi := (446552145835350110969/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree081.table
  base := (7053204124219895651494995950368893004769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-3727378415563735029854786573176600253000000000000)
      constant := (80448745372406655042987015816845921674297085703041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree081.table
  base := (1410640773894495207364795035979989842427/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-3731330736101371313278878840986491628000000000000)
      constant := (80617571751530388046928311393119113545095555699015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55819018229418763871/12500000000000000000)
  centralHi := (446552145835350110969/100000000000000000000)
  directionLo := (449334429113809106603/100000000000000000000)
  directionHi := (112333607278452276651/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree082.table
  base := (3804261748409411266987377365085839262951/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-1886678050968311447920317126785241144000000000000)
      constant := (41246615683671764834036896160446980991110788692039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree082.table
  base := (1521704656006599339723702149226317102709/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-3777357216554970738319344944439755038000000000000)
      constant := (82666250233898100396067696430419808807083740278505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449334429113809106603/100000000000000000000)
  centralHi := (112333607278452276651/25000000000000000000)
  directionLo := (28256224385073941083/6250000000000000000)
  directionHi := (452099590161183057329/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree083.table
  base := (8177972625215799191485999418808291209247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-3819333788309510761826481933964364323000000000000)
      constant := (84563697432198726825100703706323047617216621894783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree083.table
  base := (8177972440744351913191760518874035025067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-3823383697008570163359811047893018448000000000000)
      constant := (84740960205136545870849916466633572627102981210763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28256224385073941083/6250000000000000000)
  centralHi := (452099590161183057329/100000000000000000000)
  directionLo := (454847941251564461459/100000000000000000000)
  directionHi := (22742397062578223073/5000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree084.table
  base := (8761551445863500720840248992455321184621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-3865311474682398627812329614358246358000000000000)
      constant := (86660143559025050534358024065607626114679576918669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree084.table
  base := (4380775644449099716830288630435923091493/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-1934705088731084794200138575673140929000000000000)
      constant := (43420850828701725616921326632778738235065414827077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454847941251564461459/100000000000000000000)
  centralHi := (22742397062578223073/5000000000000000000)
  directionLo := (1429936829002638469/312500000000000000)
  directionHi := (457579785280844310081/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree085.table
  base := (18718519810852293573072835625041284884811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-7822578322110572987596354589504256786000000000000)
      constant := (177565139482304710723343478139680255032847887521579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree085.table
  base := (18718519543746367028331461790883744372193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-7830873315831538026881486509599090536000000000000)
      constant := (177936949168236033249963075295736190364593082389377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1429936829002638469/312500000000000000)
  centralHi := (457579785280844310081/100000000000000000000)
  directionLo := (18411816646253700103/4000000000000000000)
  directionHi := (28768463509771406411/6250000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree086.table
  base := (9971097959135629982276108677345023395267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-3957266847428174359784024975146010428000000000000)
      constant := (90930975972981964671313055783462018368005136038563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree086.table
  base := (19942195691019119678701612917125905927627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-7922926276738736876962418716505617356000000000000)
      constant := (182242557959515293971634883010585978199971103602603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18411816646253700103/4000000000000000000)
  centralHi := (28768463509771406411/6250000000000000000)
  directionLo := (7234298736966707211/1562500000000000000)
  directionHi := (92599023833173852301/20000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree087.table
  base := (21194131138827167070296093438571259066407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-8006489067602124451539745311079784926000000000000)
      constant := (186210724499628694234414222258374686302181476486023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree087.table
  base := (4238826189098803565429063790834234649337/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-8014979237645935727043350923412144176000000000000)
      constant := (186600229679375195396096990927333814591760897043965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7234298736966707211/1562500000000000000)
  centralHi := (92599023833173852301/20000000000000000000)
  directionLo := (465679171327529341307/100000000000000000000)
  directionHi := (116419792831882335327/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree088.table
  base := (22474325409432142755362985788211347738229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-8098444440347900183511440671867548996000000000000)
      constant := (190611457135409268347414689919383001780144224504981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree088.table
  base := (22474325244965462776933555698830139920789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-8107032198553134577124283130318670996000000000000)
      constant := (191009964320036337137397401307660200204292372816821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465679171327529341307/100000000000000000000)
  centralHi := (116419792831882335327/25000000000000000000)
  directionLo := (117086960430370771497/25000000000000000000)
  directionHi := (468347841721483085989/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree089.table
  base := (5945694669282350411687933714018567016227/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-2047599953273418978870784008163828266500000000000)
      constant := (48766037461670725790949328785131663551374103328003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree089.table
  base := (2972847317153493610480171465794839179709/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-2049771289865083356801303834306299454000000000000)
      constant := (48867940468742481334170681481334204218053173417402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117086960430370771497/25000000000000000000)
  centralHi := (468347841721483085989/100000000000000000000)
  directionLo := (471001391804788959287/100000000000000000000)
  directionHi := (58875173975598619911/12500000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree090.table
  base := (50238981794935573001663246003689455977/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-2070588796459862911863707848360769284000000000000)
      constant := (49892200656972639918303747967251131838646451969125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree090.table
  base := (12559745389235021226194101271145982771147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-4145569060183766138643073772065862318000000000000)
      constant := (99992811169348462241819391887627168669762447763883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471001391804788959287/100000000000000000000)
  centralHi := (58875173975598619911/12500000000000000000)
  directionLo := (118410018927592563861/25000000000000000000)
  directionHi := (94728015142074051089/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree091.table
  base := (13242231016569000206807592184373923352879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-4187155279292613689713263377115420603000000000000)
      constant := (102062707737183178134952882781181703723061214418831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree091.table
  base := (26484461931927166070767548524725664966799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-8383191081274731127367079751038251456000000000000)
      constant := (204551545706619575313844111447818725236933084905711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118410018927592563861/25000000000000000000)
  centralHi := (94728015142074051089/20000000000000000000)
  directionLo := (238132070265536795807/50000000000000000000)
  directionHi := (95252828106214718323/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree092.table
  base := (1742355753301760762825156116479699288707/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-2116566482832750777849555528754651319000000000000)
      constant := (52183497095548611586119381254389708025677443562892) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree092.table
  base := (27877691966751259808646513702695088416327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-8475244042181929977448011957944778276000000000000)
      constant := (209169531974880035215769901373010973432155673876903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238132070265536795807/50000000000000000000)
  centralHi := (95252828106214718323/20000000000000000000)
  directionLo := (59859228323714731243/12500000000000000000)
  directionHi := (95774765317943569989/20000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree093.table
  base := (29299180930263301971108105148905273179027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-8558221304076778843369917475806369346000000000000)
      constant := (213394521348088891835400270006944563542424522137203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree093.table
  base := (29299180857062231319280873975709454432999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-8567297003089128827528944164851305096000000000000)
      constant := (213839581140241753065259510071122220146859639677511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59859228323714731243/12500000000000000000)
  centralHi := (95774765317943569989/20000000000000000000)
  directionLo := (240734683847984454641/50000000000000000000)
  directionHi := (481469367695968909283/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree094.table
  base := (15374464321699451429436275378730097398633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-4325088338411277287670806418297066708000000000000)
      constant := (109053507184646410240819101318301044259093272278537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree094.table
  base := (7687232145287955381279928667229041581951/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-2164837490999081919402469092939457979000000000000)
      constant := (54640423299997476268748702195358199622198543683039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240734683847984454641/50000000000000000000)
  centralHi := (481469367695968909283/100000000000000000000)
  directionLo := (60506373923852159069/12500000000000000000)
  directionHi := (484050991390817272553/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree095.table
  base := (8056733793435994357489132654860291441701/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-2185533012392082576828327049345474371500000000000)
      constant := (55717866860873439398106822158283561089402700350789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree095.table
  base := (32226935120815288599407113968227850176777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-8751402924903526527690808578664358736000000000000)
      constant := (223335868151847815534744775394148988473676291286953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60506373923852159069/12500000000000000000)
  centralHi := (484050991390817272553/100000000000000000000)
  directionLo := (486618919179382096421/100000000000000000000)
  directionHi := (243309459589691048211/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree096.table
  base := (33733200505792499518622153950304331860767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-8834087422314106039285003558169661556000000000000)
      constant := (227687880568752527459059718067088167552993940168063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree096.table
  base := (16866600230395153083065146756893291797779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-4421727942905362688885870392785442778000000000000)
      constant := (114081052996953392853487014995058350107758133074931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486618919179382096421/100000000000000000000)
  centralHi := (243309459589691048211/50000000000000000000)
  directionLo := (19566934670108630059/4000000000000000000)
  directionHi := (122293341688178937869/25000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree097.table
  base := (7053544925309189188572984586689350432939/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-8926042795059881771256698918957425626000000000000)
      constant := (232556253743443541414639354445817878597676400540855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree097.table
  base := (35267724588285811623732841363581366593507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-8935508846717924227852672992477412376000000000000)
      constant := (233040406724567171838964917087194540423105656137923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19566934670108630059/4000000000000000000)
  centralHi := (122293341688178937869/25000000000000000000)
  directionLo := (3841519876556543053/781250000000000000)
  directionHi := (98342908839847502157/20000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree098.table
  base := (18415253762556122761417521906582791092639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-4508999083902828751614197139872594848000000000000)
      constant := (118738293483102321301631277732739894461739185001471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree098.table
  base := (18415253746293167567062291066746571151037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-4513780903812561538966802599691969598000000000000)
      constant := (118985385171244451374185483307962100564650829040093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3841519876556543053/781250000000000000)
  centralHi := (98342908839847502157/20000000000000000000)
  directionLo := (247121328103191473087/50000000000000000000)
  directionHi := (19769706248255317847/4000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree099.table
  base := (4802693649046109528170012121140243549551/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-2277488385137858308800022410133238441500000000000)
      constant := (60612220058973743270267384319865186250097288478878) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree099.table
  base := (9605387291179919740645469338769950053369/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-2279903692133080482003634351572616504000000000000)
      constant := (60738299211637479992820170698305392341979849868441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247121328103191473087/50000000000000000000)
  centralHi := (19769706248255317847/4000000000000000000)
  directionLo := (99351580450603360173/20000000000000000000)
  directionHi := (248378951126508400433/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree100.table
  base := (5005106202584977549989758265667425323507/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-2300477228324302241792946250330179459000000000000)
      constant := (61868283387889894095672758987259362309806890215846) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree100.table
  base := (40040849597177775389955369222569463355403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-9211667729439520778095469613196992836000000000000)
      constant := (247987686235811268395359851417218652954230924569067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99351580450603360173/20000000000000000000)
  centralHi := (248378951126508400433/50000000000000000000)
  directionLo := (499260476793121229559/100000000000000000000)
  directionHi := (12481511919828030739/2500000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree101.table
  base := (2084420440182887299148797588703653284771/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-2323466071510746174785870090527120476500000000000)
      constant := (63137336728099914006047074755283518880445663710095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree101.table
  base := (20844204391841095893460763622183275436051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-4651860345173359814088200910051759828000000000000)
      constant := (126537119254743885222132172674480294875878790237939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499260476793121229559/100000000000000000000)
  centralHi := (12481511919828030739/2500000000000000000)
  directionLo := (501750569431238103939/100000000000000000000)
  directionHi := (25087528471561905197/5000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree102.table
  base := (43364226735964170774947594342840539690013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-9385819658788760431115175722896245976000000000000)
      constant := (257677520317747584149645485368143516689117244183357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree102.table
  base := (43364226718987125732893196583874307499411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-9395773651253918478257334027010046476000000000000)
      constant := (258212853666923388747880571924618711048105207460979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (501750569431238103939/100000000000000000000)
  centralHi := (25087528471561905197/5000000000000000000)
  directionLo := (504228365090113347399/100000000000000000000)
  directionHi := (2521141825450566737/500000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree103.table
  base := (45068303413141531306727073636358936816763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-9477775031534536163086871083684010046000000000000)
      constant := (262857653767045900149431141323568914588137667414107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree103.table
  base := (1802732135948555390381245424570154169741/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-9487826612161117328338266233916573296000000000000)
      constant := (263403531707570526263629876907693017950975718058725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504228365090113347399/100000000000000000000)
  centralHi := (2521141825450566737/500000000000000000)
  directionLo := (253347022085481391629/50000000000000000000)
  directionHi := (506694044170962783259/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree104.table
  base := (9360127766294410810084200225863316106767/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-9569730404280311895058566444471774116000000000000)
      constant := (268089747259829661165929192471956327384788752310315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree104.table
  base := (2340031940960590535455178951850371778549/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-2394969893267079044604799610205775029000000000000)
      constant := (67161568157743158386948161082721362171426795507305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253347022085481391629/50000000000000000000)
  centralHi := (506694044170962783259/100000000000000000000)
  directionLo := (254573891353376285057/50000000000000000000)
  directionHi := (101829556541350514023/20000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree105.table
  base := (24280616493929572703196186463275633417577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-4830842888513043813515130902629769093000000000000)
      constant := (136686900397855804392964182260342880136978503238153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree105.table
  base := (48561232977441418154734150294957227291137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-9671932533975515028500130647729626936000000000000)
      constant := (273941076436749594106060767675783765276886447448993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254573891353376285057/50000000000000000000)
  centralHi := (101829556541350514023/20000000000000000000)
  directionLo := (51158975250886278763/10000000000000000000)
  directionHi := (511589752508862787631/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree106.table
  base := (12587521469931925901930661556190433087307/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 111302500000000000000000000000000000000000000
      center := (1691798)
      previous := (845899)
      next := (845899)
      square := (7770227192557706056216804173185000000000000)
      linear := (-868070590047335649608575753475196000000000000)
      constant := (24805074259021867399282202509981464021479994947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree106.table
  base := (50350085870876195185375596591041383164937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6767192)
      previous := (3383596)
      next := (3383596)
      square := (31080908770230824224867216692740000000000000)
      linear := (-3475964932318516866707391546684284000000000000)
      constant := (99426110047912226290454348185380417419886160177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51158975250886278763/10000000000000000000)
  centralHi := (511589752508862787631/100000000000000000000)
  directionLo := (257010060653739986199/50000000000000000000)
  directionHi := (514020121307479972399/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree107.table
  base := (52167197504940331825059521270185213263287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-9845596522517639090973652526835066326000000000000)
      constant := (284097787995536639347879562308173838729312694680343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree107.table
  base := (52167197497420084311143350389324015948639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-9856038455789912728661995061542680576000000000000)
      constant := (284686872694218050300669546776704799256964643585471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257010060653739986199/50000000000000000000)
  centralHi := (514020121307479972399/100000000000000000000)
  directionLo := (25821952644302162347/5000000000000000000)
  directionHi := (516439052886043246941/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree108.table
  base := (27006283930863457616797113233074108026031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-4968775947631707411472673943811415198000000000000)
      constant := (144768860829495525439550329870077193012866235558159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree108.table
  base := (54012567855338139025516571637867319674941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-9948091416697111578742927268449207396000000000000)
      constant := (290137865145430442534862784422951309976347767565149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25821952644302162347/5000000000000000000)
  centralHi := (516439052886043246941/100000000000000000000)
  directionLo := (259423353605024503953/50000000000000000000)
  directionHi := (518846707210049007907/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree109.table
  base := (13971549237156357650833107567377852263271/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-2507376817002297638729260812102648616500000000000)
      constant := (73757403841137524203487224780602946340274664728519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree109.table
  base := (2235447877727930100257582885402031982757/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-10040144377604310428823859475355734216000000000000)
      constant := (295640920478043521805106278695435136642131180779325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259423353605024503953/50000000000000000000)
  centralHi := (518846707210049007907/100000000000000000000)
  directionLo := (521243240550500825949/100000000000000000000)
  directionHi := (10424864811010016519/2000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree110.table
  base := (14447021191108049409494764231207225943081/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-2530365660188741571722184652299589634000000000000)
      constant := (75143367278015811377412562421938421238299252945609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree110.table
  base := (14447021189955547866851664667033666503941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-2533049334627877319726197920565565259000000000000)
      constant := (75299009672977484714666709251345068218779277946149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521243240550500825949/100000000000000000000)
  centralHi := (10424864811010016519/2000000000000000000)
  directionLo := (65453600700284269197/12500000000000000000)
  directionHi := (523628805602274153577/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree111.table
  base := (29859115654080033660889580729983178637813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-5106709006750371009430216984993061303000000000000)
      constant := (153084641450703522307363772534370922317665609857557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree111.table
  base := (29859115652122225340371812952559496328423/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-5112125149709354064492861944584393928000000000000)
      constant := (153401609893454474052572347287742866268429956555847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65453600700284269197/12500000000000000000)
  centralHi := (523628805602274153577/100000000000000000000)
  directionLo := (526003551597649541403/100000000000000000000)
  directionHi := (131500887899412385351/25000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree112.table
  base := (3854789786187705171117216483580489669401/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-2576343346561629437708032332693471669000000000000)
      constant := (77954264183120181645225099581358416181700271984356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree112.table
  base := (12335327315135536179623285845734290515697/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-10316303260325906979066656096075314676000000000000)
      constant := (312462463762942084049878661684604734280353066494165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526003551597649541403/100000000000000000000)
  centralHi := (131500887899412385351/25000000000000000000)
  directionLo := (528367624415253239159/100000000000000000000)
  directionHi := (13209190610381330979/2500000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree113.table
  base := (63663300576307949570525155815333160259753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-10397328758992293482803824691561650746000000000000)
      constant := (317516790605202515719182009241244993726089817446217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree113.table
  base := (63663300573483642084925482678526447663203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-10408356221233105829147588302981841496000000000000)
      constant := (318173770619929528720282371792934888100745411283267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528367624415253239159/100000000000000000000)
  centralHi := (13209190610381330979/2500000000000000000)
  directionLo := (132680291671157556063/25000000000000000000)
  directionHi := (530721166684630224253/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree114.table
  base := (65678223299547222978049941462033559141593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-10489284131738069214775520052349414816000000000000)
      constant := (323268484519506525082889804187002685246098899225977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree114.table
  base := (32839111648574400590546045566530895561457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-5250204591070152339614260254944184158000000000000)
      constant := (161968570178903529967138888494389665233628180515473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132680291671157556063/25000000000000000000)
  centralHi := (530721166684630224253/100000000000000000000)
  directionLo := (66633039735832722917/12500000000000000000)
  directionHi := (533064317886661783337/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree115.table
  base := (67721404748300459906105117076060126006361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-10581239504483844946747215413137178886000000000000)
      constant := (329072138475340149266596035300468086662881117409529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree115.table
  base := (67721404746263834127223921376392373053897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-10592462143047503529309452716794895136000000000000)
      constant := (329752572976523487834161866429641742852617728278633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66633039735832722917/12500000000000000000)
  centralHi := (533064317886661783337/100000000000000000000)
  directionLo := (535397214450027703067/100000000000000000000)
  directionHi := (133849303612506925767/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree116.table
  base := (6979284492223570554788586558280546895789/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-5336597438614810339359455386962471478000000000000)
      constant := (167463876236330937085895299217776161335139542959105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree116.table
  base := (69792844920506409950684233556609104009273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-10684515103954702379390384923701421956000000000000)
      constant := (335620068476038501873207816447016438856147532641497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535397214450027703067/100000000000000000000)
  centralHi := (133849303612506925767/25000000000000000000)
  directionLo := (67214998730487730297/12500000000000000000)
  directionHi := (537719989843901842377/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree117.table
  base := (71892543821094983194902953050136273499447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-10765150249975396410690606134712707026000000000000)
      constant := (340835326511439437363135928034701340277455083602583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree117.table
  base := (71892543819626733895699856064511851875199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-10776568064861901229471317130607948776000000000000)
      constant := (341539626856320862846903754399547542256956078713311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67214998730487730297/12500000000000000000)
  centralHi := (537719989843901842377/100000000000000000000)
  directionLo := (540032774667059302853/100000000000000000000)
  directionHi := (270016387333529651427/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree118.table
  base := (9252562680585242652214604119212956101077/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-2714276405680293035665575373875117774000000000000)
      constant := (86698715147912070801547499263297085285110243939306) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree118.table
  base := (37010250721717704964729504568647972559019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-5434310512884550039776124668757237798000000000000)
      constant := (173755624058673442492083805938459079813116938481291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540032774667059302853/100000000000000000000)
  centralHi := (270016387333529651427/50000000000000000000)
  directionLo := (271167848366781766661/50000000000000000000)
  directionHi := (542335696733563533323/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree119.table
  base := (76176717792851481937401863402317113524339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-10949060995466947874633996856288235166000000000000)
      constant := (352806354713270265859371278647104050058558824402771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree119.table
  base := (4761044861987078312472023497397614054569/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-2740168496669074732408295386105250604000000000000)
      constant := (88383733064774790468367160374801310853684469020964) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271167848366781766661/50000000000000000000)
  centralHi := (542335696733563533323/100000000000000000000)
  directionLo := (108925776231038490179/20000000000000000000)
  directionHi := (34039305072199528181/6250000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree120.table
  base := (19590298216375264212512849218374205967559/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-2760254092053180901651423054268999809000000000000)
      constant := (89717452219073140164795873243396005439083679117351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree120.table
  base := (61219681925470890848821695957027381801/7812500000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-2763181736895874444928528437831882309000000000000)
      constant := (89902669820391374340208952880222554884653107100480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108925776231038490179/20000000000000000000)
  centralHi := (34039305072199528181/6250000000000000000)
  directionLo := (273456225210376994529/50000000000000000000)
  directionHi := (546912450420753989059/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree121.table
  base := (10071740832820420357135916007362588478881/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-2783242935239624834644346894465940826500000000000)
      constant := (91246305770176687678627586389044702317584790303618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree121.table
  base := (16114785332360168035147538114912564799997/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-11144779908490696629795045958234056056000000000000)
      constant := (365738489184738008744763966706140347058835060107665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273456225210376994529/50000000000000000000)
  centralHi := (546912450420753989059/100000000000000000000)
  directionLo := (109837304894486670503/20000000000000000000)
  directionHi := (137296631118108338129/25000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree122.table
  base := (3312596767360008654089910238282992339411/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-11224927113704275070549082938651527376000000000000)
      constant := (371152597326508060803064545855477992490941355524475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree122.table
  base := (5175932448959562454198161577420594008871/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-2809208217349473869968994541285145719000000000000)
      constant := (92979590492153093698672735899251400957303474907676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109837304894486670503/20000000000000000000)
  centralHi := (137296631118108338129/25000000000000000000)
  directionLo := (275725610389653315307/50000000000000000000)
  directionHi := (110290244155861326123/20000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree123.table
  base := (21271042607449354374333769039526406771823/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-2829220621612512700630194574859822861500000000000)
      constant := (94342982903423678775084304695738410682702823978447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree123.table
  base := (3403366817169924108245511068194278663053/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-11328885830305094329956910372047109696000000000000)
      constant := (378150297633187205492573568996237981801125283997925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275725610389653315307/50000000000000000000)
  centralHi := (110290244155861326123/20000000000000000000)
  directionLo := (138426663602037065341/25000000000000000000)
  directionHi := (110741330881629652273/20000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree124.table
  base := (17476336079992089370879450655153162071187/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-11408837859195826534492473660227055516000000000000)
      constant := (383643225942267399002617515586694249550784139217215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree124.table
  base := (8738168039949425251712657559911489738927/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-5710469395606146590018921289476818258000000000000)
      constant := (192217148089231757036727045728865265971894770141515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138426663602037065341/25000000000000000000)
  centralHi := (110741330881629652273/20000000000000000000)
  directionLo := (277976469045826556927/50000000000000000000)
  directionHi := (111190587618330622771/20000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree125.table
  base := (89707449094510861631923645452169620193169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-11500793231941602266464169021014819586000000000000)
      constant := (389966480312228808443383381857890611923931796430641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree125.table
  base := (44853724547057616668697360600712346489561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-5756495876059746015059387392930081668000000000000)
      constant := (195385178802222137515957007108562726025475442494329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277976469045826556927/50000000000000000000)
  centralHi := (111190587618330622771/20000000000000000000)
  directionLo := (558190182294187638711/100000000000000000000)
  directionHi := (69773772786773454839/12500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree126.table
  base := (46030738256741639951481760028043819888693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-5796374302343688999217932190901291828000000000000)
      constant := (198170847361791636370580261822752776770387983457877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree126.table
  base := (9206147651314755573000535409646423807473/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-5802522356513345440099853496383345078000000000000)
      constant := (198579240955567027180156557955338859808200038806485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558190182294187638711/100000000000000000000)
  centralHi := (69773772786773454839/12500000000000000000)
  directionLo := (22416739811007143853/4000000000000000000)
  directionHi := (280209247637589298163/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree127.table
  base := (47221881328461429449577798165217193872627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-5842351988716576865203779871295173863000000000000)
      constant := (201384434588168219618131166905336215486349663707603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree127.table
  base := (18888752531327596946159412794160684667553/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-11697097673933889730280639199673216976000000000000)
      constant := (403598669098538700470136437251070435329071565302085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22416739811007143853/4000000000000000000)
  centralHi := (280209247637589298163/50000000000000000000)
  directionLo := (562637983150242285623/100000000000000000000)
  directionHi := (70329747893780285703/12500000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree128.table
  base := (96854307524883188410414621079020234794967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-11776659350178929462379255103378111796000000000000)
      constant := (409248003670495009840431167942240152432118592791863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree128.table
  base := (2421357688116036899470081537814187480241/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-2947287658710272145090392851644935949000000000000)
      constant := (102522729791666271521379791258221920344291370568490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562637983150242285623/100000000000000000000)
  centralHi := (70329747893780285703/12500000000000000000)
  directionLo := (112969749990030387697/20000000000000000000)
  directionHi := (282424374975075969243/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree129.table
  base := (49646555558712266437103709012480144972471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-5934307361462352597175475232082937933000000000000)
      constant := (207889549103033260596710749734737285470528142327319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree129.table
  base := (9929311111721945413731306947152733690863/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-5940601797874143715221251806743135308000000000000)
      constant := (208317616057760446471732117003237038891162053745035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112969749990030387697/20000000000000000000)
  centralHi := (282424374975075969243/50000000000000000000)
  directionLo := (35440681104858499671/6250000000000000000)
  directionHi := (567050897677735994737/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree130.table
  base := (50880086717306183149085908266771323365339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-5980285047835240463161322912476819968000000000000)
      constant := (211181076391529580720585648714933904907423055651771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree130.table
  base := (101760173434438378705267292435456642383491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-11973256556655486280523435820392797436000000000000)
      constant := (423231607945114432434948377234825459858135126496099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35440681104858499671/6250000000000000000)
  centralHi := (567050897677735994737/100000000000000000000)
  directionLo := (569244526362795309721/100000000000000000000)
  directionHi := (284622263181397654861/50000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree131.table
  base := (104255494476516153042386183082750106574109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-12052525468416256658294341185741404006000000000000)
      constant := (428997167401481617761055674335111127950103612170301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree131.table
  base := (104255494476368551058780779110244253519309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-12065309517562685130604368027299324256000000000000)
      constant := (429880046655454496414144514502412596961311235173101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569244526362795309721/100000000000000000000)
  centralHi := (284622263181397654861/50000000000000000000)
  directionLo := (571429734115122952081/100000000000000000000)
  directionHi := (285714867057561476041/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree132.table
  base := (26694768560802083739869928746135969288143/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-3036120210290508097566509136632292019000000000000)
      constant := (108921035515335737423536662726879641891694857338927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree132.table
  base := (53389537121541561956592701093547286840519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-6078681239234941990342650117102925538000000000000)
      constant := (218290274123275116661125506136705283285611730634791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (571429734115122952081/100000000000000000000)
  centralHi := (285714867057561476041/50000000000000000000)
  directionLo := (35850413573481631629/6250000000000000000)
  directionHi := (114721323435141221213/20000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree133.table
  base := (27332728183690872919034597454849032725413/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-3059109053476952030559432976829233036500000000000)
      constant := (110605769190663121032611846566692358732096927093957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree133.table
  base := (21866182546931456115621894316367993426623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-12249415439377082830766232441112377896000000000000)
      constant := (443333112718411045545551315765826997172444156878235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35850413573481631629/6250000000000000000)
  centralHi := (114721323435141221213/20000000000000000000)
  directionLo := (575775269966185684407/100000000000000000000)
  directionHi := (71971908745773210551/12500000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree134.table
  base := (55955504975628823043446923594989594173047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-6164195793326791927104713634052348108000000000000)
      constant := (224606985752709864227150154077953046737098635392983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree134.table
  base := (55955504975583778288779572283139626243337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-6170734200142140840423582324009452358000000000000)
      constant := (225068870035523252288783991120463341565642714874793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (575775269966185684407/100000000000000000000)
  centralHi := (71971908745773210551/12500000000000000000)
  directionLo := (577935785136645569559/100000000000000000000)
  directionHi := (14448394628416139239/2500000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree135.table
  base := (11451936589276769157888703288845463916353/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-6210173479699679793090561314446230143000000000000)
      constant := (228028413144827149456704371213336485907360224618085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree135.table
  base := (114519365892691280579970065075804668423043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-12433521361191480530928096854925431536000000000000)
      constant := (456994430304466281102060623758655726831800193405027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (577935785136645569559/100000000000000000000)
  centralHi := (14448394628416139239/2500000000000000000)
  directionLo := (580088253611799918729/100000000000000000000)
  directionHi := (58008825361179991873/10000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree136.table
  base := (117155980559370921247877144466486479980677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-12512302332145135318152817989680224356000000000000)
      constant := (462951641115365861742831562391931220467792195494053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree136.table
  base := (58577990279653057630556433510881073698891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-6262787161049339690504514530915979178000000000000)
      constant := (231951591709340043786787744238586560944554648326699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580088253611799918729/100000000000000000000)
  centralHi := (58008825361179991873/10000000000000000000)
  directionLo := (291116382317821839579/50000000000000000000)
  directionHi := (582232764635643679159/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree137.table
  base := (4792834158045785700529334995395283671311/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-12604257704890911050124513350467988426000000000000)
      constant := (469898415982564084968930988025701807526854940501975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree137.table
  base := (23964170790217936363204785179004107932327/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-12617627283005878231089961268738485176000000000000)
      constant := (470863999413697631259099394851779050881588306004515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291116382317821839579/50000000000000000000)
  centralHi := (582232764635643679159/100000000000000000000)
  directionLo := (146092351453657087983/25000000000000000000)
  directionHi := (584369405814628351933/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree138.table
  base := (1531424825852073289841274502935235557599/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-3174053269409171695524052177813938124000000000000)
      constant := (119224287722814649787342011876155183074309220138220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree138.table
  base := (15314248258514906804710415644150833096869/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-3177420060978269270292723368911252999000000000000)
      constant := (119469219572382144007429829876715419254037449279882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146092351453657087983/25000000000000000000)
  centralHi := (584369405814628351933/100000000000000000000)
  directionLo := (4582017680932985191/781250000000000000)
  directionHi := (586498263159422104449/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree139.table
  base := (25047075382102207456340921217916197245891/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-12788168450382462514067904072043516566000000000000)
      constant := (483947845841458965583768151388991374857221679048495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree139.table
  base := (15654422113808939158511940176711394808091/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-3200433301205068982812956420637884704000000000000)
      constant := (121235455011545627866202696805678010130104227050998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4582017680932985191/781250000000000000)
  centralHi := (586498263159422104449/100000000000000000000)
  directionLo := (294309710562655276419/50000000000000000000)
  directionHi := (588619421125310552839/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree140.table
  base := (25597005295651172141304140694936863752061/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-12880123823128238246039599432831280636000000000000)
      constant := (491050500833174650763965218269895927380476856784145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree140.table
  base := (127985026478222346167446461025244555383059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-12893786165727474781332757889458065636000000000000)
      constant := (492058824683668928061389955894688800236237557796851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294309710562655276419/50000000000000000000)
  centralHi := (588619421125310552839/100000000000000000000)
  directionLo := (295366481325645953257/50000000000000000000)
  directionHi := (118146592530258381303/20000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree141.table
  base := (26152586954295021718813145008947234707547/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-12972079195874013978011294793619044706000000000000)
      constant := (498205115866415006029796528544313056219694461317415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree141.table
  base := (32690733692861672798593519262371028097429/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-3246459781658668407853422524091148114000000000000)
      constant := (124806973050499299383694184366873503955019112953781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295366481325645953257/50000000000000000000)
  centralHi := (118146592530258381303/20000000000000000000)
  directionLo := (592838969197917678491/100000000000000000000)
  directionHi := (148209742299479419623/25000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree142.table
  base := (133569101790242507304323276469610209180291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-13064034568619789709982990154406808776000000000000)
      constant := (505411690941189251562167461985694663816270301331299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree142.table
  base := (26713820358043682598315429884314835768737/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-13077892087541872481494622303271119276000000000000)
      constant := (506449022601176557359442208940742793933785856976965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (592838969197917678491/100000000000000000000)
  centralHi := (148209742299479419623/25000000000000000000)
  directionLo := (59493752078392780873/10000000000000000000)
  directionHi := (594937520783927808731/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree143.table
  base := (5456141101385225411349850036895214088391/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-13155989941365565441954685515194572846000000000000)
      constant := (512670226057506463984503831276836963980244482304975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree143.table
  base := (136403527534610207365096826988363619681979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-13169945048449071331575554510177646096000000000000)
      constant := (513722215881216098835742319502194992886618636248731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59493752078392780873/10000000000000000000)
  centralHi := (594937520783927808731/100000000000000000000)
  directionLo := (191049182726952581/32000000000000000)
  directionHi := (298514348010863407813/50000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree144.table
  base := (69633106002355423943268929777847962878839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-6623972657055670586963190437991168458000000000000)
      constant := (259990360607687783480469852003324691029318574253271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree144.table
  base := (139266212004693529265522540665779177993811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-13261998009356270181656486717084172916000000000000)
      constant := (521047472042124758083284303630997213130746048822579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191049182726952581/32000000000000000)
  centralHi := (298514348010863407813/50000000000000000000)
  directionLo := (599112572151745475471/100000000000000000000)
  directionHi := (37444535759484092217/6250000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree145.table
  base := (28431431040110644411155635379742085377249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-13339900686857116905898076236770100986000000000000)
      constant := (527343176414805324278167356381829769996615660828805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree145.table
  base := (142157155200538540152764051159211279427999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-13354050970263469031737418923990699736000000000000)
      constant := (528424791083911309458391969987077860843301767232511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (599112572151745475471/100000000000000000000)
  centralHi := (37444535759484092217/6250000000000000000)
  directionLo := (75148653134466315559/12500000000000000000)
  directionHi := (601189225075730524473/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree146.table
  base := (145076357122226517424537893391244537898043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-13431856059602892637869771597557865056000000000000)
      constant := (534757591655804334980762436449659287574570391680027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree146.table
  base := (72538178561107035688082974062670610341183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-6723051965585333940909175565448613278000000000000)
      constant := (267927086503292180487220766718908092212586461635487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75148653134466315559/12500000000000000000)
  centralHi := (601189225075730524473/100000000000000000000)
  directionLo := (301629364694501488061/50000000000000000000)
  directionHi := (603258729389002976123/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree147.table
  base := (148023817769798150954327342559975624236989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-13523811432348668369841466958345629126000000000000)
      constant := (542223966938381030199481359189203773982783859238621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree147.table
  base := (148023817769787600748197472890836207466949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-13538156892077866731899283337803753376000000000000)
      constant := (543335617810152351372179235131742866695514626329061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301629364694501488061/50000000000000000000)
  centralHi := (603258729389002976123/100000000000000000000)
  directionLo := (605321158411723842557/100000000000000000000)
  directionHi := (302660579205861921279/50000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree148.table
  base := (75499768571667091348308805464599171077079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-6807883402547222050906581159566696598000000000000)
      constant := (274871151131271835685302206189733152508723079352631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree148.table
  base := (150999537143325239949198765241102797375881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-13630209852985065581980215544710280196000000000000)
      constant := (550869125494623548544565344296609421404298218784809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605321158411723842557/100000000000000000000)
  centralHi := (302660579205861921279/50000000000000000000)
  directionLo := (303688292109602168103/50000000000000000000)
  directionHi := (607376584219204336207/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree149.table
  base := (154003515242899310656837471321624458260613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-13707722177840219833784857679921157266000000000000)
      constant := (557312597628300349593629837575552301805224090606757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree149.table
  base := (19250439405361466348320005694023062356261/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-3430565703473066108015286937904201754000000000000)
      constant := (139613674015001512267237254579060309389728273221258) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303688292109602168103/50000000000000000000)
  centralHi := (607376584219204336207/100000000000000000000)
  directionLo := (152356269417824000591/25000000000000000000)
  directionHi := (121885015534259200473/20000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree150.table
  base := (157035752068556873071055960865626435799421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-13799677550585995565756553040708921336000000000000)
      constant := (564934853035658985915994589929458052000966896755869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree150.table
  base := (157035752068550448655909268477763108575407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-13814315774799463282142079958523333836000000000000)
      constant := (566092329506307778639922662033742932621491917387023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152356269417824000591/25000000000000000000)
  centralHi := (121885015534259200473/20000000000000000000)
  directionLo := (611466708440894689343/100000000000000000000)
  directionHi := (9554167319388979521/1562500000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree151.table
  base := (16009624762036885668348610442363178542553/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-6945816461665885648864124200748342703000000000000)
      constant := (286304534242313666184127362018811517693362214677085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree151.table
  base := (160096247620363411824192826049410866183663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-13906368735706662132223012165429860656000000000000)
      constant := (573782025833536493230259256826976602746976274928207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611466708440894689343/100000000000000000000)
  centralHi := (9554167319388979521/1562500000000000000)
  directionLo := (12270030900831815919/2000000000000000000)
  directionHi := (613501545041590795951/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree152.table
  base := (163185001898395909846388755271259560649603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-13983588296077547029699943762284449476000000000000)
      constant := (580335243975212973602352674205400146953203859232867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree152.table
  base := (32637000379678259076640605650073337461101/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-13998421696613860982303944372336387476000000000000)
      constant := (581523785041699780835933377076575705289049242186945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12270030900831815919/2000000000000000000)
  centralHi := (613501545041590795951/100000000000000000000)
  directionLo := (307764827427248420933/50000000000000000000)
  directionHi := (615529654854496841867/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree153.table
  base := (41575503725674339864995878386099859493887/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-3518885917205830690417909780768053386500000000000)
      constant := (147028344876855832252528464403392020051089806843743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree153.table
  base := (166302014902693448914076061704137518693759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-14090474657521059832384876579242914296000000000000)
      constant := (589317607130805063685234278321084654396569448029151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307764827427248420933/50000000000000000000)
  centralHi := (615529654854496841867/100000000000000000000)
  directionLo := (12351022083085641621/2000000000000000000)
  directionHi := (617551104154282081051/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree154.table
  base := (42361821658332807733633135726370269247339/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-3541874760392274623410833620964994404000000000000)
      constant := (148985868770316413804923668951446164216614629949771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree154.table
  base := (16944728663332791706439406700949459249941/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-7091263809214129341232904393074720558000000000000)
      constant := (298581746050429800406063884074655967195119723700745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12351022083085641621/2000000000000000000)
  centralHi := (617551104154282081051/100000000000000000000)
  directionLo := (619565958134442617637/100000000000000000000)
  directionHi := (309782979067221308819/50000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree155.table
  base := (86310408545177135247428199216572568272501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-7129727207157437112807514922323870843000000000000)
      constant := (301912765348373524442486933258440516275201587811989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree155.table
  base := (86310408545175731187343620012959262028999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-7137290289667728766273370496527983968000000000000)
      constant := (302530719975935245455463447322257053414663718121511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (619565958134442617637/100000000000000000000)
  centralHi := (309782979067221308819/50000000000000000000)
  directionLo := (310787140465917142257/50000000000000000000)
  directionHi := (124314856186366856903/20000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree156.table
  base := (175822606273821969263378859110707228067491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-14351409787060649957586725205435505756000000000000)
      constant := (611759546353874449697365783987959597146726881972099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree156.table
  base := (87911303136909794902239512699923341057621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-7183316770121328191313836599981247378000000000000)
      constant := (306505725341922337701753312738847207359838801815669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310787140465917142257/50000000000000000000)
  centralHi := (124314856186366856903/20000000000000000000)
  directionLo := (311788067825247201697/50000000000000000000)
  directionHi := (124715227130098880679/20000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree157.table
  base := (44763163545947147163730693797987021745043/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-3610841289951606422389605141555817456500000000000)
      constant := (154936380513163660890420147724320422436379465863027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree157.table
  base := (179052654183786572503026091440881652295489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-14458686501149855232708605406869021576000000000000)
      constant := (621013524296788941662179420317494251212549531345121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311788067825247201697/50000000000000000000)
  centralHi := (124715227130098880679/20000000000000000000)
  directionLo := (125114316876955491717/20000000000000000000)
  directionHi := (312785792192388729293/50000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree158.table
  base := (182310960820307186697871754934756879857067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-14535320532552201421530115927011033896000000000000)
      constant := (627783457793094265887835288789555109737159192058763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree158.table
  base := (182310960820305478449499390854052605988423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-14550739462057054082789537613775548396000000000000)
      constant := (629067660790709926341302661152847732212030520295847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125114316876955491717/20000000000000000000)
  centralHi := (312785792192388729293/50000000000000000000)
  directionLo := (627560688241828681927/100000000000000000000)
  directionHi := (78445086030228585241/12500000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree159.table
  base := (185597526183429644964480978282511239384499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6767192)
      previous := (3383596)
      next := (3383596)
      square := (31080908770230824224867216692740000000000000)
      linear := (-5207289393128507352617234349518974000000000000)
      constant := (226370008392737559615074626929904490138637279979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree159.table
  base := (185597526183428197653993343489806705293179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (6767192)
      previous := (3383596)
      next := (3383596)
      square := (31080908770230824224867216692740000000000000)
      linear := (-5212813251322268755026867148694224000000000000)
      constant := (226832986887011078241019210029193035326357622259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627560688241828681927/100000000000000000000)
  centralHi := (78445086030228585241/12500000000000000000)
  directionLo := (12590870147268371213/2000000000000000000)
  directionHi := (629543507363418560651/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree160.table
  base := (3778247005464133917003490227648480505953/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-7359615639021876442736753324293281018000000000000)
      constant := (322007604699488802670928042658797068972523590950425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree160.table
  base := (18891235027320546966650641159124060333209/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-7367422691935725891475701013794301018000000000000)
      constant := (322666061210753932218767608706934112244381436351005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12590870147268371213/2000000000000000000)
  centralHi := (629543507363418560651/100000000000000000000)
  directionLo := (631520100947160340593/100000000000000000000)
  directionHi := (315760050473580170297/50000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree161.table
  base := (38451086617937589997876258756903270123631/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-14811186650789528617445202009374326106000000000000)
      constant := (652209025264433871317760312590969915507701298422795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree161.table
  base := (192255433089686911187648651529647230650981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-14826898344778650633032334234495128856000000000000)
      constant := (653542447558397368356063590116497785146476821208709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (631520100947160340593/100000000000000000000)
  centralHi := (315760050473580170297/50000000000000000000)
  directionLo := (316745263633565850961/50000000000000000000)
  directionHi := (633490527267131701923/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree162.table
  base := (195626774632921923635330797311465270052327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-14903142023535304349416897370162090176000000000000)
      constant := (660454801171574670304294381212112936560991017880903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree162.table
  base := (9781338731646052180688209658624525518777/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-3729737826421462370778316610350413919000000000000)
      constant := (165451208894072174648910110607316648539228557624765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316745263633565850961/50000000000000000000)
  centralHi := (633490527267131701923/100000000000000000000)
  directionLo := (158863710923480232699/25000000000000000000)
  directionHi := (635454843693920930797/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree163.table
  base := (199026374902956065864508397769813651659267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-14995097396281080081388592730949854246000000000000)
      constant := (668752537120405936258717074195362415040981933134563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree163.table
  base := (199026374902955320381640258210987110936167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-15011004266593048333194198648308182496000000000000)
      constant := (670119286475187789658821678098607923862263356638663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158863710923480232699/25000000000000000000)
  centralHi := (635454843693920930797/100000000000000000000)
  directionLo := (637413106714117096187/100000000000000000000)
  directionHi := (159353276678529274047/25000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree164.table
  base := (2530677923747959818677704540294650058913/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-3771763192256713953340072022934404579000000000000)
      constant := (169275558277733368261001326885836131132029593509140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree164.table
  base := (202454233899836154005044680409811132841311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-15103057227500247183275130855214709316000000000000)
      constant := (678485800255100445870862307879768863523645471750079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (637413106714117096187/100000000000000000000)
  centralHi := (159353276678529274047/25000000000000000000)
  directionLo := (639365371949262964293/100000000000000000000)
  directionHi := (319682685974631482147/50000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree165.table
  base := (25738793952951184703098466701938498821671/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-3794752035443157886332995863131345596500000000000)
      constant := (171375972285790739437052458740279594499443054772238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree165.table
  base := (51477587905902235679465398859148395618007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-3798777547101861508339015765530309034000000000000)
      constant := (171726094229008086177923346066137505159907794618423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (639365371949262964293/100000000000000000000)
  centralHi := (319682685974631482147/50000000000000000000)
  directionLo := (128262338834857728319/20000000000000000000)
  directionHi := (160327923543572160399/25000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree166.table
  base := (209394728074318549737204629662202909626157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-15270963514518407277303678813313146456000000000000)
      constant := (693957505217099943948210057683635946703160375453773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree166.table
  base := (52348682018579524164328021829377249921433/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (4752260582)
      previous := (2376130291)
      next := (2376130291)
      square := (21826568183894596311913002922476665000000000000)
      linear := (-3821790787328661220859248817256940739000000000000)
      constant := (173843754114497260022595548975322711447399701127737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128262338834857728319/20000000000000000000)
  centralHi := (160327923543572160399/25000000000000000000)
  directionLo := (643252127335443229951/100000000000000000000)
  directionHi := (2512703622404075117/390625000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree167.table
  base := (106453681626003723646404059500159597478793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-7681459443632091504637687087050455263000000000000)
      constant := (351231540666374932455600329442126336095768540916777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree167.table
  base := (212907363252007063536268525373778938995661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-15379216110221843733517927475934289776000000000000)
      constant := (703897718880975965555698780019522583436759537877229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (643252127335443229951/100000000000000000000)
  centralHi := (2512703622404075117/390625000000000000)
  directionLo := (645186724567741101347/100000000000000000000)
  directionHi := (161296681141935275337/25000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree168.table
  base := (216448257156718678794982108738106066771207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-15454874260009958741247069534888674596000000000000)
      constant := (711020617490118036728892984756749669626207027333223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree168.table
  base := (4328965143134367075330309145800366744043/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-7735634535564521291799429841420408298000000000000)
      constant := (356236242092499218719009045865389655369565284350675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell133.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645186724567741101347/100000000000000000000)
  centralHi := (161296681141935275337/25000000000000000000)
  directionLo := (129423107642387750889/20000000000000000000)
  directionHi := (323557769105969377223/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree169.table
  base := (8800696391539753611343720553329349851661/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (19009042328)
      previous := (9504521164)
      next := (9504521164)
      square := (87306272735578385247652011689906660000000000000)
      linear := (-15546829632755734473218764895676438666000000000000)
      constant := (719630113689209661380777152783995133504023761530725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 11791
  qDenominator := 22366
  table := BinomialMassData.Q11791_22366.Degree169.table
  base := (110008704894246782502705512298024569535499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (9504521164)
      previous := (4752260582)
      next := (4752260582)
      square := (43653136367789192623826005844953330000000000000)
      linear := (-7781661016018120716839895944873671708000000000000)
      constant := (360549656185030828959556468652385119185054472300011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11791_22366.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell133.Kernel169
